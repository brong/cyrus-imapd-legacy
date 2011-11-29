/* cyrusdb_twoskip.c - brand new twoskip implementation, not backwards anything
 *
 * Copyright (c) 1994-2008 Carnegie Mellon University.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. The name "Carnegie Mellon University" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For permission or any legal
 *    details, please contact
 *      Carnegie Mellon University
 *      Center for Technology Transfer and Enterprise Creation
 *      4615 Forbes Avenue
 *      Suite 302
 *      Pittsburgh, PA  15213
 *      (412) 268-7393, fax: (412) 268-7395
 *      innovation@andrew.cmu.edu
 *
 * 4. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by Computing Services
 *     at Carnegie Mellon University (http://www.cmu.edu/computing/)."
 *
 * CARNEGIE MELLON UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO
 * THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS, IN NO EVENT SHALL CARNEGIE MELLON UNIVERSITY BE LIABLE
 * FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
 * AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING
 * OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <config.h>

#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <sys/types.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include "assert.h"
#include "bsearch.h"
#include "byteorder64.h"
#include "cyrusdb.h"
#include "crc32.h"
#include "libcyr_cfg.h"
#include "mappedfile.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"

/*
 * twoskip disk format.
 *
 * GOALS:
 *  a) 64 bit through
 *  b) Fast recovery after crashes
 *  c) integrity checks throughout
 *  d) simple format
 *
 * ACHIEVED BY:
 *  a)
 *   - 64 bit offsets for all values
 *   - smaller initial keylen and vallen, but they can
 *     can be extended up to 64 bits as well.
 *   - no timestamps stored in the file.
 *
 *  b)
 *   - "dirty flag" is always set in the header and
 *     fsynced BEFORE writing anything else.
 *   - a header field for "current size", after which
 *     all changes are considered suspect until commit.
 *   - two "lowest level" offsets, used in alternating
 *     order, so the highest value less than "current_size"
 *     is always the correct pointer - this means we
 *     never lose linkage, so never need to rewrite more
 *     than the affected records during a recovery.
 *   - all data is fsynced BEFORE rewriting the header to
 *     remove the dirty flag.
 *   - As long as the first 64 bytes of the file are
 *     guaranteed to write all together or not at all,
 *     we're crash-safe.
 *
 *  c)
 *   - a crc32 is stored for every byte in the file.
 *     It's checked for all header and pointer accesses,
 *     and for key and value on every value read.
 *     XXX - actually, it's not checked for value reads yet.
 *
 *  d)
 *   - there are no special commit, inorder, etc records.
 *     just add records and ghost "delete" records to give
 *     somewhere to point to on deletes.  These are only
 *     at the lowest level, so don't have a significant
 *     seek impact.
 *   - modular code makes the logic much clearer.
 */

/*
 * FORMAT:
 *
 * HEADER: 64 bytes
 *  magic: 20 bytes: "4 bytes same as skiplist" "twoskip file\0\0\0\0" 
 *  version: 4 bytes
 *  generation: 8 bytes
 *  num_records: 8 bytes
 *  repack_size: 8 bytes
 *  current_size: 8 bytes
 *  flags: 4 bytes
 *  crc32: 4 bytes
 *
 * RECORDS:
 *  type 1 byte
 *  level: 1 byte
 *  keylen: 2 bytes
 *  vallen: 4 bytes
 *  <optionally: 64 bit keylen if keylen == UINT16_MAX>
 *  <optionally: 64 bit vallen if vallen == UINT32_MAX>
 *  ptrs: 8 bytes * (level+1)
 *  head_crc32: 4 bytes
 *  tail_crc32: 4 bytes
 *  key: (keylen bytes)
 *  val: (vallen bytes)
 *  padding: enough zeros to round up to an 8 byte multiple
 *
 * Strictly, though the code doesn't currently use the same
 * path for both of them, they ARE the same thing.  8 bytes
 * of header information, "level + 1" x 8 bytes of pointers,
 * 8 bytes of crc32s and roundup("keylen + vallen", 8) bytes
 * of tail.  Just that the tail is null for a DELETE
 *
 * defined types, in skiplist language are:
 * '=' -> DUMMY
 * '+' -> ADD/INORDER
 * '-' -> DELETE (kind of)
 * but note that delete records behave differently - they're
 * part of the pointer heirarchy, so that back offsets will
 * always point somewhere past the 'end' until commit.
 *
 * The DUMMY is always MAXLEVEL level, with zero keylen and vallen
 * The DELETE is always zero level, with zero keylen and vallen
 * crc32_head is calculated on all bytes before it in the record
 * crc32_tail is calculated on all bytes after, INCLUDING padding
 */

/* OPERATION:
 *
 * Finding a record works very much like sliplist, but we have
 * a datastructure, 'struct skiploc', to help find it.  There
 * is one of these embedded directly in the 'struct db', and
 * it's the only one we ever use.
 *
 * skiploc contains two complete sets of offsets - at every
 * level the offset of the previous record, and the offset of
 * the next record, in relation to the requested key.  If the
 * key is an exact match, it also contains a copy of the
 * struct skiprecord.  If not, it contains the struct
 * skiprecord for the previous record at level zero.
 *
 * It also contains a 'struct buf' with a copy of the requested
 * key, which allows for efficient relocation of the position in
 * the file when nothing is changed.
 *
 * So nothing is really changed with finding, except the special
 * "level zero" alternative pointer.  We'll see that in action
 * later.
 *
 * TRANSACTIONS:
 * 1) before writing anything else, the header is updated with the
 *    DIRTY flag set, and then fdatasync is run.
 * 2) after all changes, fdatasync is run again.
 * 3) finally, the header is updated with a new current_size, and
 *    fdatasync is run for a third time.
 *
 * ADDING A NEW RECORD:
 * a new record is created with forward locations pointing to the
 * next pointers in the skiploc.  This is appended to the file.
 * This works for either a create OR replace, since in both cases
 * the nextlocs are correct.  Level zero is set to zero on a new
 * record.
 *
 * If it's not a replace, a "random" level will be chosen for the
 * record.  All update operations below apply only up to this level,
 * pointers above are unaffected - and continue over the location
 * of this change.
 *
 * For each backloc, the record at that offset is read, and the
 * forward pointers at each level are replaced with the offset
 * of the new record.  NOTE: see special level zero logic below.
 *
 * Again, if this was a replace, the backlocs don't point to the
 * current record, so it just silently disappears from the lists.
 *
 * DELETING A RECORD:
 * The logic is almost identical to adding, but a delete record
 * always has a level of zero, with only a single pointer forward
 * to the next record.
 *
 * Because of this, the updates are done up to the level of the
 * old record instead.
 *
 * THE SPECIAL "level zero":
 * To allow a "fast fsck" after an aborted transaction, rather
 * than having only a single level 1 pointer, we have two.  The
 * following algorithm is used to select which one to change.
 *
 * The definition of "current_size" is the size of the database
 * at last commit, it does not get updated during a transaction.
 *
 * So: when updating level 1 - if either level 1 or level 0 has
 * a value >= current_size, then that value gets updated again.
 * otherwise, the lowest value gets replaced with the new value.
 *
 * when reading, the highest value is used - except during
 * recovery when it's the highest value less than current_size,
 * since any "future" offsets are bogus.
 */


/********** TUNING *************/

/* don't bother rewriting if the database has less than this much "new" data */
#define MINREWRITE 16834
/* don't bother rewriting if more than this percentage dirty */
#define REWRITE_PERCENT 20
/* number of skiplist levels - 31 gives us binary search to 2^32 records.
 * limited to 255 by file format, but skiplist had 20, and that was enough
 * for most real uses.  31 is heaps. */
#define MAXLEVEL 31
/* should be 0.5 for binary search semantics */
#define PROB 0.5

/* format specifics */
#define VERSION 1

/* type aliases */
#define LLU long long unsigned int
#define LU long unsigned int

/********** DATA STRUCTURES *************/

/* A single "record" in the twoskip file.  This could be a
 * DUMMY, a KEYRECORD, a VALRECORD or even a DELETE - they
 * all read and write with the same functions */
struct skiprecord {
    /* location on disk (not part of the on-disk format as such) */
    size_t offset;
    size_t len;

    /* what are our header fields */
    uint8_t type;
    uint8_t level;
    size_t keylen;
    size_t vallen;

    /* where to do we go from here? */
    size_t nextloc[MAXLEVEL+1];

    /* what do our integrity checks say? */
    uint32_t crc32_head;
    uint32_t crc32_tail;

    /* our key and value */
    size_t keyoffset;
    size_t valoffset;
};

/* a location in the twoskip file.  We always have:
 * record: if "is_exactmatch" this points to the record
 *         with the matching key, otherwise it points to
 *         the 'compar' order previous record.
 * backloc: the records that point TO this location
 *          at each level.  If is_exactmatch, they
 *          point to the record, otherwise they are
 *          the record.
 * forwardloc: the records pointed to by the record
 *             at 'backloc' at the same level.  Kept
 *             here for efficiency
 * keybuf: a copy of the requested key - we always keep
 *         this so we can re-seek after the file has been
 *         checkpointed under us (say a read-only foreach)
 *
 * generation and end can be used to see if anything in
 * the file may have changed and needs re-reading.
 */
struct skiploc {
    /* requested, may not match actual record */
    struct buf keybuf;
    int is_exactmatch;

    /* current or next record */
    struct skiprecord record;

    /* we need both sets of offsets to cheaply insert */
    size_t backloc[MAXLEVEL];
    size_t forwardloc[MAXLEVEL];

    /* need a generation so we know if the location is still valid */
    uint64_t generation;
    size_t end;
};

enum {
    UNLOCKED = 0,
    READLOCKED = 1,
    WRITELOCKED = 2,
};

#define DIRTY (1<<0)

struct txn {
    /* logstart is where we start changes from on commit, where we truncate
       to on abort */
    int num;
};

struct db_header {
    /* header info */
    uint32_t version;
    uint32_t flags;
    uint64_t generation;
    uint64_t num_records;
    size_t repack_size;
    size_t current_size;
};

struct db {
    /* file data */
    struct mappedfile *mf;

    struct db_header header;
    struct skiploc loc;

    /* tracking info */
    int is_open;
    size_t end;
    int txn_num;
    struct txn *current_txn;

    /* comparator function to use for sorting */
    int open_flags;
    int (*compar) (const char *s1, int l1, const char *s2, int l2);
};

struct db_list {
    struct db *db;
    struct db_list *next;
    int refcount;
};

#define HEADER_MAGIC ("\241\002\213\015twoskip file\0\0\0\0")
#define HEADER_MAGIC_SIZE (20)

/* offsets of header files */
enum {
    OFFSET_HEADER = 0,
    OFFSET_VERSION = 20,
    OFFSET_GENERATION = 24,
    OFFSET_NUM_RECORDS = 32,
    OFFSET_REPACK_SIZE = 40,
    OFFSET_CURRENT_SIZE = 48,
    OFFSET_FLAGS = 56,
    OFFSET_CRC32 = 60,
};

/* plus 4 zero bytes */
#define HEADER_SIZE 64

static struct db_list *open_twoskip = NULL;

static int mycommit(struct db *db, struct txn *tid);
static int myabort(struct db *db, struct txn *tid);
static int mycheckpoint(struct db *db);
static int myconsistent(struct db *db, struct txn *tid);
static int recovery(struct db *db);

/************** HELPER FUNCTIONS ****************/

/* calculate padding size */
static size_t roundup(size_t record_size, int howfar)
{
    if (record_size % howfar)
	record_size += howfar - (record_size % howfar);
    return record_size;
}

/* choose a level appropriately randomly */
static uint8_t randlvl(uint8_t lvl, uint8_t maxlvl)
{
    while (((float) rand() / (float) (RAND_MAX)) < PROB) {
	lvl++;
	if (lvl == maxlvl) break;
    }
    return lvl;
}

static const char *_base(struct db *db)
{
    return mappedfile_base(db->mf);
}

static const char *_key(struct db *db, struct skiprecord *rec)
{
    return mappedfile_base(db->mf) + rec->keyoffset;
}

static const char *_val(struct db *db, struct skiprecord *rec)
{
    return mappedfile_base(db->mf) + rec->valoffset;
}

static size_t _size(struct db *db)
{
    return mappedfile_size(db->mf);
}

static const char *_fname(struct db *db)
{
    return mappedfile_fname(db->mf);
}

/* find the next record at a given level, encapsulating the
 * level 0 magic */
static size_t _getloc(struct db *db, struct skiprecord *record,
		      uint8_t level)
{
    const char *base;
    size_t offset;

    if (level)
	return record->nextloc[level + 1];

    /* if one is past, must be the other */
    if (record->nextloc[0] >= db->end)
	offset = record->nextloc[1];
    else if (record->nextloc[1] >= db->end)
	offset = record->nextloc[0];

    /* highest remaining */
    else if (record->nextloc[0] > record->nextloc[1])
	offset = record->nextloc[0];
    else
	offset = record->nextloc[1];

    base = _base(db);
    /* skip past any delete pointer */
    if (offset && base[offset] == '-')
	offset = ntohll(*((uint64_t *)(base+offset+8)));

    return offset;
}

/* set the next record at a given level, encapsulating the
 * level 0 magic */
static void _setloc(struct db *db, struct skiprecord *record,
		    uint8_t level, size_t offset)
{
    if (level) {
	record->nextloc[level+1] = offset;
	return;
    }

    /* level zero is special */
    /* already this transaction, update this one */
    if (record->nextloc[0] >= db->header.current_size)
	record->nextloc[0] = offset;
    else if (record->nextloc[1] >= db->header.current_size)
	record->nextloc[1] = offset;
    /* otherwise, update older one */
    else if (record->nextloc[1] > record->nextloc[0])
	record->nextloc[0] = offset;
    else
	record->nextloc[1] = offset;
}

/************** HEADER ****************/

/* given an open, mapped db, read in the header information */
static int read_header(struct db *db)
{
    uint32_t crc;

    assert(db && db->mf && db->is_open);

    if (_size(db) < HEADER_SIZE) {
	syslog(LOG_ERR,
	       "twoskip: file not large enough for header: %s", _fname(db));
    }

    if (memcmp(_base(db), HEADER_MAGIC, HEADER_MAGIC_SIZE)) {
	syslog(LOG_ERR, "twoskip: invalid magic header: %s", _fname(db));
	return CYRUSDB_IOERROR;
    }

    db->header.version
	= ntohl(*((uint32_t *)(_base(db) + OFFSET_VERSION)));

    if (db->header.version > VERSION) {
	syslog(LOG_ERR, "twoskip: version mismatch: %s has version %d",
	       _fname(db), db->header.version);
	return CYRUSDB_IOERROR;
    }

    db->header.generation
	= ntohll(*((uint64_t *)(_base(db) + OFFSET_GENERATION)));

    db->header.num_records
	= ntohll(*((uint64_t *)(_base(db) + OFFSET_NUM_RECORDS)));

    db->header.repack_size
	= ntohll(*((uint64_t *)(_base(db) + OFFSET_REPACK_SIZE)));

    db->header.current_size
	= ntohll(*((uint64_t *)(_base(db) + OFFSET_CURRENT_SIZE)));

    db->header.flags
	= ntohl(*((uint32_t *)(_base(db) + OFFSET_FLAGS)));

    crc = ntohl(*((uint32_t *)(_base(db) + OFFSET_CRC32)));

    if (crc32_map(_base(db), OFFSET_CRC32) != crc) {
	syslog(LOG_ERR, "DBERROR: %s: twoskip header CRC failure",
	       _fname(db));
	return CYRUSDB_IOERROR;
    }

    db->end = db->header.current_size;

    return 0;
}

/* given an open, mapped, locked db, write the header information */
static int write_header(struct db *db)
{
    char buf[HEADER_SIZE];
    size_t offset = 0;

    /* format one buffer */
    memcpy(buf + 0, HEADER_MAGIC, HEADER_MAGIC_SIZE);
    *((uint32_t *)(buf + OFFSET_VERSION)) = htonl(db->header.version);
    *((uint64_t *)(buf + OFFSET_GENERATION)) = htonll(db->header.generation);
    *((uint64_t *)(buf + OFFSET_NUM_RECORDS)) = htonll(db->header.num_records);
    *((uint64_t *)(buf + OFFSET_REPACK_SIZE)) = htonll(db->header.repack_size);
    *((uint64_t *)(buf + OFFSET_CURRENT_SIZE)) = htonll(db->header.current_size);
    *((uint32_t *)(buf + OFFSET_FLAGS)) = htonl(db->header.flags);
    *((uint32_t *)(buf + OFFSET_CRC32)) = htonl(crc32_map(buf, OFFSET_CRC32));

    /* write it out */
    return mappedfile_write(db->mf, &offset, buf, HEADER_SIZE);
}

/* simple wrapper to write with an fsync */
static int commit_header(struct db *db)
{
    int r = write_header(db);
    if (!r) r = mappedfile_commit(db->mf);
    return r;
}

/******************** RECORD *********************/

/* read a single skiprecord at the given offset */
static int read_record(struct db *db, size_t offset,
		       struct skiprecord *record)
{
    const char *base;
    int i;

    memset(record, 0, sizeof(struct skiprecord));

    record->offset = offset;
    record->len = 24; /* absolute minimum */

    /* need space for at least the header plus some details */
    if (record->offset + record->len > _size(db))
	goto badsize;

    base = _base(db) + offset;

    /* read in the record header */
    record->type = base[0];
    record->level = base[1];
    record->keylen = ntohs(*((uint16_t *)(base + 2)));
    record->vallen = ntohl(*((uint32_t *)(base + 4)));
    offset += 8;

    /* make sure we fit */
    assert(record->level <= MAXLEVEL);

    /* long key */
    if (record->keylen == UINT16_MAX) {
	base = _base(db) + offset;
	record->keylen = ntohll(*((uint64_t *)base));
	offset += 8;
    }

    /* long value */
    if (record->vallen == UINT32_MAX) {
	base = _base(db) + offset;
	record->vallen = ntohll(*((uint64_t *)base));
	offset += 8;
    }

    /* we know the length now */
    record->len = (offset - record->offset) /* header including lengths */
		+ 8 * (1 + record->level)   /* ptrs */
		+ 8                         /* crc32s */
		+ roundup(record->keylen + record->vallen, 8);  /* keyval */

    if (record->offset + record->len > _size(db))
	goto badsize;

    for (i = 0; i <= record->level; i++) {
	base = _base(db) + offset;
	record->nextloc[i] = ntohll(*((uint64_t *)base));
	offset += 8;
    }

    base = _base(db) + offset;
    record->crc32_head = ntohl(*((uint32_t *)base));
    if (crc32_map(_base(db) + record->offset, (offset - record->offset))
	!= record->crc32_head)
	return CYRUSDB_IOERROR;

    record->crc32_tail = ntohl(*((uint32_t *)(base+4)));

    record->keyoffset = offset + 8;
    record->valoffset = record->keyoffset + record->keylen;

    return 0;

badsize:
    syslog(LOG_ERR, "twoskip: attempt to read past end of file %s: %08llX > %08llX",
	   _fname(db), (LLU)record->offset + record->len, (LLU)_size(db));
    return CYRUSDB_IOERROR;
}

/* prepare the header part of the record (everything except the key, value
 * and padding).  Used for both writes and rewrites. */
#define MAXRECORDHEAD ((MAXLEVEL + 5)*8)
static char *prepare_record(struct skiprecord *record, size_t *sizep)
{
    static char writebuf[MAXRECORDHEAD];
    int len = 8;
    int i;

    writebuf[0] = record->type;
    writebuf[1] = record->level;
    if (record->keylen < UINT16_MAX) {
	*((uint16_t *)(writebuf+2)) = htons(record->keylen);
    }
    else {
	*((uint16_t *)(writebuf+2)) = htons(UINT16_MAX);
	*((uint64_t *)(writebuf+len)) = htonll(record->keylen);
	len += 8;
    }

    if (record->vallen < UINT32_MAX) {
	*((uint32_t *)(writebuf+4)) = htonl(record->vallen);
    }
    else {
	*((uint32_t *)(writebuf+4)) = htonl(UINT32_MAX);
	*((uint64_t *)(writebuf+len)) = htonll(record->vallen);
	len += 8;
    }

    /* got pointers? */
    for (i = 0; i <= record->level; i++) {
	*((uint64_t *)(writebuf+len)) = htonll(record->nextloc[i]);
	len += 8;
    }

    /* NOTE: crc32_tail does not change */
    record->crc32_head = crc32_map(writebuf, len);
    *((uint32_t *)(writebuf+len)) = htonl(record->crc32_head);
    *((uint32_t *)(writebuf+len+4)) = htonl(record->crc32_tail);
    len += 8;

    *sizep = len;

    return writebuf;
}

/* only changing the record head, so only rewrite that much */
static int rewrite_record(struct db *db, struct skiprecord *record)
{
    const char *buf;
    size_t len;
    size_t offset = record->offset;

    /* we must already be in a transaction before updating records */
    assert(db->header.flags & DIRTY);
    assert(offset);

    buf = prepare_record(record, &len);

    return mappedfile_write(db->mf, &offset, buf, len);
}

/* you can only write records at the end */
static int write_record(struct db *db, struct skiprecord *record,
			const char *key, const char *val)
{
    char zeros[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    int r;
    uint64_t len;
    size_t offset = db->end;
    struct iovec io[4];

    assert(!record->offset);

    /* we'll put the HEAD on later */

    io[1].iov_base = (char *)key;
    io[1].iov_len = record->keylen;

    io[2].iov_base = (char *)val;
    io[2].iov_len = record->vallen;

    /* pad to 8 bytes */
    len = record->vallen + record->keylen;
    io[3].iov_base = zeros;
    io[3].iov_len = roundup(len, 8) - len;

    /* calculate the CRC32 of the tail first */
    record->crc32_tail = crc32_iovec(io+1, 3);

    /* prepare the record once we know the crc32 of the tail */
    io[0].iov_base = prepare_record(record, &io[0].iov_len);

    /* write to the mapped file, getting the offset updated */
    r = mappedfile_writev(db->mf, &offset, io, 4);
    if (r) return CYRUSDB_IOERROR;

    /* locate the record */
    record->offset = db->end;
    record->keyoffset = db->end + io[0].iov_len;
    record->valoffset = record->keyoffset + record->keylen;
    record->len = (offset - db->end);

    /* and advance the known file size */
    db->end = offset;

    return 0;
}

/* helper to append a record, starting the transaction by dirtying the
 * header first if required */
static int append_record(struct db *db, struct skiprecord *record,
			 const char *key, const char *val)
{
    int r;

    assert(db->current_txn);

    /* dirty the header if not already dirty */
    if (!(db->header.flags & DIRTY)) {
	db->header.flags |= DIRTY;
	r = commit_header(db);
	if (r) return r;
    }

    return write_record(db, record, key, val);
}

/************************** LOCATION MANAGEMENT ***************************/

/* finds a record, either an exact match or the record
 * immediately before */
static int relocate(struct db *db)
{
    struct skiploc *loc = &db->loc;
    struct skiprecord newrecord;
    size_t offset;
    uint8_t level;
    uint8_t i;
    int cmp = -1; /* never found a thing! */
    int r;

    /* pointer validity */
    loc->generation = db->header.generation;
    loc->end = db->end;

    /* start with the dummy */
    r = read_record(db, HEADER_SIZE, &loc->record);
    loc->is_exactmatch = 0;

    /* special case start pointer for efficiency */
    if (!loc->keybuf.len) {
	for (i = 0; i < loc->record.level; i++) {
	    loc->backloc[i] = loc->record.offset;
	    loc->forwardloc[i] = _getloc(db, &loc->record, i);
	}
	return 0;
    }

    level = loc->record.level;
    newrecord.offset = 0;
    while (level) {
	offset = _getloc(db, &loc->record, level-1);

	loc->backloc[level-1] = loc->record.offset;
	loc->forwardloc[level-1] = offset;

	if (offset && newrecord.offset != offset) {
	    r = read_record(db, offset, &newrecord);
	    if (r) return r;
	    cmp = db->compar(_key(db, &newrecord), newrecord.keylen,
			     loc->keybuf.s, loc->keybuf.len);

	    /* not there?  stay at this level */
	    if (cmp < 0) {
		/* move the offset range along */
		loc->record = newrecord;
		continue;
	    }
	}

	level--;
    }

    if (cmp == 0) { /* we found it exactly */
	loc->is_exactmatch = 1;
	loc->record = newrecord;
	for (i = 0; i < loc->record.level; i++)
	    loc->forwardloc[i] = _getloc(db, &loc->record, i);
    }

    return 0;
}

/* helper function to find a location, either by using the existing
 * location if it's close enough, or using the full relocate above */
static int find_loc(struct db *db, const char *key, size_t keylen)
{
    struct skiprecord newrecord;
    struct skiploc *loc = &db->loc;
    int cmp, i, r;

    buf_setmap(&loc->keybuf, key, keylen);

    /* can we special case advance? */
    if (keylen && loc->end == db->end
               && loc->generation == db->header.generation) {
	cmp = db->compar(_key(db, &loc->record), loc->record.keylen,
			 loc->keybuf.s, loc->keybuf.len);
	/* same place, and was exact.  Otherwise we're going back,
	 * and the reverse pointers are no longer valid... */
	if (db->loc.is_exactmatch && cmp == 0) {
	    return 0;
	}

	/* we're looking after this record */
	if (cmp < 0) {
	    for (i = 0; i < db->loc.record.level; i++)
		loc->backloc[i] = db->loc.record.offset;

	    /* nothing afterwards? */
	    if (!loc->forwardloc[0]) {
		db->loc.is_exactmatch = 0;
		return 0;
	    }

	    /* read the next record */
	    r = read_record(db, loc->forwardloc[0], &newrecord);
	    if (r) return r;

	    /* now where is THIS record? */
	    cmp = db->compar(_key(db, &newrecord), newrecord.keylen,
			     loc->keybuf.s, loc->keybuf.len);

	    /* exact match? */
	    if (cmp == 0) {
		db->loc.is_exactmatch = 1;
		db->loc.record = newrecord;
		for (i = 0; i < newrecord.level; i++)
		    loc->forwardloc[i] = _getloc(db, &newrecord, i);
		return 0;
	    }

	    /* or in the gap */
	    if (cmp > 0) {
		db->loc.is_exactmatch = 0;
		return 0;
	    }
	}
	/* if we fell out here, it's not a "local" record, just search */
    }

    return relocate(db);
}

/* helper function to advance to the "next" record.  Used by foreach,
 * fetchnext, and internal functions */
static int advance_loc(struct db *db)
{
    struct skiploc *loc = &db->loc;
    uint8_t i;
    int r;

    /* has another session made changes?  Need to re-find the location */
    if (loc->end != db->end || loc->generation != db->header.generation) {
	r = relocate(db);
	if (r) return r;
    }

    /* reached the end? */
    if (!loc->forwardloc[0]) {
	buf_reset(&loc->keybuf);
	return relocate(db);
    }

    /* update back pointers */
    for (i = 0; i < loc->record.level; i++)
	loc->backloc[i] = loc->record.offset;

    /* ADVANCE */
    r = read_record(db, loc->forwardloc[0], &loc->record);
    if (r) return r;

    /* update forward pointers */
    for (i = 0; i < loc->record.level; i++)
	loc->forwardloc[i] = _getloc(db, &loc->record, i);

    /* keep our location */
    buf_setmap(&loc->keybuf, _key(db, &loc->record), loc->record.keylen);
    loc->is_exactmatch = 1;

    return 0;
}

/* helper function to update all the back records efficiently
 * after appending a new record, either create or delete.  The
 * caller must set forwardloc[] correctly for each level it has
 * changed */
static int stitch(struct db *db, uint8_t maxlevel)
{
    struct skiploc *loc = &db->loc;
    struct skiprecord oldrecord;
    uint8_t i;
    int r;

    oldrecord.level = 0;
    while (oldrecord.level < maxlevel) {
	uint8_t level = oldrecord.level;

	r = read_record(db, loc->backloc[level], &oldrecord);
	if (r) return r;

	for (i = level; i < maxlevel; i++)
	    _setloc(db, &oldrecord, i, loc->forwardloc[i]);

	r = rewrite_record(db, &oldrecord);
	if (r) return r;
    }

    return 0;
}

/* overall "store" function - pass NULL val for delete.  This is
 * the place that all changes funnel through */
static int store_record(struct db *db, const char *val, size_t vallen)
{
    struct skiploc *loc = &db->loc;
    struct skiprecord newrecord;
    uint8_t level = 0;
    int r;
    int i;

    if (loc->is_exactmatch) {
	level = loc->record.level;
	db->header.num_records--;
	db->header.repack_size -= loc->record.len;
    }

    /* build a new record */
    memset(&newrecord, 0, sizeof(struct skiprecord));
    if (val) {
	newrecord.type = '+';
	newrecord.level = randlvl(1, MAXLEVEL);
	newrecord.keylen = loc->keybuf.len;
	newrecord.vallen = vallen;
	for (i = 0; i < newrecord.level; i++)
	    newrecord.nextloc[i+1] = loc->forwardloc[i];
	if (newrecord.level > level)
	    level = newrecord.level;
    }
    else {
	if (!loc->is_exactmatch)
	    return CYRUSDB_NOTFOUND;
	/* remove this record */
	newrecord.type = '-';
	newrecord.nextloc[0] = loc->forwardloc[0];
    }

    /* append to the file */
    r = append_record(db, &newrecord, loc->keybuf.s, val);
    if (r) return r;

    /* get the nextlevel to point here - needs to be at least one! */
    loc->forwardloc[0] = newrecord.offset;
    for (i = 1; i < newrecord.level; i++)
	loc->forwardloc[i] = newrecord.offset;

    /* update all backpointers */
    r = stitch(db, level);

    /* finally, re-read the record so we're working with keyoffset
     * and valoffset fields which are accurate.  Could also fix
     * append_record to handle this. */
    r = read_record(db, newrecord.offset, &loc->record);
    if (r) return r;

    /* and update the forwardloc back to their correct values */
    for (i = 0; i < loc->record.level; i++)
	loc->forwardloc[i] = _getloc(db, &loc->record, i);

    if (val) {
	loc->is_exactmatch = 1;
	db->header.num_records++;
	db->header.repack_size += loc->record.len;
    }
    else {
	loc->is_exactmatch = 0;
    }

    loc->end = db->end;

    return 0;
}

/************ DATABASE STRUCT AND TRANSACTION MANAGEMENT **************/

static int write_lock(struct db *db)
{
    int r = mappedfile_writelock(db->mf);
    if (r) return r;

    /* reread header */
    if (db->is_open)
	return read_header(db);

    return 0;
}

static int read_lock(struct db *db)
{
    int r = mappedfile_readlock(db->mf);
    if (r) return r;

    /* reread header */
    if (db->is_open)
	return read_header(db);

    return 0;
}

static int newtxn(struct db *db, struct txn **tidptr)
{
    int r;

    assert(!db->current_txn);
    assert(!*tidptr);

    /* grab a r/w lock */
    r = write_lock(db);
    if (r) return r;

    /* didn't close cleanly before? */
    if (db->header.flags & DIRTY) {
	/* yikes, need recovery */
	r = recovery(db);
	if (r) return r;
    }

    /* create the transaction */
    db->txn_num++;
    db->current_txn = xmalloc(sizeof(struct txn));
    db->current_txn->num = db->txn_num;

    /* pass it back out */
    *tidptr = db->current_txn;

    return 0;
}

static int unlock(struct db *db)
{
    return mappedfile_unlock(db->mf);
}

static void dispose_db(struct db *db)
{
    if (!db) return;

    if (db->mf) {
	if (mappedfile_islocked(db->mf)) {
	    syslog(LOG_ERR, "twoskip: %s closed while still locked", _fname(db));
	    unlock(db);
	}
	mappedfile_close(&db->mf);
    }

    buf_free(&db->loc.keybuf);

    free(db);
}

/************************************************************/

static int myinit(const char *dbdir __attribute__((unused)),
		  int myflags __attribute__((unused)))
{
    return 0;
}

static int mydone(void)
{
    return 0;
}

static int mysync(void)
{
    return 0;
}

static int myarchive(const char **fnames, const char *dirname)
{
    int r;
    const char **fname;
    char dstname[1024], *dp;
    int length, rest;

    strlcpy(dstname, dirname, sizeof(dstname));
    length = strlen(dstname);
    dp = dstname + length;
    rest = sizeof(dstname) - length;

    /* archive those files specified by the app */
    for (fname = fnames; *fname != NULL; ++fname) {
	syslog(LOG_DEBUG, "archiving database file: %s", *fname);
	strlcpy(dp, strrchr(*fname, '/'), rest);
	r = cyrusdb_copyfile(*fname, dstname);
	if (r) {
	    syslog(LOG_ERR,
		   "DBERROR: error archiving database file: %s", *fname);
	    return CYRUSDB_IOERROR;
	}
    }

    return 0;
}

static int opendb(const char *fname, int flags, struct db **ret)
{
    struct db *db;
    int r;

    assert(fname);
    assert(ret);

    db = (struct db *) xzmalloc(sizeof(struct db));

    db->open_flags = flags & ~CYRUSDB_CREATE;
    db->compar = (flags & CYRUSDB_MBOXSORT) ? bsearch_ncompare_mbox
					    : bsearch_ncompare_raw;

    r = mappedfile_open(&db->mf, fname, flags & CYRUSDB_CREATE);
    if (r) goto done;

    db->is_open = 0;

    /* grab a read lock, only reading the header */
    r = read_lock(db);
    if (r) goto done;

    /* if the file is empty, then the header needs to be created first */
    if (mappedfile_size(db->mf) == 0) {
	unlock(db);
	r = write_lock(db);
	if (r) goto done;
    }

    /* race condition.  Another process may have already got the write
     * lock and created the header. Only go ahead if the map_size is
     * still zero (read/write_lock updates map_size). */
    if (mappedfile_size(db->mf) == 0) {
	struct skiprecord dummy;

	/* create the dummy! */
	memset(&dummy, 0, sizeof(struct skiprecord));
	dummy.type = '=';
	dummy.level = MAXLEVEL;

	/* append dummy after header location */
	db->end = HEADER_SIZE;
	r = write_record(db, &dummy, NULL, NULL);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: writing dummy node for %s: %m",
		   fname);
	    goto done;
	}

	/* create the header */
	db->header.version = VERSION;
	db->header.generation = 1;
	db->header.repack_size = db->end;
	db->header.current_size = db->end;
	r = commit_header(db);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: writing header for %s: %m",
		   fname);
	    goto done;
	}
    }

    db->is_open = 1;

    r = read_header(db);
    if (r) goto done;

    /* unlock the DB */
    unlock(db);

    if (db->header.flags & DIRTY) {
	/* need to run recovery */
	r = write_lock(db);
	if (r) goto done;
	if (db->header.flags & DIRTY) {
	    r = recovery(db);
	    if (r) goto done;
	}
	unlock(db);
    }

    *ret = db;

done:
    if (r) dispose_db(db);
    return r;
}

static int myopen(const char *fname, int flags, struct db **ret)
{
    struct db_list *ent;
    struct db *mydb;
    int r;

    /* do we already have this DB open? */
    for (ent = open_twoskip; ent; ent = ent->next) {
	if (strcmp(_fname(ent->db), fname)) continue;
	ent->refcount++;
	*ret = ent->db;
	return 0;
    }

    r = opendb(fname, flags, &mydb);
    if (r) return r;

    /* track this database in the open list */
    ent = (struct db_list *) xzmalloc(sizeof(struct db_list));
    ent->db = mydb;
    ent->refcount = 1;
    ent->next = open_twoskip;
    open_twoskip = ent;

    /* return the open DB */
    *ret = mydb;

    return 0;
}

static int myclose(struct db *db)
{
    struct db_list *ent = open_twoskip;
    struct db_list *prev = NULL;

    assert(db);

    /* remove this DB from the open list */
    while (ent && ent->db != db) {
	prev = ent;
	ent = ent->next;
    }
    assert(ent);

    if (--ent->refcount <= 0) {
	if (prev) prev->next = ent->next;
	else open_twoskip = ent->next;
	free(ent);
	dispose_db(db);
    }

    return 0;
}

/*************** EXTERNAL APIS ***********************/

static int myfetch(struct db *db,
	    const char *key, size_t keylen,
	    const char **foundkey, size_t *foundkeylen,
	    const char **data, size_t *datalen,
	    struct txn **tidptr, int fetchnext)
{
    int r = 0;

    assert(db);
    if (datalen) assert(data);

    if (data) *data = NULL;
    if (datalen) *datalen = 0;

    /* Hacky workaround:
     *
     * If no transaction was passed, but we're in a transaction,
     * then just do the read within that transaction.
     */
    if (!tidptr && db->current_txn)
	tidptr = &db->current_txn;

    if (tidptr) {
	if (!*tidptr) {
	    r = newtxn(db, tidptr);
	    if (r) return r;
	}
    } else {
	/* grab a r lock */
	r = read_lock(db);
	return r;
    }

    r = find_loc(db, key, keylen);
    if (r) goto done;

    if (fetchnext) {
	r = advance_loc(db);
	if (r) goto done;
    }

    if (foundkey) *foundkey = db->loc.keybuf.s;
    if (foundkeylen) *foundkeylen = db->loc.keybuf.len;

    if (!r && db->loc.is_exactmatch) {
	if (data) *data = _val(db, &db->loc.record);
	if (datalen) *datalen = db->loc.record.vallen;
    }
    else {
	/* we didn't get an exact match */
	r = CYRUSDB_NOTFOUND;
    }

    if (!tidptr) {
	/* release read lock */
	int r1;
	if ((r1 = unlock(db)) < 0) {
	    return r1;
	}
    }

done:
    return r;
}

/* foreach allows for subsidary mailbox operations in 'cb'.
   if there is a txn, 'cb' must make use of it.
*/
static int myforeach(struct db *db,
	      const char *prefix, size_t prefixlen,
	      foreach_p *goodp,
	      foreach_cb *cb, void *rock,
	      struct txn **tidptr)
{
    int r = 0, cb_r = 0;
    int need_unlock = 0;
    const char *val;
    size_t vallen;

    assert(db);
    assert(cb);
    if (prefixlen) assert(prefix);

    /* Hacky workaround:
     *
     * If no transaction was passed, but we're in a transaction,
     * then just do the read within that transaction.
     */
    if (!tidptr && db->current_txn)
	tidptr = &db->current_txn;
    if (tidptr) {
	if (!*tidptr) {
	    r = newtxn(db, tidptr);
	    if (r) return r;
	}
    } else {
	/* grab a r lock */
	r = read_lock(db);
	return r;
	need_unlock = 1;
    }

    r = find_loc(db, prefix, prefixlen);
    if (r) goto done;

    if (!db->loc.is_exactmatch) {
	/* advance to the first match */
	r = advance_loc(db);
	if (r) goto done;
    }

    while (db->loc.is_exactmatch) {
	/* does it match prefix? */
	if (prefixlen) {
	    if (db->loc.record.keylen < prefixlen) break;
	    if (db->compar(_key(db, &db->loc.record), prefixlen, prefix, prefixlen)) break;
	}

	val = _val(db, &db->loc.record);
	vallen = db->loc.record.vallen;

	if (!goodp || goodp(rock, db->loc.keybuf.s, db->loc.keybuf.len,
				  val, vallen)) {
	    if (!tidptr) {
		/* release read lock */
		r = unlock(db);
		if (r) goto done;
		need_unlock = 0;
	    }

	    /* make callback */
	    cb_r = cb(rock, db->loc.keybuf.s, db->loc.keybuf.len,
			    val, vallen);
	    if (cb_r) break;

	    if (!tidptr) {
		/* grab a r lock */
		r = read_lock(db);
		if (r) goto done;
		need_unlock = 1;
	    }
	}

	/* move to the next one */
	r = advance_loc(db);
	if (r) goto done;
    }

 done:

    if (need_unlock) {
	/* release read lock */
	int r1 = unlock(db);
	if (r1) return r1;
    }

    return r ? r : cb_r;
}

/* helper function for all writes - wraps create and delete and the FORCE
 * logic for each */
static int skipwrite(struct db *db,
		     const char *key, size_t keylen,
		     const char *data, size_t datalen,
		     int force)
{
    int r = find_loc(db, key, keylen);
    if (r) return r;

    /* could be a delete or a replace */
    if (db->loc.is_exactmatch) {
	if (!data) return store_record(db, NULL, 0);
	if (!force) return CYRUSDB_EXISTS;
	/* unchanged?  Save the IO */
	if (!db->compar(data, datalen,
			_val(db, &db->loc.record),
			db->loc.record.vallen))
	    return 0;
	return store_record(db, data, datalen);
    }

    /* only create if it's not a delete, obviously */
    if (data) return store_record(db, data, datalen);

    /* must be a delete - are we forcing? */
    if (!force) return CYRUSDB_NOTFOUND;

    return 0;
}

static int mycommit(struct db *db, struct txn *tid)
{
    int r = 0;

    assert(db);
    assert(tid == db->current_txn);

    /* no need to abort if we're not dirty */
    if (!(db->header.flags & DIRTY))
	goto done;

    r = mappedfile_commit(db->mf);
    if (r) goto done;

    db->header.current_size = db->end;
    db->header.flags &= ~DIRTY;
    r = commit_header(db);

 done:
    if (r) {
	int r2;

	/* error during commit; we must abort */
	r2 = myabort(db, tid);
	if (r2) {
	    syslog(LOG_ERR, "DBERROR: twoskip %s: commit AND abort failed",
		   _fname(db));
	}
    } else {
	/* consider checkpointing */
	size_t diff = db->header.current_size - db->header.repack_size;
	if (diff > MINREWRITE &&
	   (diff * 100 / db->header.current_size) > REWRITE_PERCENT)
	    r = mycheckpoint(db);
	else
	    unlock(db);

	free(tid);
	db->current_txn = NULL;
    }

    return r;
}

static int myabort(struct db *db, struct txn *tid)
{
    int r;

    assert(db);
    assert(tid == db->current_txn);

    /* free the tid */
    free(tid);
    db->current_txn = NULL;

    /* no need to abort if we're not dirty */
    if (db->header.flags & DIRTY) {
	db->end = db->header.current_size;
	r = recovery(db);
    }

    unlock(db);

    return r;
}

static int mystore(struct db *db,
	    const char *key, size_t keylen,
	    const char *data, size_t datalen,
	    struct txn **tidptr, int force)
{
    struct txn *localtid = NULL;
    int r = 0;
    int r2 = 0;

    assert(db);
    assert(key && keylen);

    /* not keeping the transaction, just create one local to
     * this function */
    if (!tidptr) tidptr = &localtid;

    /* make sure we're write locked and up to date */
    if (!*tidptr) {
	r = newtxn(db, tidptr);
	if (r) return r;
    }

    r = skipwrite(db, key, keylen, data, datalen, force);

    if (r) {
	r2 = myabort(db, *tidptr);
    }
    else if (localtid) {
	/* commit the store, which releases the write lock */
	r = mycommit(db, localtid);
    }

    return r2 ? r2 : r;
}

/* compress 'db', closing at the end.  Uses foreach to copy into a new
 * database, then rewrites over the old one */

struct copy_rock {
    struct db *db;
    struct txn *tid;
};

static int copy_cb(void *rock,
		   const char *key, size_t keylen,
		   const char *val, size_t vallen)
{
    struct copy_rock *cr = (struct copy_rock *)rock;

    return mystore(cr->db, key, keylen, val, vallen, &cr->tid, 0);
}

static int mycheckpoint(struct db *db)
{
    char newfname[1024];
    time_t start = time(NULL);
    struct copy_rock cr;
    int r = 0;

    /* must be in a transaction still */
    assert(db->current_txn);

    r = myconsistent(db, db->current_txn);
    if (r) {
	syslog(LOG_ERR, "db %s, inconsistent pre-checkpoint, bailing out",
	       _fname(db));
	unlock(db);
	return r;
    }

    /* open fname.NEW */
    snprintf(newfname, sizeof(newfname), "%s.NEW", _fname(db));
    unlink(newfname);

    cr.db = NULL;
    cr.tid = NULL;
    r = opendb(newfname, db->open_flags | CYRUSDB_CREATE, &cr.db);
    if (r) return r;

    r = myforeach(db, NULL, 0, NULL, copy_cb, &cr, &db->current_txn);
    if (r) goto err;

    r = myconsistent(cr.db, cr.tid);
    if (r) {
	syslog(LOG_ERR, "db %s, inconsistent post-checkpoint, bailing out",
	       _fname(db));
	goto err;
    }

    cr.db->header.current_size = cr.db->end;
    cr.db->header.repack_size = cr.db->end;

    r = mycommit(cr.db, cr.tid);
    if (r) goto err;

    /* move new file to original file name */
    r = mappedfile_rename(cr.db->mf, _fname(db));
    if (r) goto err;

    /* OK, we're commmitted now - clean up */
    unlock(db);

    /* gotta clean it all up */
    mappedfile_close(&db->mf);
    buf_free(&db->loc.keybuf);

    *db = *cr.db;
    free(cr.db); /* leaked? */

    {
	int diff = time(NULL) - start;
	syslog(LOG_INFO,
	       "twoskip: checkpointed %s (%llu record%s, %llu bytes) in %d second%s",
	       _fname(db), (LLU)db->header.num_records,
	       db->header.num_records == 1 ? "" : "s",
	       (LLU)(db->header.current_size), diff, diff == 1 ? "" : "s");
    }

    return 0;

 err:
    myabort(cr.db, cr.tid);
    unlink(_fname(cr.db));
    myclose(cr.db);
    unlock(db);
    return CYRUSDB_IOERROR;
}


/* dump the database.
   if detail == 1, dump all records.
   if detail == 2, also dump pointers for active records.
   if detail == 3, dump all records/all pointers.
*/
static int dump(struct db *db, int detail __attribute__((unused)))
{
    struct skiprecord record;
    size_t offset = HEADER_SIZE;
    int r = 0;
    int i;

    printf("HEADER: v=%lu fl=%lu num=%llu sz=(%08llX/%08llX)\n",
	  (LU)db->header.version,
	  (LU)db->header.flags,
	  (LLU)db->header.num_records,
	  (LLU)db->header.current_size,
	  (LLU)db->header.repack_size);

    while (offset < db->header.current_size) {
	printf("%08llX ", (LLU)offset);

	r = read_record(db, offset, &record);
	if (r) return r;

	if (r) {
	    printf("ERROR\n");
	    break;
	}

	switch (record.type) {
	case '-':
	    printf("DELETE ptr=%llX\n", (LLU)record.nextloc[0]);
	    break;

	case '+':
	case '=':
	    printf("%s kl=%llu dl=%llu lvl=%d (%.*s)\n",
		   (record.type == '+' ? "KEY" : "DUMMY"),
		   (LLU)record.keylen, (LLU)record.vallen,
		   record.level, (int)record.keylen, _key(db, &record));
	    printf("\t");
	    for (i = 0; i <= record.level; i++) {
		printf("%08llX ", (LLU)record.nextloc[i]);
		if (!(i % 8))
		    printf("\n\t");
	    }
	    printf("\n");
	}
    }

    return r;
}

static int consistent(struct db *db)
{
    int r;

    r = read_lock(db);
    if (r) return r;

    r = myconsistent(db, NULL);

    unlock(db);

    return r;
}

/* perform some basic consistency checks */
static int myconsistent(struct db *db, struct txn *tid)
{
    struct skiprecord oldrecord;
    struct skiprecord record;
    size_t fwd[MAXLEVEL];
    int r = 0;
    int cmp;
    int i;

    assert(db->current_txn == tid); /* could both be null */

    /* read in the dummy */
    r = read_record(db, HEADER_SIZE, &oldrecord);
    if (r) return r;

    /* set up the location pointers */
    for (i = 0; i < MAXLEVEL; i++)
	fwd[i] = _getloc(db, &oldrecord, i);

    while (fwd[0]) {
	r = read_record(db, fwd[0], &record);
	if (r) return r;

	cmp = db->compar(_key(db, &record), record.keylen,
			 _key(db, &oldrecord), oldrecord.keylen);
	if (cmp <= 0) {
	    syslog(LOG_ERR, "DBERROR: twoskip out of order %s: %.*s (%08llX) <= %.*s (%08llX)",
		   _fname(db), (int)record.keylen, _key(db, &record),
		   (LLU)record.offset,
		   (int)oldrecord.keylen, _key(db, &oldrecord),
		   (LLU)oldrecord.offset);
	    return CYRUSDB_INTERNAL;
	}

	for (i = 0; i < record.level; i++) {
	    /* check the old pointer was to here */
	    if (fwd[i] != record.offset) {
		syslog(LOG_ERR, "DBERROR: twoskip broken linkage %s: %08llX at %d, expected %08llX",
		       _fname(db), (LLU)record.offset, i, (LLU)fwd[i]);
		return CYRUSDB_INTERNAL;
	    }
	    /* and advance to the new pointer */
	    fwd[i] = _getloc(db, &record, i);
	}

	/* keep a copy for comparison purposes */
	oldrecord = record;
    }

    for (i = 0; i < MAXLEVEL; i++) {
	if (fwd[i]) {
	    syslog(LOG_ERR, "DBERROR: twoskip broken tail %s: %08llX at %d",
		   _fname(db), (LLU)fwd[i], i);
	    return CYRUSDB_INTERNAL;
	}
    }

    /* we walked the whole file and saw every pointer */

    return 0;
}

/* run recovery on this file.
 * always called with a write lock. */
static int recovery(struct db *db)
{
    int needfix[MAXLEVEL+1];
    struct skiprecord record;
    struct skiprecord fixrecord;
    time_t start = time(NULL);
    size_t nextoffset = 0;
    int r = 0;
    int i;

    assert(mappedfile_iswritelocked(db->mf));

    /* no need to run recovery if we're not dirty */
    if (!(db->header.flags & DIRTY))
	return 0;

    /* start with the dummy */
    nextoffset = HEADER_SIZE;

    /* and nothing needs updating */
    for (i = 0; i <= MAXLEVEL; i++)
	needfix[i] = 0;

    db->header.num_records = 0;

    while (nextoffset) {
	r = read_record(db, nextoffset, &record);
	if (r) return r;

	/* check for old offsets needing fixing */
	for (i = 0; i <= record.level; i++) {
	    if (needfix[i]) {
		/* need to fix up the previous record to point here */
		r = read_record(db, needfix[i], &fixrecord);
		if (r) return r;

		/* XXX - optimise adjacent same records */
		fixrecord.nextloc[i] = record.offset;
		r = rewrite_record(db, &fixrecord);
		if (r) return r;

		needfix[i] = 0;
	    }
	}

	/* mark up any broken pointers on this one for fixing */
	for (i = 0; i <= record.level; i++) {
	    if (record.nextloc[i] >= db->end)
		needfix[i] = record.offset;
	}

	/* find the next record */
	nextoffset = _getloc(db, &record, 0);

	db->header.num_records++;
    }

    /* check for remaining offsets needing fixing */
    for (i = 0; i <= MAXLEVEL; i++) {
	if (needfix[i]) {
	    /* need to fix up the previous record to point to the end */
	    r = read_record(db, needfix[i], &fixrecord);
	    if (r) return r;

	    /* XXX - optimise, same as above */
	    fixrecord.nextloc[i] = 0;
	    r = rewrite_record(db, &fixrecord);
	    if (r) return r;
	}
    }

    r = mappedfile_truncate(db->mf, db->header.current_size);
    if (r) return r;

    r = mappedfile_commit(db->mf);
    if (r) return r;

    /* clear the dirty flag */
    db->header.flags &= ~DIRTY;
    r = commit_header(db);
    if (r) return r;

    {
	int diff = time(NULL) - start;
	syslog(LOG_INFO,
	       "twoskip: recovered %s (%llu record%s, %llu bytes) in %d second%s",
	       _fname(db), (LLU)db->header.num_records,
	       db->header.num_records == 1 ? "" : "s",
	       (LLU)(db->header.current_size+8), diff, diff == 1 ? "" : "s");
    }

    return 0;
}

static int fetch(struct db *mydb,
		 const char *key, size_t keylen,
		 const char **data, size_t *datalen,
		 struct txn **tidptr)
{
    assert(key);
    assert(keylen);
    return myfetch(mydb, key, keylen, NULL, NULL,
		   data, datalen, tidptr, 0);
}

static int fetchnext(struct db *mydb,
		 const char *key, size_t keylen,
		 const char **foundkey, size_t *fklen,
		 const char **data, size_t *datalen,
		 struct txn **tidptr)
{
    return myfetch(mydb, key, keylen, foundkey, fklen,
		   data, datalen, tidptr, 1);
}

static int create(struct db *db,
		  const char *key, size_t keylen,
		  const char *data, size_t datalen,
		  struct txn **tid)
{
    if (datalen) assert(data);
    return mystore(db, key, keylen, data ? data : "", datalen, tid, 0);
}

static int store(struct db *db,
		 const char *key, size_t keylen,
		 const char *data, size_t datalen,
		 struct txn **tid)
{
    if (datalen) assert(data);
    return mystore(db, key, keylen, data ? data : "", datalen, tid, 1);
}

static int delete(struct db *db,
		 const char *key, size_t keylen,
		 struct txn **tid, int force)
{
    return mystore(db, key, keylen, NULL, 0, tid, force);
}

struct cyrusdb_backend cyrusdb_twoskip =
{
    "twoskip",			/* name */

    &myinit,
    &mydone,
    &mysync,
    &myarchive,

    &myopen,
    &myclose,

    &fetch,
    &fetch,
    &fetchnext,

    &myforeach,
    &create,
    &store,
    &delete,

    &mycommit,
    &myabort,

    &dump,
    &consistent
};
