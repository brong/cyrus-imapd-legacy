/* cyrusdb_skiplist2.c -- cyrusdb skiplist implementation - version 2
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
 *
 * $Id: cyrusdb_skiplist.c,v 1.71 2010/01/06 17:01:45 murch Exp $
 */

#include <config.h>

#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <netinet/in.h>

#include "assert.h"
#include "bsearch.h"
#include "byteorder64.h"
#include "cyrusdb.h"
#include "crc32.h"
#include "cyr_lock.h"
#include "libcyr_cfg.h"
#include "map.h"
#include "retry.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

#define PROB (0.5)

/*
 * V2 disk format; all numbers in network byte order
 *
 * there's the data file, consisting of the
 * multiple records of "key", "data", and "skip pointers", where skip
 * pointers are the record number of the data pointer.
 *
 * on startup, recovery is performed.  the last known good data file
 * is taken and the intent log is replayed on it.  the index file is
 * regenerated from scratch.
 *
 * during operation ckecpoints will compress the data.  the data file
 * is locked.  then a checkpoint rewrites the data file in order,
 * removing any unused records.  this is written and fsync'd to
 * dfile.NEW and stored for use during recovery.
 */

/*
 *  header "skiplist file\0\0\0"
 *  version (4 bytes)
 *  minor_version (4 bytes)
 *  maxlevel (4 bytes)
 *  curlevel (4 bytes)
 *  num_records (4 bytes)
 *   not really kept up-to-date accurately
 *  log start (8 bytes)
 *   offset where log records start, used mainly to tell when to compress
 *  last recovery (8 bytes)
 *   seconds since unix epoch
 *
 *   DUMMY (first node is of this type)
 *   INORDER
 *   ADD
 *   DELETE
 *   COMMIT (commit the previous records)
 *
 *  Record format a single 64 bit structure consisting of
 *   8 bits: type
 *   8 bits: level
 *  16 bits: keylen
 *  32 bits: vallen
 *
 * ====================================================================
 *
 * v1 format
 *
 * header "skiplist file\0\0\0"
 * version (4 bytes)
 * version_minor (4 bytes)
 * maxlevel (4 bytes)
 * curlevel (4 bytes)
 * listsize (4 bytes)
 *   in active items
 * log start (4 bytes)
 *   offset where log records start, used mainly to tell when to compress
 * last recovery (4 bytes)
 *   seconds since unix epoch
 *
 * 1 or more skipnodes, one of:
 *
 *   record type (4 bytes) [DUMMY, INORDER, ADD]
 *   key size (4 bytes)
 *   key string (bit string, rounded to up to 4 byte multiples w/ 0s)
 *   data size (4 bytes)
 *   data string (bit string, rounded to up to 4 byte multiples w/ 0s)
 *   skip pointers (4 bytes each)
 *     least to most
 *   padding (4 bytes, must be -1)
 *
 *   record type (4 bytes) [DELETE]
 *   record ptr (4 bytes; record to be deleted)
 *
 *   record type (4 bytes) [COMMIT]
 *
 *
 * record type is either
 *   DUMMY (first node is of this type)
 *   INORDER
 *   ADD
 *   DELETE
 *   COMMIT (commit the previous records)
 *
 */

/* V2 TYPES */

#define HAS_LEVEL    (1<<1)
#define HAS_VALUE    (1<<2)
#define HAS_DELETE   (1<<3)
#define HAS_COMPRESS (1<<4)

/* commit is special */
#define COMMIT    (1<<0)
/* everything else is a bitmap of options */
#define DUMMY     ( HAS_LEVEL )
#define ADD       ( HAS_LEVEL | HAS_VALUE )
#define REPLACE   ( HAS_LEVEL | HAS_VALUE | HAS_DELETE )
#define DELETE    (                         HAS_DELETE )
#define ZADD      ( HAS_LEVEL | HAS_VALUE |              HAS_COMPRESS )
#define ZREPLACE  ( HAS_LEVEL | HAS_VALUE | HAS_DELETE | HAS_COMPRESS )

/* V1 TYPES */

enum {
    INORDERv1 = 1,
    ADDv1 = 2,
    DELETEv1 = 4,
    COMMITv1 = 255,
    DUMMYv1 = 257
};

#define VERSION 2
#define VERSION_MINOR 1
/* don't rewrite logs shorter than this */
#define MINREWRITE 16834

/* we go up to 24 now - big files! */
#define MAXLEVELv2 24
#define MAXLEVELv1 20

/* total record head =
 * (HEADER + VALEXT + KEYEXT + DELPTR + MAXLEVEL + CRCS) * 8 bytes/64 bits
 */
#define MAXRECORDHEAD ((5+MAXLEVELv2)*8)

#define LLU long long unsigned int

struct skiprecord {
    /* where am I? (not part of the on-disk format) */
    uint64_t offset;
    uint64_t len;

    /* what are my fields */
    uint8_t type;
    uint8_t level;
    uint64_t keylen;
    uint64_t vallen;

    /* where to do we go from here? */
    uint64_t deloffset;
    uint64_t offsets[MAXLEVELv2+1];

    /* what do our integrity checks say? */
    uint32_t crc32_head;
    uint32_t crc32_tail;

    /* our key and value */
    const char *key;
    const char *val;
};

/* a location in the skiplist file.  We always have:
 * offsets: pointers to the record immediately AFTER
 *          this location at each level.
 * backoffsets: the records that point TO this location
 *              at each level.
 * record: if "is_exactmatch" this points to the record
 * at this location.  If not, it is undefined (currently
 * usually the next record at level 0)
 */
struct skiploc {
    const char *key;
    uint64_t keylen;
    int is_exactmatch;

    struct skiprecord record;
    uint64_t forwardoffsets[MAXLEVELv2];
    uint64_t backoffsets[MAXLEVELv2];
};

enum {
    UNLOCKED = 0,
    READLOCKED = 1,
    WRITELOCKED = 2,
};

struct txn {
    /* logstart is where we start changes from on commit, where we truncate
       to on abort */
    uint64_t logstart;
    uint64_t logend;			/* where to write to continue this txn */
};

struct db_header {
    /* header info */
    uint16_t version;
    uint16_t version_minor;
    uint32_t num_records;
    uint64_t logstart; /* where the log starts from last chkpnt */
    uint8_t maxlevel;
    uint8_t curlevel;
    uint32_t flags;
    uint32_t crc32;
    time_t last_recovery;
};

struct db {
    /* file data */
    char *fname;
    int fd;

    const char *map_base;
    /* obviously, you need 64 bit size_t
     * if you want 64 bit support */
    size_t map_len;	/* mapped size */
    size_t map_size;	/* actual size */
    ino_t map_ino;

    size_t header_size;
    struct db_header header;

    /* tracking info */
    int no_fsync;   /* XXX: keep it with the DB, not global */
    int do_compress; /* XXX: per DB or per config? Not sure */ 
    int lock_status;
    int is_open;
    struct txn *current_txn;

    /* comparator function to use for sorting */
    int (*compar) (const char *s1, int l1, const char *s2, int l2);
};

struct db_list {
    struct db *db;
    struct db_list *next;
    int refcount;
};

#define HEADER_MAGIC ("\241\002\213\015skiplist file\0\0\0")
#define HEADER_MAGIC_SIZE (20)

/* offsets of header files v2 */
enum {
    OFFSET_HEADER = 0,
    OFFSET_VERSION = 20,
    OFFSET_VERSION_MINOR = 24,
    OFFSET_MAXLEVEL = 28,
    OFFSET_CURLEVEL = 32,
    OFFSET_NUM_RECORDS = 36,
    OFFSET_LOGSTART = 40,
    OFFSET_LASTRECOVERYv1 = 44,
    OFFSET_LASTRECOVERYv2 = 48,
    OFFSET_FLAGS = 56,
    OFFSET_CRC32 = 60
};

#define HEADER_SIZEv1 (OFFSET_LASTRECOVERYv1 + 4)
#define HEADER_SIZEv2 (OFFSET_CRC32 + 4)
#define MAX_HEADER_SIZE (OFFSET_CRC32 + 4)

enum {
    /* Force recovery regardless of timestamp on database */
    RECOVERY_FORCE = 1,
};

static int initdone = 0;
static time_t global_recovery = 0;
static struct db_list *open_db = NULL;
static char commit_bytes[16];

static int be_paranoid = 0;

static int myinit(const char *dbdir, int myflags)
{
    char sfile[1024];
    int fd, r = 0;
    char wiretime[8];

    if (initdone) return 0;

    snprintf(sfile, sizeof(sfile), "%s/skipstamp", dbdir);

    if (myflags & CYRUSDB_RECOVER) {
	/* set the recovery timestamp; all databases earlier than this
	   time need recovery run when opened */

	global_recovery = time(NULL);
	fd = open(sfile, O_RDWR | O_CREAT, 0644);
	if (fd == -1) goto writerr;

	r = ftruncate(fd, 0);
	if (r == -1) goto writerr;

	/* store 32 bit for backwards compatibility if it fits */
	if (global_recovery < UINT32_MAX) {
	    *((uint32_t *)wiretime) = htonl(global_recovery);
	    r = write(fd, wiretime, 4);
	    if (r == -1) goto writerr;
	}
	/* support the future otherwise */
	else {
	    *((uint64_t *)wiretime) = htonll(global_recovery);
	    r = write(fd, wiretime, 8);
	    if (r == -1) goto writerr;
	}

	r = close(fd);
	if (r == -1) goto writerr;
    } else {
	/* read the global recovery timestamp */

	fd = open(sfile, O_RDONLY, 0644);
	if (fd == -1) r = -1;
	if (r != -1) r = read(fd, wiretime, 8);
	close(fd);
	if (r == 8) {
	    global_recovery = ntohll(*((uint64_t *)wiretime));
	}
	else if (r == 4) {
	    global_recovery = ntohl(*((uint32_t *)wiretime));
	}
	else {
	    syslog(LOG_ERR, "DBERROR: reading %s, assuming the worst: %m", 
		   sfile);
	    global_recovery = 0;
	}
    }

    srand(time(NULL) * getpid());

    /* initialise the "commit_bytes" comparator */
    memset(commit_bytes, 0, 16);
    commit_bytes[0] = COMMIT;
    *((uint32_t *)(commit_bytes+8)) = htonl(crc32_map(commit_bytes, 8));

    open_db = NULL;
    initdone = 1;

    return 0;

writerr:
    syslog(LOG_ERR, "DBERROR: writing %s: %m", sfile);
    if (fd != -1) close(fd);
    return CYRUSDB_IOERROR;
}

static int mydone(void)
{
    initdone = 0;

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

static int mycommit(struct db *db, struct txn *tid);
static int myabort(struct db *db, struct txn *tid);
static int mycheckpoint(struct db *db);
static int myconsistent(struct db *db, struct txn *tid, int locked);
static int recovery(struct db *db, int flags);
static int write_lock(struct db *db, const char *altname);

/* is this a complete file? */
static int SAFE_TO_APPENDv2(struct db *db)
{
    /* check it's bigger than the header */
    if (db->map_size <= HEADER_SIZEv2)
	return 1;

    /* and it must be multiple of 8 bytes */
    if (db->map_size % 8)
	return 1;

    /* and MUST end with a commit */
    if (memcmp(db->map_base + db->map_size - 16, commit_bytes, 16))
	return 1;

    return 0;
}

static int SAFE_TO_APPENDv1(struct db *db)
{
    /* check it's a multiple of 4 */
    if (db->map_size % 4) return 1;

    /* is it the beginning of the log? */
    if (db->map_size == db->header.logstart) {
	if (*((uint32_t *)(db->map_base + db->map_size - 4)) != htonl(-1)) {
	    return 1;
	}
    }

    /* in the middle of the log somewhere */
    else {
	if (*((uint32_t *)(db->map_base + db->map_size - 4)) != htonl(COMMITv1)) {
	    return 1;
	}

	/* if it's not an end of a record or a delete */
	if (!((*((uint32_t *)(db->map_base + db->map_size - 8)) == htonl(-1)) ||
	      (*((uint32_t *)(db->map_base + db->map_size -12)) == htonl(DELETEv1)))) {
	    return 1;
	}
    }

    return 0;
}

static int SAFE_TO_APPEND(struct db *db)
{
    return (db->header.version == 1) ? SAFE_TO_APPENDv1(db)
				     : SAFE_TO_APPENDv2(db);
}

static int newtxn(struct db *db, struct txn **tidptr)
{
    struct txn *tid;
    int r;

    /* grab a r/w lock */
    r = write_lock(db, NULL);
    if (r) return r;

    /* is this file safe to append to?
     * If it isn't, we need to run recovery. */
    if (SAFE_TO_APPEND(db)) {
	r = recovery(db, RECOVERY_FORCE);
	if (r) return r;
	r = write_lock(db, NULL);
        if (r) return r;
	if (SAFE_TO_APPEND(db))
	    return CYRUSDB_IOERROR; /* broken AGAIN? */
    }

    /* create the transaction */
    tid = xmalloc(sizeof(struct txn));
    tid->logstart = db->map_size;
    tid->logend = tid->logstart;
    db->current_txn = tid;

    /* pass it back out */
    *tidptr = tid;

    return 0;
}

static uint64_t roundup(uint64_t record_size, int howfar)
{
    if (record_size % howfar)
	record_size += howfar - (record_size % howfar);
    return record_size;
}

static int read_recordv2(struct db *db, uint64_t offset,
		         struct skiprecord *record)
{
    int i;

    memset(record, 0, sizeof(struct skiprecord));

    record->offset = offset;
    record->len = 8; /* header is 8 bytes */

    if (offset + record->len > db->map_size)
	goto badsize;

    /* split this into pieces */
    record->type =   db->map_base[record->offset];
    record->level =  db->map_base[record->offset+1];
    record->keylen = ntohs(*((uint16_t *)(db->map_base + record->offset + 2)));
    record->vallen = ntohl(*((uint32_t *)(db->map_base + record->offset + 4)));

    /* sanity check level is handleable - we can go up to 255 just by
     * recompiling if needed */
    if (record->level > db->header.maxlevel) {
	syslog(LOG_ERR, "DBERROR: %s: skiplist record level over maxlevel at %08llX: %d > %d",
	       db->fname, (LLU)offset, record->level, db->header.maxlevel);
	return CYRUSDB_IOERROR;
    }

    /* check for key overflow */
    if (record->keylen == UINT16_MAX) {
	if (offset + record->len + 8 > db->map_size)
	    goto badsize;
	record->keylen = ntohll(*((uint64_t *)(db->map_base + record->offset + record->len)));
	record->len += 8;
    }

    /* check for value overflow */
    if (record->vallen == UINT32_MAX) {
	if (offset + record->len + 8 > db->map_size)
	    goto badsize;
	record->vallen = ntohll(*((uint64_t *)(db->map_base + record->offset + record->len)));
	record->len += 8;
    }

    /* check for delete pointer */
    if (record->type & HAS_DELETE) {
	if (offset + record->len + 8 > db->map_size)
	    goto badsize;
	record->deloffset = ntohll(*((uint64_t *)(db->map_base + record->offset + record->len)));
	record->len += 8;
    }
    else {
	record->deloffset = 0;
    }

    /* read in skip pointers */
    for (i = 0; i < record->level; i++) {
	if (offset + record->len + 8 > db->map_size)
	    goto badsize;
	record->offsets[i] = ntohll(*((uint64_t *)(db->map_base + record->offset + record->len)));
	record->len += 8;
    }

    if (offset + record->len + 8 > db->map_size)
	goto badsize;
    record->crc32_head = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len)));
    if (crc32_map(db->map_base + record->offset, record->len) != record->crc32_head)
	return CYRUSDB_IOERROR;
    record->crc32_tail = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len+4)));
    record->len += 8;

    record->key = db->map_base + record->offset + record->len;
    record->len += record->keylen; /* XXX: unaligned value - is the tradeoff good? */

    record->val = db->map_base + record->offset + record->len;
    record->len += record->vallen;

    /* round up the final figure */
    record->len = roundup(record->len, 8);

    /* and make sure the whole rest fits */
    if (offset + record->len > db->map_size)
	goto badsize;

    return 0;

badsize:
    syslog(LOG_ERR, "skiplist: attempt to read past end of file %s: %08llX > %08llX",
	   db->fname, (LLU)offset + record->len, (LLU)db->map_size);
    return CYRUSDB_IOERROR;
}

static int read_recordv1(struct db *db, uint64_t offset,
		         struct skiprecord *record)
{
    uint32_t type;
    uint32_t ptr;

    memset(record, 0, sizeof(struct skiprecord));

    record->offset = offset;
    record->len = 4; /* header is 4 bytes */

    if (offset + record->len > db->map_size)
	goto badsize;

    /* split this into pieces */
    type = ntohl(*((uint32_t *)(db->map_base + record->offset)));
    if (type == COMMITv1) {
	record->type = COMMIT;
	return 0;
    }

    if (type == DELETEv1) {
	if (offset + record->len + 4 > db->map_size)
	    goto badsize;
	record->deloffset = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len)));
	record->type = DELETE;
	record->len += 4; /* header is 4 bytes */
	return 0;
    }

    if (type == INORDERv1 || type == ADDv1)
	record->type = ADD;
    else if (type == DUMMYv1)
	record->type = DUMMY;
    else
	return CYRUSDB_IOERROR; /* unknown type */


    /* read the key */
    if (offset + record->len + 4 > db->map_size)
	goto badsize;
    record->keylen = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len)));
    record->key = db->map_base + record->offset + record->len + 4;
    record->len += 4 + roundup(record->keylen, 4);

    /* read the value */
    if (offset + record->len + 4 > db->map_size)
	goto badsize;
    record->vallen = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len)));
    record->val = db->map_base + record->offset + record->len + 4;
    record->len += 4 + roundup(record->vallen, 4);

    /* read the pointers */
    while (record->level <= db->header.maxlevel) {
	if (offset + record->len + 4 > db->map_size)
	    goto badsize;
	ptr = ntohl(*((uint32_t *)(db->map_base + record->offset + record->len)));
	record->len += 4;
	if (ptr == (uint32_t)-1) return 0; /* found the end */
	record->offsets[record->level] = ptr;
	record->level++;
    }

    /* failed to exit correctly */
    return CYRUSDB_IOERROR;

badsize:
    syslog(LOG_ERR, "skiplist: attempt to read past end of file %s: %08llX > %08llX",
	   db->fname, (LLU)offset + record->len, (LLU)db->map_size);
    return CYRUSDB_IOERROR;
}

static int read_record(struct db *db, uint64_t offset,
		       struct skiprecord *record)
{
    return (db->header.version == 1) ? read_recordv1(db, offset, record)
				     : read_recordv2(db, offset, record);
}

static int advance_loc(struct db *db, struct skiploc *loc)
{
    uint8_t i;
    int r;

    if (loc->is_exactmatch) {
	/* update the offsets */
	for (i = 0; i < loc->record.level; i++) {
	    loc->backoffsets[i] = loc->record.offset;
	    loc->forwardoffsets[i] = loc->record.offsets[i];
	}

	/* hit the end?  Dummy time */
	if (!loc->record.offsets[0]) {
	    loc->record.offsets[0] = db->header_size;
	}

	r = read_record(db, loc->record.offsets[0], &loc->record);
	if (r) return r;
    }

    /* well, it's always on a record now! */
    loc->is_exactmatch = loc->record.type == DUMMY ? 0 : 1;
    loc->key = loc->record.key;
    loc->keylen = loc->record.keylen;

    return 0;
}

/* given an open, mapped db, read in the header information */
static int read_header(struct db *db)
{
    assert(db && db->map_len && db->fname && db->map_base
              && db->is_open && db->lock_status);
    if (db->map_len < OFFSET_LOGSTART) {
	syslog(LOG_ERR,
	       "skiplist: file not large enough for header: %s", db->fname);
    }

    if (memcmp(db->map_base, HEADER_MAGIC, HEADER_MAGIC_SIZE)) {
	syslog(LOG_ERR, "skiplist: invalid magic header: %s", db->fname);
	return CYRUSDB_IOERROR;
    }

    db->header.version
	= ntohl(*((uint32_t *)(db->map_base + OFFSET_VERSION)));
    db->header.version_minor
	= ntohl(*((uint32_t *)(db->map_base + OFFSET_VERSION_MINOR)));

    if (db->header.version > VERSION) {
	syslog(LOG_ERR, "skiplist: version mismatch: %s has version %d.%d",
	       db->fname, db->header.version, db->header.version_minor);
	return CYRUSDB_IOERROR;
    }

    db->header.maxlevel
	= ntohl(*((uint32_t *)(db->map_base + OFFSET_MAXLEVEL)));
    db->header.curlevel
	= ntohl(*((uint32_t *)(db->map_base + OFFSET_CURLEVEL)));
    db->header.num_records
	= ntohl(*((uint32_t *)(db->map_base + OFFSET_NUM_RECORDS)));

    if (db->header.version == 1) {
	db->header.logstart
	    = ntohl(*((uint32_t *)(db->map_base + OFFSET_LOGSTART)));
	db->header.last_recovery
	    = ntohl(*((uint32_t *)(db->map_base + OFFSET_LASTRECOVERYv1)));
	db->header_size = HEADER_SIZEv1;
    }
    else {
	db->header.logstart
	    = ntohll(*((uint64_t *)(db->map_base + OFFSET_LOGSTART)));
	db->header.last_recovery
	    = ntohll(*((uint64_t *)(db->map_base + OFFSET_LASTRECOVERYv2)));
	db->header.flags
	    = ntohl(*((uint32_t *)(db->map_base + OFFSET_FLAGS)));
	db->header.crc32
	    = ntohl(*((uint32_t *)(db->map_base + OFFSET_CRC32)));

	if (crc32_map(db->map_base, OFFSET_CRC32) != db->header.crc32) {
	    syslog(LOG_ERR, "DBERROR: %s: skiplist2 header CRC failure",
	           db->fname);
	    return CYRUSDB_IOERROR;
	}
	db->header_size = HEADER_SIZEv2;
    }

    return 0;
}

/* given an open, mapped db, locked db,
   write the header information */
static int write_header(struct db *db)
{
    char buf[MAX_HEADER_SIZE];
    int n;

    assert(db->lock_status == WRITELOCKED);

    /* format one buffer */
    memcpy(buf + 0, HEADER_MAGIC, HEADER_MAGIC_SIZE);
    *((uint32_t *)(buf + OFFSET_VERSION)) = htonl(db->header.version);
    *((uint32_t *)(buf + OFFSET_VERSION_MINOR)) = htonl(db->header.version_minor);
    *((uint32_t *)(buf + OFFSET_MAXLEVEL)) = htonl(db->header.maxlevel);
    *((uint32_t *)(buf + OFFSET_CURLEVEL)) = htonl(db->header.curlevel);
    *((uint32_t *)(buf + OFFSET_NUM_RECORDS)) = htonl(db->header.num_records);
    if (db->header.version == 1) {
	*((uint32_t *)(buf + OFFSET_LOGSTART)) = htonl(db->header.logstart);
	*((uint32_t *)(buf + OFFSET_LASTRECOVERYv1)) = htonl(db->header.last_recovery);
    } else {
	*((uint64_t *)(buf + OFFSET_LOGSTART)) = htonll(db->header.logstart);
	*((uint64_t *)(buf + OFFSET_LASTRECOVERYv2)) = htonll(db->header.last_recovery);
	*((uint32_t *)(buf + OFFSET_FLAGS)) = htonl(db->header.flags);
	*((uint32_t *)(buf + OFFSET_CRC32)) = htonl(crc32_map(buf, OFFSET_CRC32));
    }

    /* write it out */
    lseek(db->fd, 0, SEEK_SET);
    n = retry_write(db->fd, buf, db->header_size);
    if (n != (int)db->header_size) {
	syslog(LOG_ERR, "DBERROR: writing skiplist2 header for %s: %m",
	       db->fname);
	return CYRUSDB_IOERROR;
    }

    return 0;
}

static char *prepare_recordv2(struct skiprecord *record, size_t *sizep)
{
    static char writebuf[MAXRECORDHEAD];
    int len = 8;
    int i;

    writebuf[0] = record->type;
    writebuf[1] = record->level;
    if (record->keylen < UINT16_MAX)
	*((uint16_t *)(writebuf+2)) = htons(record->keylen);
    if (record->vallen < UINT32_MAX)
	*((uint32_t *)(writebuf+4)) = htonl(record->vallen);

    if (record->keylen >= UINT16_MAX) {
	*((uint32_t *)(writebuf+4)) = htons(UINT16_MAX);
	*((uint64_t *)(writebuf+len)) = htonll(record->keylen);
	len += 8;
    }

    if (record->vallen >= UINT32_MAX) {
	*((uint32_t *)(writebuf)) = htonl(UINT32_MAX);
	*((uint64_t *)(writebuf+len)) = htonll(record->vallen);
	len += 8;
    }

    if (record->deloffset) {
	*((uint64_t *)(writebuf+len)) = htonll(record->deloffset);
	len += 8;
    }

    for (i = 0; i < record->level; i++) {
	*((uint64_t *)(writebuf+len)) = htonll(record->offsets[i]);
	len += 8;
    }

    record->crc32_head = crc32_map(writebuf, len);
    *((uint32_t *)(writebuf+len)) = htonl(record->crc32_head);
    *((uint32_t *)(writebuf+len+4)) = htonl(record->crc32_tail);
    len += 8;

    *sizep = len;

    return writebuf;
}

static int rewrite_recordv2(struct db *db, struct skiprecord *record)
{
    const char *buf;
    size_t len;
    int n;

    lseek(db->fd, record->offset, 0);

    buf = prepare_recordv2(record, &len);
    n = retry_write(db->fd, buf, len);
    if (n == -1)
	return CYRUSDB_IOERROR;

    return 0;
}

static int rewrite_recordv1(struct db *db, struct skiprecord *record)
{
    static char ptrs[4*MAXLEVELv1];
    int i;
    int n;
    size_t offset;
    assert(record->type & HAS_LEVEL);

    /* find the pointers! three 32 bit values plus key and value */
    offset = 12 + roundup(record->keylen, 4) + roundup(record->vallen, 4);

    /* write all the offsets in */
    for (i = 0; i < record->level; i++) {
	*((uint32_t *)(ptrs + 4*i)) = htonl(record->offsets[i]);
    }

    lseek(db->fd, record->offset + offset, 0);
    n = retry_write(db->fd, ptrs, 4 * record->level);
    if (n == -1)
	return CYRUSDB_IOERROR;

    return 0;
}

static int rewrite_record(struct db *db, struct skiprecord *record)
{
    return (db->header.version == 1) ? rewrite_recordv1(db, record)
				     : rewrite_recordv2(db, record);
}

static int zencode(struct skiprecord *record)
{
    static struct buf localbuf = BUF_INITIALIZER;

    /* already compressed? */
    if (record->type & HAS_COMPRESS)
	return 0;

    /* nothing to compress? */
    if (!(record->type & HAS_VALUE))
	return 0;

    /* don't compress tiny values */
    if (record->vallen < 8)
	return 0;

#ifdef HAVE_ZLIB
    buf_free(&localbuf);
    buf_init_ro(&localbuf, record->val, record->vallen);

    if (!buf_deflate(&localbuf)) {
	/* success, change type */
	record->type |= HAS_COMPRESS;
	record->val = localbuf.s;
	record->vallen = localbuf.len;
    }

    /* otherwise it's OK, we just store uncompressed */
#endif

    return 0;
}

static int zdecode(struct skiprecord *record)
{
    static struct buf localbuf = BUF_INITIALIZER;

    /* nothing to decode? */
    if (!(record->type & HAS_COMPRESS))
	return 0;

#ifdef HAVE_ZLIB
    buf_free(&localbuf);
    buf_init_ro(&localbuf, record->val, record->vallen);
    if (!buf_inflate(&localbuf)) {
	/* success, change type */
	record->type &= ~HAS_COMPRESS;
	record->val = localbuf.s;
	record->vallen = localbuf.len;
	return 0;
    }
#endif

    /* can't process compressed records without zlib! */
    return CYRUSDB_INTERNAL;
}

static int write_recordv2(struct db *db,
			  struct skiprecord *record,
			  uint64_t *offsetp)
{
    char zeros[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    int n;
    uint64_t len;
    struct iovec io[4];

    if (db->do_compress) zencode(record);

    /* we'll put the HEAD here later */
    io[0].iov_base = zeros;
    io[0].iov_len = 0;

    io[1].iov_base = (char *)record->key;
    io[1].iov_len = record->keylen;
    /* XXX - padding? */
    io[2].iov_base = (char *)record->val;
    io[2].iov_len = record->vallen;

    len = record->vallen + record->keylen;
    io[3].iov_base = zeros;
    io[3].iov_len = roundup(len, 8) - len;

    record->crc32_tail = crc32_iovec(io, 4);

    /* prepare the record once we know the crc32 of the tail.
     * this works because io[0] is zero bytes, so only the
     * tail gets calculated */
    io[0].iov_base = prepare_recordv2(record, &io[0].iov_len);

    lseek(db->fd, *offsetp, 0);
    n = retry_writev(db->fd, io, 4);
    if (n == -1)
	return CYRUSDB_IOERROR;

    record->offset = *offsetp;
    record->len = n;
    *offsetp += record->len;

    if (db->map_size < *offsetp) {
	db->map_size = *offsetp;
	map_refresh(db->fd, 0, &db->map_base, &db->map_len, db->map_size,
		    db->fname, 0);
    }

    return 0;
}
static int write_recordv1(struct db *db,
			  struct skiprecord *record,
			  uint64_t *offsetp)
{
    char zeros[4];
    int n;
    int i;
    int r;

    char startbuf[12];
    char keylenbuf[4];
    char vallenbuf[4];
    char ptrs[4*MAXLEVELv1];
    char minusone[4];

    struct iovec io[9];
    int nio = 1;

    /* can't be compressed */
    r = zdecode(record);
    if (r) return r;

    io[0].iov_base = startbuf;
    io[0].iov_len = 4;

    switch (record->type) {
    case COMMIT:
	*((uint32_t *)startbuf) = htonl(COMMITv1);
	goto write;

    case DELETE:
	*((uint32_t *)(startbuf)) = htonl(DELETEv1);
	*((uint32_t *)(startbuf+4)) = htonl(record->deloffset);
	io[0].iov_len = 8;
	goto write;

    case REPLACE:
	/* tricky! - 2 records */
	*((uint32_t *)(startbuf)) = htonl(DELETEv1);
	*((uint32_t *)(startbuf+4)) = htonl(record->deloffset);
	*((uint32_t *)(startbuf+8)) = htonl(ADDv1);
	io[0].iov_len = 12;
	break;

    case ADD:
	/* check if we're INORDER or later */
	if (record->offset < db->header.logstart)
	    *((uint32_t *)startbuf) = htonl(INORDERv1);
	else
	    *((uint32_t *)startbuf) = htonl(ADDv1);
	break;

    case DUMMY:
	*((uint32_t *)startbuf) = htonl(DUMMYv1);
	break;
    }

    /* format the rest of the record for the wire */
    *((uint32_t *)zeros) = htonl(0);

    /* key */
    *((uint32_t *)keylenbuf) = htonl(record->keylen);
    io[1].iov_base = keylenbuf;
    io[1].iov_len = 4;
    io[2].iov_base = (char *)record->key;
    io[2].iov_len = record->keylen;
    io[3].iov_base = zeros;
    io[3].iov_len = roundup(record->keylen, 4) - record->keylen;

    /* val */
    *((uint32_t *)vallenbuf) = htonl(record->vallen);
    io[4].iov_base = vallenbuf;
    io[4].iov_len = 4;
    io[5].iov_base = (char *)record->val;
    io[5].iov_len = record->vallen;
    io[6].iov_base = zeros;
    io[6].iov_len = roundup(record->vallen, 4) - record->vallen;

    /* pointers */
    *((uint32_t *)minusone) = htonl(-1);
    for (i = 0; i < record->level; i++) {
	*((uint32_t *)(ptrs + 4*i)) = htonl(record->offsets[i]);
    }

    io[7].iov_base = ptrs;
    io[7].iov_len = 4 * record->level;
    io[8].iov_base = minusone;
    io[8].iov_len = 4;

    nio = 9;

write:
    lseek(db->fd, *offsetp, 0);
    n = retry_writev(db->fd, io, nio);
    if (n == -1)
	return CYRUSDB_IOERROR;

    record->offset = *offsetp;
    record->len = n;
    *offsetp += record->len;

    /* special case REPLACE became an ADD and a DELETE, and
     * we only want to remember the second one! */
    if (record->type == REPLACE) {
	record->deloffset = 0;
	record->offset += 8;
	record->len -= 8;
	record->type = ADD;
    }

    if (db->map_size < *offsetp) {
	db->map_size = *offsetp;
	map_refresh(db->fd, 0, &db->map_base, &db->map_len, db->map_size,
		    db->fname, 0);
    }

    return 0;
}

static int write_record(struct db *db,
			struct skiprecord *record,
			uint64_t *offsetp)
{
    return (db->header.version == 1) ? write_recordv1(db, record, offsetp)
				     : write_recordv2(db, record, offsetp);
}

/* shortcut - we don't map commits, because they're not in the stream */
static int write_commitv2(struct db *db, uint64_t offset)
{
    int n;

    lseek(db->fd, offset, 0);
    n = retry_write(db->fd, commit_bytes, 16);
    if (n == -1)
	return CYRUSDB_IOERROR;

    return 0;
}

static int write_commitv1(struct db *db, uint64_t offset)
{
    int n;
    char bytes[4];

    /* special case - we don't commit the logstart in v1 */
    if (offset == db->header.logstart)
	return 0;

    *((uint32_t *)bytes) = htonl(COMMITv1);

    lseek(db->fd, offset, 0);
    n = retry_write(db->fd, bytes, 4);
    if (n == -1)
	return CYRUSDB_IOERROR;

    return 0;
}

static int write_commit(struct db *db, uint64_t offset)
{
    return (db->header.version == 1) ? write_commitv1(db, offset)
				     : write_commitv2(db, offset);
}

static int write_delete(struct db *db, uint64_t deloffset, uint64_t *offsetp)
{
    struct skiprecord record;
    int r;

    memset(&record, 0, sizeof(struct skiprecord));

    record.type = DELETE;
    record.deloffset = deloffset;

    r = write_record(db, &record, offsetp);
    if (r) return r;

    return 0;
}


/* make sure our mmap() is big enough */
static int update_lock(struct db *db, struct txn *txn)
{
    /* txn->logend is the current size of the file */
    assert (db->is_open && db->lock_status == WRITELOCKED);
    map_refresh(db->fd, 0, &db->map_base, &db->map_len, txn->logend,
		db->fname, 0);
    db->map_size = txn->logend;

    return 0;
}

static int write_lock(struct db *db, const char *altname)
{
    struct stat sbuf;
    const char *lockfailaction;
    const char *fname = altname ? altname : db->fname;

    assert(db->lock_status == UNLOCKED);
    if (lock_reopen(db->fd, fname, &sbuf, &lockfailaction) < 0) {
	syslog(LOG_ERR, "IOERROR: %s %s: %m", lockfailaction, fname);
	return CYRUSDB_IOERROR;
    }
    if (db->map_ino != sbuf.st_ino) {
	map_free(&db->map_base, &db->map_len);
    }
    db->map_size = sbuf.st_size;
    db->map_ino = sbuf.st_ino;
    db->lock_status = WRITELOCKED;

    map_refresh(db->fd, 0, &db->map_base, &db->map_len, sbuf.st_size,
		fname, 0);

    if (db->is_open) {
	/* reread header */
	read_header(db);
    }

    /* printf("%d: write lock: %d\n", getpid(), db->map_ino); */

    return 0;
}

static int read_lock(struct db *db)
{
    struct stat sbuf, sbuffile;
    int newfd = -1;

    assert(db->lock_status == UNLOCKED);
    for (;;) {
	if (lock_shared(db->fd) < 0) {
	    syslog(LOG_ERR, "IOERROR: lock_shared %s: %m", db->fname);
	    return CYRUSDB_IOERROR;
	}

	if (fstat(db->fd, &sbuf) == -1) {
	    syslog(LOG_ERR, "IOERROR: fstat %s: %m", db->fname);
	    lock_unlock(db->fd);
	    return CYRUSDB_IOERROR;
	}

	if (stat(db->fname, &sbuffile) == -1) {
	    syslog(LOG_ERR, "IOERROR: stat %s: %m", db->fname);
	    lock_unlock(db->fd);
	    return CYRUSDB_IOERROR;
	}
	if (sbuf.st_ino == sbuffile.st_ino) break;

	newfd = open(db->fname, O_RDWR, 0644);
	if (newfd == -1) {
	    syslog(LOG_ERR, "IOERROR: open %s: %m", db->fname);
	    lock_unlock(db->fd);
	    return CYRUSDB_IOERROR;
	}

	dup2(newfd, db->fd);
	close(newfd);
    }

    if (db->map_ino != sbuf.st_ino) {
	map_free(&db->map_base, &db->map_len);
    }
    db->map_size = sbuf.st_size;
    db->map_ino = sbuf.st_ino;
    db->lock_status = READLOCKED;

    /* printf("%d: read lock: %d\n", getpid(), db->map_ino); */

    map_refresh(db->fd, 0, &db->map_base, &db->map_len, sbuf.st_size,
		db->fname, 0);

    if (db->is_open) {
	/* reread header */
	read_header(db);
    }

    return 0;
}

static int unlock(struct db *db)
{
    if (db->lock_status == UNLOCKED) 
	return 0;

    if (lock_unlock(db->fd) < 0) {
	syslog(LOG_ERR, "IOERROR: lock_unlock %s: %m", db->fname);
	return CYRUSDB_IOERROR;
    }

    db->lock_status = UNLOCKED;

    return 0;
}

static int lock_or_refresh(struct db *db, struct txn **tidptr)
{
    assert(db != NULL && tidptr != NULL);

    if (!*tidptr) {
	/* check that the DB isn't in a transaction */
	assert(db->current_txn == NULL);

	/* start the transaction */
	return newtxn(db, tidptr);
    }

    /* check that the DB agrees that we're in this transaction */
    assert(db->current_txn == *tidptr);

    /* just update the active transaction */
    update_lock(db, *tidptr);

    return 0;
}

static int dispose_db(struct db *db)
{
    if (!db) return 0;

    if (db->lock_status) {
	syslog(LOG_ERR, "skiplist: closed while still locked");
	unlock(db);
    }
    if (db->fname) {
	free(db->fname);
    }
    if (db->map_base) {
	map_free(&db->map_base, &db->map_len);
    }
    if (db->fd != -1) {
	close(db->fd);
    }

    free(db);

    return 0;
}

static int db_fsync(struct db *db)
{
    if (!db->no_fsync) {
	if (fsync(db->fd) < 0)
	    return CYRUSDB_IOERROR;
    }
    return 0;
}

static int myopen(const char *fname, int flags, struct db **ret, int version)
{
    struct db *db;
    struct db_list *list_ent = open_db;
    int r;

    if (!fname || !ret) return CYRUSDB_BADPARAM;

    while (list_ent && strcmp(list_ent->db->fname, fname)) {
	list_ent = list_ent->next;
    }
    if (list_ent) {
	/* we already have this DB open! */
	syslog(LOG_NOTICE, "skiplist: %s is already open %d time%s, returning object",
	fname, list_ent->refcount, list_ent->refcount == 1 ? "" : "s");
	*ret = list_ent->db;
	++list_ent->refcount;
	return 0;
    }

    db = (struct db *) xzmalloc(sizeof(struct db));
    db->fd = -1;
    db->fname = xstrdup(fname);
    db->compar = (flags & CYRUSDB_MBOXSORT) ? bsearch_ncompare : compare;
    db->no_fsync = libcyrus_config_getswitch(CYRUSOPT_SKIPLIST_UNSAFE);
    db->do_compress = (flags & CYRUSDB_ZLIB);

    db->fd = open(fname, O_RDWR, 0644);
    if (db->fd == -1 && errno == ENOENT) {
	if (!(flags & CYRUSDB_CREATE)) {
	    r = CYRUSDB_NOTFOUND;
	    goto done;
	}
	if (cyrus_mkdir(fname, 0755) == -1) {
	    r = CYRUSDB_IOERROR;
	    goto done;
	}
	db->fd = open(fname, O_RDWR | O_CREAT, 0644);
    }

    if (db->fd == -1) {
	syslog(LOG_ERR, "IOERROR: opening %s: %m", fname);
	r = CYRUSDB_IOERROR;
	goto done;
    }

    db->is_open = 0;
    db->lock_status = UNLOCKED;

    /* grab a read lock, only reading the header */
    r = read_lock(db);
    if (r) goto done;

    /* if the file is empty, then the header needs to be created first */
    if (db->map_size == 0) {
	unlock(db);
	r = write_lock(db, NULL);
	if (r) goto done;
    }

    /* race condition.  Another process may have already got the write
     * lock and created the header. Only go ahead if the map_size is
     * still zero (read/write_lock updates map_size). */
    if (db->map_size == 0) {
	struct skiprecord dummy;

	/* initialize in memory structure */
	db->header.version = version;
	db->header.version_minor = (version == 1) ? 2 : VERSION_MINOR;
	db->header.last_recovery = time(NULL);
	db->header_size = (version == 1) ? HEADER_SIZEv1 : HEADER_SIZEv2;
	db->header.maxlevel = (version == 1) ? MAXLEVELv1 : MAXLEVELv2;
	db->header.curlevel = db->header.maxlevel; /* bogus optimisation */

	/* create the dummy! */
	memset(&dummy, 0, sizeof(struct skiprecord));
	dummy.type = DUMMY;
	dummy.level = db->header.maxlevel;

	db->header.logstart = db->header_size;
	r = write_record(db, &dummy, &db->header.logstart);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: writing dummy node for %s: %m",
		   db->fname);
	    goto done;
	}

	/* create the header */
	r = write_header(db);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: writing header for %s: %m",
		   db->fname);
	    goto done;
	}

	/* v1 this should magically do nothing :) */
	r = write_commit(db, db->header.logstart);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: writing commit for %s: %m",
		   db->fname);
	    goto done;
	}

	/* sync the db */
	r = db_fsync(db);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: fsync(%s): %m", db->fname);
	    goto done;
	}

	/* map the header in so we can read it */
	db->map_size = db->header.logstart;
	map_refresh(db->fd, 0, &db->map_base, &db->map_len, db->map_size,
		    db->fname, 0);
    }

    db->is_open = 1;

    r = read_header(db);
    if (r) goto done;

    /* unlock the DB */
    unlock(db);

    if (!global_recovery || db->header.last_recovery < global_recovery) {
	/* run recovery; we rebooted since the last time recovery
	   was run */
	r = write_lock(db, NULL);
	if (r) goto done;
	r = recovery(db, 0);
	if (r) goto done;
    }

    *ret = db;

    /* track this database in the open list */
    list_ent = (struct db_list *) xzmalloc(sizeof(struct db_list));
    list_ent->db = db;
    list_ent->next = open_db;
    list_ent->refcount = 1;
    open_db = list_ent;

done:
    if (r) dispose_db(db);
    return r;
}

static int myclose(struct db *db)
{
    struct db_list *list_ent = open_db;
    struct db_list *prev = NULL;

    if (!db) return CYRUSDB_BADPARAM;

    /* remove this DB from the open list */
    while (list_ent && list_ent->db != db) {
	prev = list_ent;
	list_ent = list_ent->next;
    }
    assert(list_ent);
    if (--list_ent->refcount <= 0) {
	if (prev) prev->next = list_ent->next;
	else open_db = list_ent->next;
	free(list_ent);
	return dispose_db(db);
    }

    return 0;
}

/* finds a record, either an exact match or the record
 * immediately afterwards */
static int find_loc(struct db *db,
		    const char *key, int keylen,
		    struct skiploc *loc)
{
    uint8_t level;
    uint8_t i;
    int cmp;
    int r;

    assert(db);
    assert(loc);

    memset(loc, 0, sizeof(struct skiploc));

    /* track where we're looking */
    loc->key = key;
    loc->keylen = keylen;

    /* initialise with the dummy */
    r = read_record(db, db->header_size, &loc->record);
    if (r) return r;

    /* starting pointers */
    for (i = 0; i < loc->record.level; i++) {
	loc->backoffsets[i] = loc->record.offset; /* DUMMY_OFFSET */
	loc->forwardoffsets[i] = loc->record.offsets[i];
    }

    /* for-loop that's unsigned-safe */
    level = loc->record.level;
    while (level) {
	while (loc->forwardoffsets[level-1]) {
	    r = read_record(db, loc->forwardoffsets[level-1], &loc->record);
	    if (r) return r;
	    assert(loc->record.level >= level);
	    cmp = db->compar(loc->record.key, loc->record.keylen,
			     loc->key, loc->keylen);
	    /* no longer "before", so we keep looking */
	    if (cmp >= 0) {
		if (cmp == 0) loc->is_exactmatch = 1;
		break;
	    }
	    /* keep looking, we're not there yet */
	    for (i = 0; i < level; i++) {
		loc->backoffsets[i] = loc->record.offset;
		loc->forwardoffsets[i] = loc->record.offsets[i];
	    }
	}

	level--;
	/* skip identical levels */
	while (level && loc->forwardoffsets[level]
		     == loc->forwardoffsets[level-1])
	    level--;
    }

    return 0;
}

static int myfetch(struct db *db,
	    const char *key, size_t keylen,
	    const char **foundkey, size_t *foundkeylen,
	    const char **data, size_t *datalen,
	    struct txn **tidptr, int fetchnext)
{
    struct skiploc loc;
    int r = 0;

    if (!db) return CYRUSDB_BADPARAM;
    if (data && !datalen) return CYRUSDB_BADPARAM;

    if (data) *data = NULL;
    if (datalen) *datalen = 0;

    /* Hacky workaround:
     *
     * If no transaction was passed, but we're in a transaction,
     * then just do the read within that transaction.
     */
    if (!tidptr && db->current_txn != NULL) {
	tidptr = &(db->current_txn);
    }

    if (tidptr) {
	/* make sure we're write locked and up to date */
	if ((r = lock_or_refresh(db, tidptr)) < 0) {
	    return r;
	}
    } else {
	/* grab a r lock */
	if ((r = read_lock(db)) < 0) {
	    return r;
	}
    }

    r = find_loc(db, key, keylen, &loc);
    if (r) goto done;

    if (fetchnext) {
	r = advance_loc(db, &loc);
	if (r) goto done;
    }

    if (foundkey) *foundkey = loc.key;
    if (foundkeylen) *foundkeylen = loc.keylen;

    if (!r && loc.is_exactmatch) {
	if (data || datalen) {
	    r = zdecode(&loc.record);
	}
	if (!r) {
	    if (data) *data = loc.record.val;
	    if (datalen) *datalen = loc.record.vallen;
	}
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

static int fetch(struct db *mydb,
		 const char *key, size_t keylen,
		 const char **data, size_t *datalen,
		 struct txn **tidptr)
{
    if (!key || !keylen) return CYRUSDB_BADPARAM;
    return myfetch(mydb, key, keylen, NULL, NULL,
		   data, datalen, tidptr, 0);
}
static int fetchlock(struct db *mydb,
		     const char *key, size_t keylen,
		     const char **data, size_t *datalen,
		     struct txn **tidptr)
{
    if (!key || !keylen) return CYRUSDB_BADPARAM;
    return myfetch(mydb, key, keylen, NULL, NULL,
		   data, datalen, tidptr, 0);
}

static int fetchnext(struct db *mydb,
		     const char *key, size_t keylen,
		     const char **retkey, size_t *retkeylen,
		     const char **data, size_t *datalen,
		     struct txn **tidptr)
{
    return myfetch(mydb, key, keylen, retkey, retkeylen,
		   data, datalen, tidptr, 1);
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
    struct skiploc loc;
    int r = 0, cb_r = 0;
    int need_unlock = 0;
    char *lastkey = NULL;

    if (!db || !cb) return CYRUSDB_BADPARAM;
    if (prefixlen && !prefix) return CYRUSDB_BADPARAM;

    /* Hacky workaround:
     *
     * If no transaction was passed, but we're in a transaction,
     * then just do the read within that transaction. 
     */
    if (!tidptr && db->current_txn != NULL) {
	tidptr = &(db->current_txn);
    }

    if (tidptr) {
	/* make sure we're write locked and up to date */
	r = lock_or_refresh(db, tidptr);
	if (r) goto done;
    } else {
	/* grab a r lock */
	r = read_lock(db);
	if (r) goto done;
	need_unlock = 1;
    }

    r = find_loc(db, prefix, prefixlen, &loc);
    if (r) goto done;

    if (!loc.is_exactmatch) {
	/* advance to the first match */
	r = advance_loc(db, &loc);
	if (r) goto done;
    }

    while (loc.record.type != DUMMY) {
	/* does it match prefix? */
	if (prefixlen) {
	    if (loc.record.keylen < prefixlen) break;
	    if (db->compar(loc.record.key, prefixlen, prefix, prefixlen)) break;
	}

	r = zdecode(&loc.record);
	if (r) goto done;

	if (!goodp || goodp(rock, loc.record.key, loc.record.keylen,
				  loc.record.val, loc.record.vallen)) {
	    size_t sz = db->map_size;
	    ino_t ino = db->map_ino;

	    if (!tidptr) {
		/* release read lock */
		r = unlock(db);
		if (r) goto done;
		need_unlock = 0;
	    }

	    free(lastkey);
	    lastkey = xstrndup(loc.record.key, loc.record.keylen);

	    /* make callback */
	    cb_r = cb(rock, loc.record.key, loc.record.keylen,
			    loc.record.val, loc.record.vallen);
	    if (cb_r) break;

	    if (!tidptr) {
		/* grab a r lock */
		r = read_lock(db);
		if (r) goto done;
		need_unlock = 1;
	    } else {
		/* make sure we're up to date */
		update_lock(db, *tidptr);
	    }

	    /* reposition */
	    if (ino != db->map_ino || sz != db->map_size) {
		/* something changed in the file; reseek to the record */
		r = find_loc(db, lastkey, strlen(lastkey), &loc);
		if (r) goto done;
	    }
	}
	/* move to the next one */
	r = advance_loc(db, &loc);
	if (r) goto done;
    }

 done:
    free(lastkey);

    if (need_unlock) {
	/* release read lock */
	int r1 = unlock(db);
	if (r1) return r1;
    }

    return r ? r : cb_r;
}

static uint8_t randlvl(uint8_t maxlevel)
{
    uint8_t lvl = 1;

    while ((((float) rand() / (float) (RAND_MAX)) < PROB)
	   && (lvl < maxlevel)) {
	lvl++;
    }
    /* syslog(LOG_DEBUG, "picked level %d", lvl); */

    return lvl;
}

static int stitch_record(struct db *db, struct skiploc *loc)
{
    struct skiprecord oldrecord;
    int level = 0;
    int r;

    /* OK, so we're adding this record into place.
     * update the reverse locations to point here, and
     * make sure that the forward pointers are right too */

    /* STITCH always happens from the bottom up, so that
     * a broken set of links never leaves reversed nodes */
    while (level < loc->record.level) {
	r = read_record(db, loc->backoffsets[level], &oldrecord);
	if (r) return r;

	oldrecord.offsets[level] = loc->record.offset;
	loc->forwardoffsets[level] = loc->record.offset;

	/* merge identical records */
	while (level < loc->record.level &&
	       loc->backoffsets[level] == oldrecord.offset) {
	    loc->forwardoffsets[level] = loc->record.offset;
	    oldrecord.offsets[level] = loc->record.offset;
	    level++;
	}

	r = rewrite_record(db, &oldrecord);
	if (r) return r;
    }

    /* we just stitched this record into place, so it's an
     * exact match */
    loc->is_exactmatch = 1;
    loc->key = loc->record.key;
    loc->keylen = loc->record.keylen;

    return 0;
}

static int unstitch_record(struct db *db, struct skiploc *loc)
{
    struct skiprecord oldrecord;
    int level = loc->record.level;
    int r;

    /* Remove from High to Low for the opposite reason to the
     * stitching above */
    while (level) {
	r = read_record(db, loc->backoffsets[level-1], &oldrecord);
	if (r) return r;

	/* merge identical records */
	while (level && loc->backoffsets[level-1] == oldrecord.offset) {
	    level--;
	    /* should be pointing here now! */
	    if (oldrecord.offsets[level] != loc->record.offset)
		return CYRUSDB_NOTFOUND;
	    /* make it point past */
	    oldrecord.offsets[level] = loc->record.offsets[level];
	}

	r = rewrite_record(db, &oldrecord);
	if (r) return r;
    }

    /* no longer there, so we don't have an exact match */
    loc->is_exactmatch = 0;
    loc->key = loc->record.key;
    loc->keylen = loc->record.keylen;

    return 0;
}

static int mystore(struct db *db,
	    const char *key, size_t keylen,
	    const char *data, size_t datalen,
	    struct txn **tidptr, int overwrite)
{
    struct skiploc loc;
    struct txn *tid;
    struct txn *localtid = NULL;
    int r;
    int i;

    if (!db || !key || !keylen) return CYRUSDB_BADPARAM;
    if (datalen && !data) return CYRUSDB_BADPARAM;

    /* not keeping the transaction, just create one local to
     * this function */
    if (!tidptr) {
	tidptr = &localtid;
    }

    /* make sure we're write locked and up to date */
    if ((r = lock_or_refresh(db, tidptr)) < 0) {
	return r;
    }

    tid = *tidptr; /* consistent naming is nice */

    if (be_paranoid) {
	assert(myconsistent(db, tid, 1) == 0);
    }

    r = find_loc(db, key, keylen, &loc);
    if (r) goto done;

    if (loc.is_exactmatch) {
	if (!overwrite) {
	    r = CYRUSDB_EXISTS;
	    goto done;
	} else {
	    /* just overwrite the existing record */
	    loc.record.type = REPLACE;
	    loc.record.deloffset = loc.record.offset;
	}
    }
    else {
	/* build a new record in-place */
	memset(&loc.record, 0, sizeof(struct skiprecord));
	loc.record.type = ADD;
	loc.record.key = key;
	loc.record.keylen = keylen;
	loc.record.level = randlvl(db->header.maxlevel);
	for (i = 0; i < loc.record.level; i++)
	    loc.record.offsets[i] = loc.forwardoffsets[i];
    }
    loc.record.val = data;
    loc.record.vallen = datalen;
    r = write_record(db, &loc.record, &tid->logend);
    if (r) goto done;

    /* update pointers after writing record so abort is guaranteed to
     * see which records need reverting */
    r = stitch_record(db, &loc);
    if (r) goto done;

    if (be_paranoid) {
	assert(myconsistent(db, tid, 1) == 0);
    }

 done:

    if (r) {
	myabort(db, tid);
    }

    if (!r && localtid) {
	/* commit the store, which releases the write lock */
	r = mycommit(db, tid);
    }

    return r;
}

static int create(struct db *db,
		  const char *key, size_t keylen,
		  const char *data, size_t datalen,
		  struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, 0);
}

static int store(struct db *db,
		 const char *key, size_t keylen,
		 const char *data, size_t datalen,
		 struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, 1);
}

static int mydelete(struct db *db,
	     const char *key, size_t keylen,
	     struct txn **tidptr, int force)
{
    struct skiploc loc;
    struct txn *tid;
    struct txn *localtid = NULL;
    int r;

    if (!db || !key || !keylen) return CYRUSDB_BADPARAM;

    /* not keeping the transaction, just create one local to
     * this function */
    if (!tidptr) {
	tidptr = &localtid;
    }

    /* make sure we're write locked and up to date */
    if ((r = lock_or_refresh(db, tidptr)) < 0) {
	return r;
    }

    tid = *tidptr; /* consistent naming is nice */

    if (be_paranoid) {
	assert(myconsistent(db, tid, 1) == 0);
    }

    r = find_loc(db, key, keylen, &loc);
    if (r) goto done;

    if (!loc.is_exactmatch) {
        /* nothing to do */
	if (!force)
	    r = CYRUSDB_NOTFOUND;
	goto done;
    }

    /* create the deletion record */
    r = write_delete(db, loc.record.offset, &tid->logend);
    if (r) goto done;

    r = unstitch_record(db, &loc);
    if (r) goto done;

    if (be_paranoid) {
	assert(myconsistent(db, tid, 1) == 0);
    }

 done:

    if (r) {
	myabort(db, tid);
    }
    else if (localtid) {
	/* commit the store, which releases the write lock */
	r = mycommit(db, tid);
    }

    return r;
}

static int mycommit(struct db *db, struct txn *tid)
{
    int r = 0;

    if (!db) return CYRUSDB_BADPARAM;
    if (tid != db->current_txn) return CYRUSDB_LOCKED;

    update_lock(db, tid);

    if (be_paranoid) {
	assert(myconsistent(db, tid, 1) == 0);
    }

    /* verify that we did something this txn */
    if (tid->logstart == tid->logend) {
	/* empty txn, done */
	r = 0;
	goto done;
    }

    /* fsync to make sure all changes are on disk */
    if (db_fsync(db)) {
	syslog(LOG_ERR, "IOERROR: writing %s: %m", db->fname);
	r = CYRUSDB_IOERROR;
	goto done;
    }

    r = write_commit(db, tid->logend);
    if (r) goto done;

    /* fsync a second time to make the commit stick */
    if (db_fsync(db)) {
	syslog(LOG_ERR, "IOERROR: writing %s: %m", db->fname);
	r = CYRUSDB_IOERROR;
	goto done;
    }

    if (be_paranoid)
	assert(myconsistent(db, db->current_txn, 1) == 0);

 done:
    if (r) {
	int r2;

	/* error during commit; we must abort */
	r2 = myabort(db, tid);
	if (r2) {
	    syslog(LOG_ERR, "DBERROR: skiplist2 %s: commit AND abort failed",
		   db->fname);
	}
    } else {
	db->current_txn = NULL;

	/* consider checkpointing */
	if (tid->logend > (2 * db->header.logstart + MINREWRITE))
	    r = mycheckpoint(db);
	else
	    r = unlock(db);

	/* free tid */
	free(tid);
    }

    return r;
}

static int myabort(struct db *db, struct txn *tid)
{
    struct skiprecord record;
    struct skiploc loc;
    uint8_t type;
    uint64_t offset;
    int r = 0;

    if (!db) return CYRUSDB_BADPARAM;
    if (tid != db->current_txn) return CYRUSDB_LOCKED;

    /* update the mmap so we can see the log entries we need to remove */
    update_lock(db, tid);

    /* look at the log entries we've written, and undo their effects */
    while (tid->logstart < tid->logend) {
	offset = tid->logstart;
	/* walk forward to the FINAL log record each time, so we undo
	 * in reverse order to creation */
	while (offset < tid->logend) {
	    r = read_record(db, offset, &record);
	    if (r) goto done;
	    offset += record.len;
	}

	type = record.type;

	/* if it's a delete, find the source record to stitch back in */
	if (type == DELETE) {
	    r = read_record(db, record.deloffset, &record);
	    if (r) goto done;
	}

	/* find the location of this record */
	r = find_loc(db, record.key, record.keylen, &loc);
	if (r) goto done;

	switch (type) {
	case DUMMY:
	case COMMIT:
	    abort();

	case ADD:
	case ZADD:
	    /* must exist and be this record */
	    if (!loc.is_exactmatch || record.offset != loc.record.offset) {
		r = CYRUSDB_NOTFOUND;
		goto done;
	    }

	    /* remove this record */
	    r = unstitch_record(db, &loc);
	    if (r) goto done;

	    break;

	case DELETE:
	    if (loc.is_exactmatch) {
		r = CYRUSDB_EXISTS;
		goto done;
	    }

	    /* copy the original record in for stitching */
	    loc.record = record;

	    /* add this record back */
	    r = stitch_record(db, &loc);
	    if (r) goto done;

	    break;

	case REPLACE:
	case ZREPLACE:
	    /* must exist and be this record */
	    if (!loc.is_exactmatch || record.offset != loc.record.offset) {
		r = CYRUSDB_NOTFOUND;
		goto done;
	    }

	    /* NOTE: because we're undoing in the same order that we "did",
	     * we know that the forward pointers at deloffset will be correct,
	     * so we don't need to copy them back */

	    /* point to the earlier version */
	    loc.record.offset = record.offset;

	    /* stitch the old copy of the record back into place */
	    r = stitch_record(db, &loc);
	    if (r) goto done;

	    break;
	}

	/* remove this record from the end of the known transaction */
	tid->logend -= record.len;
    }

done:
    /* truncate the file to remove log entries */
    if (ftruncate(db->fd, tid->logstart) < 0) {
	syslog(LOG_ERR,
	       "DBERROR: skiplist2 abort %s: ftruncate: %m",
	       db->fname);
	r = CYRUSDB_IOERROR;
	unlock(db);
	return r;
    }

    db->map_size = tid->logstart;

    /* free the tid */
    free(tid);
    db->current_txn = NULL;

    /* ok, we've truncated, but we didn't actually clean up,
     * so force recovery too */
    if (r) {
	syslog(LOG_ERR, "DBERROR: abort error, running recovery %s", db->fname);
	r = recovery(db, RECOVERY_FORCE);
    }
    else {
	r = unlock(db);
    }

    return r;
}

/* compress 'db', closing at the end */
static int mycheckpoint(struct db *db)
{
    char fname[1024];
    time_t start = time(NULL);
    struct skiploc loc;
    struct db newdb;
    struct skiploc newloc;
    int r = 0;
    int i;

    /* we need the latest and greatest data */
    assert(db->is_open && db->lock_status == WRITELOCKED);

    /* can't be in a transaction */
    assert(db->current_txn == NULL);

    r = myconsistent(db, NULL, 1);
    if (r < 0) {
	syslog(LOG_ERR, "db %s, inconsistent pre-checkpoint, bailing out",
	       db->fname);
	unlock(db);
	return r;
    }

    /* open fname.NEW */
    snprintf(fname, sizeof(fname), "%s.NEW", db->fname);
    unlink(fname);

    newdb = *db;
    newdb.fd = open(fname, O_RDWR | O_CREAT, 0644);
    if (newdb.fd < 0) {
	syslog(LOG_ERR, "DBERROR: skiplist2 checkpoint: open(%s): %m", fname);
	goto err;
    }

    /* truncate it just in case! */
    if (ftruncate(newdb.fd, 0) < 0) {
	syslog(LOG_ERR, "DBERROR: skiplist2 checkpoint %s: ftruncate %m", fname);
	goto err;
    }

    /* prepare the new file for mmap updates */
    newdb.fname = fname;
    newdb.map_base = 0;
    newdb.map_size = 0;
    newdb.map_len = 0;
    newdb.map_ino = 0;

    newdb.header.logstart = db->header_size;

    memset(&newloc, 0, sizeof(struct skiploc));

    /* make a dummy record */
    newloc.record.type = DUMMY;
    newloc.record.level = db->header.maxlevel;
    r = write_record(&newdb, &newloc.record, &newdb.header.logstart);
    if (r) goto err;

    /* backpointers all point to the dummy */
    for (i = 0; i < newloc.record.level; i++)
	newloc.backoffsets[i] = db->header_size;

    newdb.header.num_records = 0;

    /* find the first record */
    r = find_loc(db, NULL, 0, &loc);
    if (r) goto err;

    /* set it as 'exactmatch' */
    r = advance_loc(db, &loc);
    if (r) goto err;

    /* this is amenable to the same optimisation mentioned in
     * recovery for the initial in-order items commit, for the
     * same reason */
    while (loc.record.type != DUMMY) {
	newdb.header.num_records++;

	/* all records are new adds in a repack */
	memset(&newloc.record, 0, sizeof(struct skiprecord));
	if (loc.record.type == ZADD || loc.record.type == ZREPLACE)
	    newloc.record.type = ZADD;
	else
	    newloc.record.type = ADD;
	newloc.record.level = loc.record.level;
	newloc.record.key = loc.record.key;
	newloc.record.keylen = loc.record.keylen;
	newloc.record.val = loc.record.val;
	newloc.record.vallen = loc.record.vallen;

	/* write the record to the new DB */
	r = write_record(&newdb, &newloc.record, &newdb.header.logstart);
	if (r) goto err;

	/* stitch this shiny new "ADD" into place */
	r = stitch_record(&newdb, &newloc);
	if (r) goto err;

	/* update the backpointers to point to the new record */
	r = advance_loc(&newdb, &newloc);
	if (r) goto err;

	/* and get the next record from the source DB */
	r = advance_loc(db, &loc);
	if (r) goto err;
    }

    newdb.header.last_recovery = time(NULL);
    r = write_header(&newdb);
    if (r) goto err;

    r = write_commit(&newdb, newdb.header.logstart);
    if (r) goto err;

    /* sync new file */
    if (db_fsync(&newdb)) {
	syslog(LOG_ERR, "DBERROR: skiplist2 checkpoint: fdatasync(%s): %m", fname);
	goto err;
    }

    if ((r = myconsistent(&newdb, NULL, 1)) < 0) {
	syslog(LOG_ERR, "db %s, inconsistent post-checkpoint, bailing out",
	       db->fname);
	return r;
    }

    /* move new file to original file name */
    if ((rename(newdb.fname, db->fname) < 0)) {
	syslog(LOG_ERR, "DBERROR: skiplist checkpoint: rename(%s, %s): %m", 
	       newdb.fname, db->fname);
	goto err;
    }

    /* OK, we're commmitted now */
    /* remove content of old file so it doesn't sit around using disk */
    map_free(&db->map_base, &db->map_len);
    ftruncate(db->fd, 0);
    /* lose the lock  - by now other users may already be doing stuff to the
     * new file! */
    close(db->fd);

    /* copy the new DB details back */
    newdb.lock_status = UNLOCKED;
    newdb.fname = db->fname;
    *db = newdb;

    /* force the new file name to disk */
    if (fsync(db->fd) < 0) {
	syslog(LOG_ERR, "DBERROR: skiplist checkpoint: fsync(%s): %m", db->fname);
	return CYRUSDB_IOERROR;
    }

    {
	int diff = time(NULL) - start;
	syslog(LOG_INFO, 
	       "skiplist: checkpointed %s (%d record%s, %llu bytes) in %d second%s",
	       db->fname, db->header.num_records, db->header.num_records == 1 ? "" : "s", 
	       (LLU)(db->header.logstart+8), diff, diff == 1 ? "" : "s"); 
    }

    return 0;

 err:
    map_free(&newdb.map_base, &newdb.map_len);
    if (newdb.fd != -1) close(newdb.fd);
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
    uint64_t offset = db->header_size;
    struct skiprecord record;
    int i;
    int r;

    while (offset < db->map_size) {
	printf("%08llX ", (LLU)offset);

	r = read_record(db, offset, &record);
	if (r) {
	    printf("ERROR\n");
	    break;
	}

	switch (record.type) {
	case DUMMY:
	    printf("DUMMY ");
	    break;
	case ADD:
	    printf("ADD ");
	    break;
	case ZADD:
	    printf("ZADD ");
	    break;
	case DELETE:
	    printf("DELETE ");
	    break;
	case REPLACE:
	    printf("REPLACE ");
	    break;
	case ZREPLACE:
	    printf("ZREPLACE ");
	    break;
	case COMMIT:
	    printf("COMMIT ");
	    break;
	}

	switch (record.type) {
	case REPLACE:
	case ZREPLACE:
	    printf("del=%08llX ", (LLU)record.deloffset);
	    /* fallthrough */
	case DUMMY:
	case ADD:
	case ZADD:
	    printf("kl=%llu dl=%llu lvl=%d\n",
		   (LLU)record.keylen, (LLU)record.vallen, record.level);
	    printf("\t");
	    for (i = 0; i < record.level; i++)
		printf("%08llX ", (LLU)record.offsets[i]);
	    printf("\n");
	    break;

	case DELETE:
	    printf("del=%08llX\n", (LLU)record.deloffset);
	    break;

	case COMMIT:
	    printf("\n");
	    break;
	}

	offset += record.len;
    }

    return 0;
}

static int consistent(struct db *db)
{
    return myconsistent(db, NULL, 0);
}

/* perform some basic consistency checks */
static int myconsistent(struct db *db, struct txn *tid, int locked)
{
    struct skiploc loc;
    struct skiprecord record;
    int cmp;
    int r = 0;
    int i;

    assert(db->current_txn == tid); /* could both be null */

    if (!locked) read_lock(db);
    else if (tid) update_lock(db, tid);

    r = find_loc(db, NULL, 0, &loc);
    if (r) goto done;

    while (loc.record.type != DUMMY) {
	for (i = 0; i < loc.record.level; i++) {
	    if (!loc.record.offsets[i])
		continue; /* already the last one, could use "break"
			   * if we didn't already not trust the pointers */

	    r = read_record(db, loc.record.offsets[i], &record);
	    if (r) goto done;

	    cmp = db->compar(record.key, record.keylen,
			     loc.record.key, loc.record.keylen);
	    if (cmp <= 0) {
		syslog(LOG_ERR, "DBERROR: skiplist2 out of order %s: %.*s (%08llX) <= %.*s (%08llX)",
		       db->fname, (int)record.keylen, record.key, (LLU)record.offset,
		       (int)loc.record.keylen, loc.record.key, (LLU)loc.record.offset);
		r = CYRUSDB_INTERNAL;
		goto done;
	    }
	}

	r = advance_loc(db, &loc);
	if (r) goto done;
    }

done:
    if (!locked) unlock(db);

    return r;
}

/* run recovery on this file.  Always unlocks at the end,
 * always called with a write lock. */
static int recovery(struct db *db, int flags)
{
    struct skiprecord commitrecord;
    struct skiprecord record;
    time_t start = time(NULL);
    struct skiploc loc;
    uint64_t offset;
    int r = 0;
    int i;

    assert(db->is_open && db->lock_status == WRITELOCKED);
    /* can't run recovery inside a txn */
    assert(db->current_txn == NULL);

    if (!(flags & RECOVERY_FORCE)
	&& global_recovery
	&& db->header.last_recovery >= global_recovery) {
	/* someone beat us to it */
	goto done;
    }

    /* restart the counter */
    db->header.num_records = 0;

    r = read_record(db, db->header_size, &record);
    /* initialise the dummy pointers  */
    for (i = 0; i < record.level; i++)
	record.offsets[i] = 0;
    r = rewrite_record(db, &record);
    if (r) goto done;

    /* check for the first commit - we know those records
     * are in order and are all ADDs, so we'll be efficient */
    if (db->header.version == 1) {
	/* special case magic for v1, invisible zero-length commit record */
	commitrecord.offset = db->header.logstart;
	commitrecord.len = 0;
    }
    else {
	r = read_record(db, db->header.logstart, &commitrecord);
	if (r) goto done;
	assert(commitrecord.type == COMMIT);
    }

    /* prepare the backreferences */
    memset(&loc, 0, sizeof(struct skiploc));
    for (i = 0; i < db->header.maxlevel; i++)
	loc.backoffsets[i] = db->header_size;

    /* NOTE: some performance gain available here by caching
     * MAXLEVEL worth of old records to update, and not writing
     * them until we meet another record of equivalent level
     * - the saving is record->level worth of rewrites */

    offset = record.offset + record.len;

    while (offset < commitrecord.offset) {
	r = read_record(db, offset, &record);
	if (r) goto done;

	/* zero out forward pointers and rewrite */
	for (i = 0; i < record.level; i++)
	    record.offsets[i] = 0;
	r = rewrite_record(db, &record);
	if (r) goto done;

	/* move forwards */
	offset += record.len;

	/* stitch record in at this location */
	loc.record = record;
	r = stitch_record(db, &loc);
	if (r) goto done;

	/* and bring the backpointers up to this commit */
	r = advance_loc(db, &loc);
	if (r) goto done;
    }

    /* now we do the 'find a commit and apply the stuff up to it'
     * dance */

    offset = commitrecord.offset + commitrecord.len;
    while (offset < db->map_size) {
	uint64_t nextoffset = offset;
	int foundone = 0;
	while (nextoffset < db->map_size) {
	    r = read_record(db, nextoffset, &commitrecord);
	    if (r) goto done;
	    if (commitrecord.type == COMMIT) {
		foundone = 1;
		break;
	    }
	    nextoffset += commitrecord.len;
	}
	if (!foundone) {
	    /* there's uncommitted rubbish on the end of the file */
	    ftruncate(db->fd, offset);
	    /* XXX - warn, and all that jazz */
	    goto done;
	}

	while (offset < nextoffset) {
	    uint8_t type;

	    r = read_record(db, offset, &record);
	    if (r) goto done;

	    type = record.type;
	    offset += record.len;

	    /* delete, find the original */
	    if (type == DELETE) {
		r = read_record(db, record.deloffset, &record);
		if (r) goto done;
	    }

	    /* now locate the current version of this record */
	    r = find_loc(db, record.key, record.keylen, &loc);
	    if (r) goto done;

	    switch (type) {
	    /* it can only be one of these */
	    case ADD:
	    case ZADD:
		if (loc.is_exactmatch) {
		    r = CYRUSDB_EXISTS;
		    goto done;
		}

		/* update the forward pointers */
		for (i = 0; i < record.level; i++)
		    record.offsets[i] = loc.forwardoffsets[i];
		r = rewrite_record(db, &record);
		if (r) goto done;

		/* and stictch in the backwards pointers */
		loc.record = record;
		r = stitch_record(db, &loc);
		if (r) goto done;

		break;

	    case REPLACE:
	    case ZREPLACE:
		if (!loc.is_exactmatch ||
		     loc.record.offset != record.deloffset) {
		    r = CYRUSDB_NOTFOUND;
		    goto done;
		}

		/* update the forward pointers */
		for (i = 0; i < record.level; i++)
		    record.offsets[i] = loc.record.offsets[i];
		r = rewrite_record(db, &record);
		if (r) goto done;

		/* and stitch in the backwards pointers */
		loc.record = record;
		r = stitch_record(db, &loc);
		if (r) goto done;

		break;

	    case DELETE:
		if (!loc.is_exactmatch ||
		     loc.record.offset != record.offset) {
		    r = CYRUSDB_NOTFOUND;
		    goto done;
		}

		/* unstitch the record */
		r = unstitch_record(db, &loc);
		if (r) goto done;

		break;
	    }
	}
	offset = commitrecord.offset + commitrecord.len;
    }

    /* if we're checkpointing now, do it before fsyncing, since
     * we're about to throw away this data anyway */
    if (libcyrus_config_getswitch(CYRUSOPT_SKIPLIST_ALWAYS_CHECKPOINT))
	return mycheckpoint(db);

    /* fsync the recovered database */
    if (db_fsync(db)) {
	syslog(LOG_ERR,
	       "DBERROR: skiplist recovery %s: fdatasync: %m", db->fname); 
	r = CYRUSDB_IOERROR;
	if (r) goto done;
    }

    /* set the last recovery timestamp */
    db->header.last_recovery = time(NULL);
    r = write_header(db);
    if (r) goto done;

    /* fsync the new header */
    if (db_fsync(db)) {
	syslog(LOG_ERR,
	       "DBERROR: skiplist recovery %s: fdatasync: %m", db->fname); 
	r = CYRUSDB_IOERROR;
	if (r) goto done;
    }

    {
	int diff = time(NULL) - start;

	syslog(LOG_NOTICE, 
	       "skiplist: recovered %s (%d record%s, %llu bytes) in %d second%s",
	       db->fname, db->header.num_records, db->header.num_records == 1 ? "" : "s", 
	       (LLU)db->map_size, diff, diff == 1 ? "" : "s"); 
    }

 done:
    unlock(db);
    return r;
}

static int myopenz(const char *fname, int flags, struct db **ret)
{
    return myopen(fname, flags | CYRUSDB_ZLIB, ret, 2);
}

static int myopenv2(const char *fname, int flags, struct db **ret)
{
    return myopen(fname, flags, ret, 2);
}

static int myopenv1(const char *fname, int flags, struct db **ret)
{
    return myopen(fname, flags, ret, 1);
}

struct cyrusdb_backend cyrusdb_skiplist2 =
{
    "skiplist2",			/* name */

    &myinit,
    &mydone,
    &mysync,
    &myarchive,

    &myopenv2,
    &myclose,

    &fetch,
    &fetchlock,
    &fetchnext,

    &myforeach,
    &create,
    &store,
    &mydelete,

    &mycommit,
    &myabort,

    &dump,
    &consistent
};

struct cyrusdb_backend cyrusdb_skiplist2z =
{
    "skiplist2z",			/* name */

    &myinit,
    &mydone,
    &mysync,
    &myarchive,

    &myopenz,
    &myclose,

    &fetch,
    &fetchlock,
    &fetchnext,

    &myforeach,
    &create,
    &store,
    &mydelete,

    &mycommit,
    &myabort,

    &dump,
    &consistent
};

struct cyrusdb_backend cyrusdb_skiplist1 =
{
    "skiplist1",			/* name */

    &myinit,
    &mydone,
    &mysync,
    &myarchive,

    &myopenv1,
    &myclose,

    &fetch,
    &fetchlock,
    &fetchnext,

    &myforeach,
    &create,
    &store,
    &mydelete,

    &mycommit,
    &myabort,

    &dump,
    &consistent
};
