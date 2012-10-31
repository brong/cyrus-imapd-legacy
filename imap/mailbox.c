/* mailbox.c -- Mailbox manipulation routines
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
 * $Id: mailbox.c,v 1.201 2010/06/28 12:04:20 brong Exp $
 */
#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <ctype.h>
#include <errno.h>
#ifdef HAVE_INTTYPES_H
# include <inttypes.h>
#elif defined(HAVE_STDINT_H)
# include <stdint.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <utime.h>

#ifdef HAVE_DIRENT_H
# include <dirent.h>
# define NAMLEN(dirent) strlen((dirent)->d_name)
#else
# define dirent direct
# define NAMLEN(dirent) (dirent)->d_namlen
# if HAVE_SYS_NDIR_H
#  include <sys/ndir.h>
# endif
# if HAVE_SYS_DIR_H
#  include <sys/dir.h>
# endif
# if HAVE_NDIR_H
#  include <ndir.h>
# endif
#endif

#ifdef HAVE_LIBUUID
#include <uuid/uuid.h>
#endif

#include "acl.h"
#include "annotate.h"
#include "assert.h"
#include "crc32.h"
#include "md5.h"
#include "exitcodes.h"
#include "global.h"
#include "imap/imap_err.h"
#include "imparse.h"
#include "cyr_lock.h"
#include "mailbox.h"
#include "message.h"
#include "map.h"
#include "mboxlist.h"
#include "parseaddr.h"
#include "proc.h"
#include "retry.h"
#include "seen.h"
#include "upgrade_index.h"
#include "util.h"
#include "sequence.h"
#include "statuscache.h"
#include "strarray.h"
#include "sync_log.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "xstats.h"

#include "mailbox_update_notifier.h"

struct mailboxlist {
    struct mailboxlist *next;
    struct mailbox m;
    struct mboxlock *l;
    int nopen;
};

static struct mailboxlist *open_mailboxes = NULL;

#define zeromailbox(m) { memset(&m, 0, sizeof(struct mailbox)); \
                         (m).index_fd = -1; \
                         (m).cache_fd = -1; \
                         (m).header_fd = -1; }

static int mailbox_index_unlink(struct mailbox *mailbox);
static int mailbox_index_repack(struct mailbox *mailbox);
static int mailbox_lock_index_internal(struct mailbox *mailbox,
				       int locktype);

static struct mailboxlist *create_listitem(const char *name)
{
    struct mailboxlist *item = xmalloc(sizeof(struct mailboxlist));
    item->next = open_mailboxes;
    open_mailboxes = item;

    item->nopen = 1;
    item->l = NULL;
    zeromailbox(item->m);
    item->m.name = xstrdup(name);
    /* ensure we never print insane times */
    gettimeofday(&item->m.starttime, 0);

    return item;
}

static struct mailboxlist *find_listitem(const char *name)
{
    struct mailboxlist *item;

    for (item = open_mailboxes; item; item = item->next) {
	if (!strcmp(name, item->m.name))
	    return item;
    }

    return NULL;
}

static void remove_listitem(struct mailboxlist *remitem)
{
    struct mailboxlist *item;
    struct mailboxlist *previtem = NULL;

    for (item = open_mailboxes; item; item = item->next) {
	if (item == remitem) {
	    if (previtem)
		previtem->next = item->next;
	    else
		open_mailboxes = item->next;
	    free(item);
	    return;
	}
	previtem = item;
    }

    fatal("didn't find item in list", EC_SOFTWARE);
}

EXPORTED char *mailbox_meta_fname(struct mailbox *mailbox, int metafile)
{
    static char fnamebuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_metapath(mailbox->part, mailbox->name, metafile, 0);
    if (!src) return NULL;

    strncpy(fnamebuf, src, MAX_MAILBOX_PATH);
    return fnamebuf;
}

EXPORTED char *mailbox_meta_newfname(struct mailbox *mailbox, int metafile)
{
    static char fnamebuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_metapath(mailbox->part, mailbox->name, metafile, 1);
    if (!src) return NULL;

    strncpy(fnamebuf, src, MAX_MAILBOX_PATH);
    return fnamebuf;
}

EXPORTED int mailbox_meta_rename(struct mailbox *mailbox, int metafile)
{
    char *fname = mailbox_meta_fname(mailbox, metafile);
    char *newfname = mailbox_meta_newfname(mailbox, metafile);

    if (rename(newfname, fname))
	return IMAP_IOERROR;

    return 0;
}

EXPORTED char *mailbox_message_fname(struct mailbox *mailbox, unsigned long uid)
{
    static char localbuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_datapath(mailbox->part, mailbox->name, uid);
    if (!src) return NULL;

    strncpy(localbuf, src, MAX_MAILBOX_PATH);
    return localbuf;
}

EXPORTED char *mailbox_datapath(struct mailbox *mailbox)
{
    static char localbuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_datapath(mailbox->part, mailbox->name, 0);
    if (!src) return NULL;

    strncpy(localbuf, src, MAX_MAILBOX_PATH);
    return localbuf;
}

/*
 * Names of the headers we cache in the cyrus.cache file.
 *
 * Changes to this list probably require bumping the cache version
 * number (obviously)
 *
 * note that header names longer than MAX_CACHED_HEADER_SIZE
 * won't be cached regardless
 *
 * xxx can we get benefits by requireing this list to be sorted?
 * (see is_cached_header())
 *
 */
const struct mailbox_header_cache mailbox_cache_headers[] = {
    /* things we have always cached */
    { "priority", 0 },
    { "references", 0 },
    { "resent-from", 0 },
    { "newsgroups", 0 },
    { "followup-to", 0 },

    /* x headers that we may want to cache anyway */
    { "x-mailer", 1 },
    { "x-trace", 1 },

    /* outlook express seems to want these */
    { "x-ref", 2  },
    { "x-priority", 2 },
    { "x-msmail-priority", 2 },
    { "x-msoesrec", 2 },

    /* for efficient FastMail interface display */
    { "x-spam-score", 3 },
    { "x-spam-hits", 3 },
    { "x-spam-source", 3 },
    { "x-resolved-to", 3 },
    { "x-delivered-to", 3 },
    { "x-mail-from", 3 },
    { "x-truedomain", 3 },
    { "x-truedomain-dkim", 3 },
    { "x-truedomain-spf", 3 },
    { "x-truedomain-domain", 3 },

    /* for conversations */
    { "x-me-message-id", 4 },

    /* things to never cache */
    { "bcc", BIT32_MAX },
    { "cc", BIT32_MAX },
    { "date", BIT32_MAX },
    { "delivery-date", BIT32_MAX },
    { "envelope-to", BIT32_MAX },
    { "from", BIT32_MAX },
    { "in-reply-to", BIT32_MAX },
    { "mime-version", BIT32_MAX },
    { "reply-to", BIT32_MAX },
    { "received", BIT32_MAX },
    { "return-path", BIT32_MAX },
    { "sender", BIT32_MAX },
    { "subject", BIT32_MAX },
    { "to", BIT32_MAX },

    /* signatures tend to be large, and are useless without the body */
    { "dkim-signature", BIT32_MAX },
    { "domainkey-signature", BIT32_MAX },
    { "domainkey-x509", BIT32_MAX },

    /* older versions of PINE (before 4.56) need message-id in the cache too
     * though technically it is a waste of space because it is in
     * ENVELOPE.  We should probably uncomment the following at some
     * future point [ken3 notes this may also be useful to have here for
     * threading so we can avoid parsing the envelope] */
    /* { "message-id", BIT32_MAX }, */
};
const int MAILBOX_NUM_CACHE_HEADERS =
  sizeof(mailbox_cache_headers)/sizeof(struct mailbox_header_cache);

/*
 *  Function to test if a header is in the cache
 *
 *  Assume cache entry version 1, unless other data is found
 *  in the table.
 */
static inline unsigned is_cached_header(const char *hdr)
{
    int i;

    /* xxx if we can sort the header list we can do better here */
    for (i=0; i<MAILBOX_NUM_CACHE_HEADERS; i++) {
	if (!strcmp(mailbox_cache_headers[i].name, hdr))
	    return mailbox_cache_headers[i].min_cache_version;
    }

    /* Don't Cache X- headers unless explicitly configured to*/
    if ((hdr[0] == 'x') && (hdr[1] == '-')) return BIT32_MAX;

    /* Everything else we cache in version 1 */
    return 1;
}

/*  External API to is_cached_header that prepares the string
 *
 *   Returns minimum version required for lookup to succeed
 *   or BIT32_MAX if header not cached
 */
EXPORTED unsigned mailbox_cached_header(const char *s)
{
    char hdr[MAX_CACHED_HEADER_SIZE];
    int i;

    /* Generate lower case copy of string */
    /* xxx sometimes the caller has already generated this .. 
     * maybe we can just require callers to do it? */
    for (i=0 ; *s && (i < (MAX_CACHED_HEADER_SIZE - 1)) ; i++)
	hdr[i] = tolower(*s++);

    if (*s) return BIT32_MAX;   /* Input too long for match */
    hdr[i] = '\0';

    return is_cached_header(hdr);
}

/* Same as mailbox_cached_header, but for use on a header
 * as it appears in the message (i.e. :-terminated, not NUL-terminated)
 */
HIDDEN unsigned mailbox_cached_header_inline(const char *text)
{
    char buf[MAX_CACHED_HEADER_SIZE];
    int i;

    /* Scan for header */
    for (i=0; i < (MAX_CACHED_HEADER_SIZE - 1); i++) {
	if (!text[i] || text[i] == '\r' || text[i] == '\n') break;
	
	if (text[i] == ':') {
	    buf[i] = '\0';
	    return is_cached_header(buf);
	} else {
	    buf[i] = tolower(text[i]);
	}
    }

    return BIT32_MAX;
}

const char *cache_base(struct index_record *record)
{
    const char *base = record->crec.base->s;
    return base + record->crec.offset;
}

unsigned cache_size(struct index_record *record)
{
    return record->crec.len;
}

struct buf *cache_buf(struct index_record *record)
{
    static struct buf staticbuf;

    buf_init_ro(&staticbuf,
		cache_base(record),
		cache_size(record));

    return &staticbuf;
}

EXPORTED const char *cacheitem_base(struct index_record *record, int field)
{
    const char *base = record->crec.base->s;
    return base + record->crec.item[field].offset;
}

EXPORTED unsigned cacheitem_size(struct index_record *record, int field)
{
    return record->crec.item[field].len;
}

EXPORTED struct buf *cacheitem_buf(struct index_record *record, int field)
{
    static struct buf staticbuf;

    buf_init_ro(&staticbuf,
		cacheitem_base(record, field),
		cacheitem_size(record, field));

    return &staticbuf;
}


/* parse a single cache record from the mapped file - creates buf
 * records which point into the map, so you can't free it while
 * you still have them around! */
int cache_parserecord(struct buf *cachebase, unsigned cache_offset,
		      struct cacherecord *crec)
{
    unsigned cache_ent;
    unsigned offset;
    const char *cacheitem, *next;

    offset = cache_offset;

    if (offset >= cachebase->len) {
	syslog(LOG_ERR, "IOERROR: offset greater than cache size %u %u",
	       offset, cachebase->len);
	return IMAP_IOERROR;
    }

    for (cache_ent = 0; cache_ent < NUM_CACHE_FIELDS; cache_ent++) {
	cacheitem = cachebase->s + offset;
	/* copy locations */
	crec->item[cache_ent].len = CACHE_ITEM_LEN(cacheitem);
	crec->item[cache_ent].offset = offset + CACHE_ITEM_SIZE_SKIP;

	/* moving on */
	next = CACHE_ITEM_NEXT(cacheitem);
	if (next < cacheitem) {
	    syslog(LOG_ERR, "IOERROR: cache offset negative");
	    return IMAP_IOERROR;
	}

	offset = next - cachebase->s;
	if (offset > cachebase->len) {
	    syslog(LOG_ERR, "IOERROR: offset greater than cache size %u %u (%d)",
		   offset, cachebase->len, cache_ent);
	    return IMAP_IOERROR;
	}
    }

    /* all fit within the cache, it's gold as far as we can tell */
    crec->base = cachebase;
    crec->len = offset - cache_offset;
    crec->offset = cache_offset;

    return 0;
}

HIDDEN int mailbox_ensure_cache(struct mailbox *mailbox, unsigned offset)
{
    struct stat sbuf;
    unsigned generation;
    int retry = 0;
    int openflags = mailbox->is_readonly ? O_RDONLY : O_RDWR;

 retry:
    /* open the file */
    if (mailbox->cache_fd == -1) {
	char *fname;

	/* it's bogus to be dirty here */
	if (mailbox->cache_dirty)
	    abort();

	fname = mailbox_meta_fname(mailbox, META_CACHE);
	mailbox->cache_fd = open(fname, openflags, 0);
	if (mailbox->cache_fd == -1)
	    goto fail;

	if (mailbox->cache_buf.s)
	    map_free((const char **)&mailbox->cache_buf.s, &mailbox->cache_len);
	mailbox->cache_buf.len = 0;
    }

    if (offset >= mailbox->cache_buf.len) {
	/* get the size and inode */
	if (fstat(mailbox->cache_fd, &sbuf) == -1) {
	    syslog(LOG_ERR, "IOERROR: fstating cache %s: %m", mailbox->name);
	    goto fail;
	}
	mailbox->cache_buf.len = sbuf.st_size;
	if (mailbox->cache_buf.len < 4)
	    goto fail;

	map_refresh(mailbox->cache_fd, 0, (const char **)&mailbox->cache_buf.s,
		    &mailbox->cache_len, mailbox->cache_buf.len, "cache",
		    mailbox->name);

	generation = ntohl(*((bit32 *)(mailbox->cache_buf.s)));
	if (generation < mailbox->i.generation_no && !retry) {
	    /* try a rename - maybe we got killed between renames in repack */
	    map_free((const char **)&mailbox->cache_buf.s, &mailbox->cache_len);
	    close(mailbox->cache_fd);
	    mailbox->cache_fd = -1;
	    syslog(LOG_NOTICE, "WARNING: trying to rename cache file %s (%d < %d)",
		   mailbox->name, generation, mailbox->i.generation_no);
	    mailbox_meta_rename(mailbox, META_CACHE);
	    retry = 1;
	    goto retry;
	}
	if (generation != mailbox->i.generation_no) {
	    map_free((const char **)&mailbox->cache_buf.s, &mailbox->cache_len);
	    goto fail;
	}
    }

    return 0;

fail:
    /* rebuild the cache from scratch! */
    syslog(LOG_ERR, "IOERROR: %s failed to open cache - rebuilding",
	   mailbox->name);

    {
	struct index_record record;
	const char *fname;
	uint32_t recno;
	uint32_t offset;
	uint32_t gen;

	/* make sure we have a file */
	if (mailbox->cache_fd == -1) {
	    fname = mailbox_meta_fname(mailbox, META_CACHE);
	    mailbox->cache_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
	}

	/* update the generation number */
	gen = htonl(mailbox->i.generation_no);
	retry_write(mailbox->cache_fd, (char *)&gen, 4);

	for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	    if (mailbox_read_index_record(mailbox, recno, &record))
		continue;
	    if (record.system_flags & FLAG_UNLINKED)
		continue;
	    fname = mailbox_message_fname(mailbox, record.uid);
	    offset = record.cache_offset; /* gets overwritten by parse */
	    if (message_parse(fname, &record))
		continue;
	    lseek(mailbox->cache_fd, offset, SEEK_SET);
	    retry_write(mailbox->cache_fd, cache_base(&record),
			cache_size(&record));
	}
	(void)fsync(mailbox->cache_fd);

	/* get the size and inode */
	fstat(mailbox->cache_fd, &sbuf);
	mailbox->cache_buf.len = sbuf.st_size;

	map_refresh(mailbox->cache_fd, 0, (const char **)&mailbox->cache_buf.s,
		    &mailbox->cache_len, mailbox->cache_buf.len, "cache",
		    mailbox->name);
    }

    return 0;
}

static int mailbox_index_islocked(struct mailbox *mailbox, int write)
{
    if (mailbox->index_locktype == LOCK_EXCLUSIVE) return 1;
    if (mailbox->index_locktype == LOCK_SHARED && !write) return 1;
    return 0;
}

/* return the offset for the start of the record! */
int mailbox_append_cache(struct mailbox *mailbox,
			 struct index_record *record)
{
    int r;

    assert(mailbox_index_islocked(mailbox, 1));

    /* no cache content */
    if (!record->crec.len)
	return 0;

    /* already been written */
    if (record->cache_offset)
	return 0;

    /* ensure we have a cache fd */
    r = mailbox_ensure_cache(mailbox, 0);
    if (r) {
	syslog(LOG_ERR, "Failed to open cache to %s for %u",
		mailbox->name, record->uid);
	return r; /* unable to append */
    }

    r = cache_append_record(mailbox->cache_fd, record);
    if (r) {
	syslog(LOG_ERR, "Failed to append cache to %s for %u",
	       mailbox->name, record->uid);
	return r;
    }

    mailbox->cache_dirty = 1;

    /* and now read it straight back in to ensure we're always
     * fresh */
    r = mailbox_ensure_cache(mailbox, record->cache_offset);
    if (r) return r;

    /* try to parse the cache record */
    r = cache_parserecord(&mailbox->cache_buf,
			  record->cache_offset, &record->crec);
    if (r) return r;

    if (record->cache_crc != crc32_buf(cache_buf(record)))
	return IMAP_MAILBOX_CHECKSUM;

    return 0;
}

EXPORTED int mailbox_cacherecord(struct mailbox *mailbox,
			struct index_record *record)
{
    uint32_t crc;
    int r = 0;

    /* do we already have a record loaded? */
    if (record->crec.len)
	return 0;

    if (!record->cache_offset)
	r = IMAP_IOERROR;
    if (r) goto done;

    r = mailbox_ensure_cache(mailbox, record->cache_offset);
    if (r) goto done;

    /* try to parse the cache record */
    r = cache_parserecord(&mailbox->cache_buf,
			  record->cache_offset, &record->crec);

    if (r) goto done;
    crc = crc32_buf(cache_buf(record));
    if (crc != record->cache_crc)
	r = IMAP_MAILBOX_CHECKSUM;

done:
    if (r) 
	syslog(LOG_ERR, "IOERROR: invalid cache record for %s uid %u (%s)",
	       mailbox->name, record->uid, error_message(r));

    return r;
}

int cache_append_record(int fd, struct index_record *record)
{
    unsigned offset;
    unsigned size = cache_size(record);
    int n;

    /* no parsed cache present */
    if (!record->crec.len)
	return 0;

    /* cache offset already there - probably already been written */
    if (record->cache_offset)
	return 0;

    if (record->cache_crc != crc32_buf(cache_buf(record)))
	return IMAP_MAILBOX_CHECKSUM;

    offset = lseek(fd, 0L, SEEK_END);
    n = retry_write(fd, cache_base(record), size);
    if (n < 0) {
	syslog(LOG_ERR, "failed to append %u bytes to cache", size);
	return IMAP_IOERROR;
    }

    record->cache_offset = offset;

    return 0;
}

static int mailbox_commit_cache(struct mailbox *mailbox)
{
    if (!mailbox->cache_dirty)
	return 0;

    mailbox->cache_dirty = 0;

    /* not open! That's bad */
    if (mailbox->cache_fd == -1)
	abort(); 

    /* just fsync is all that's needed to commit */
    (void)fsync(mailbox->cache_fd);

    return 0;
}

/* function to be used for notification of mailbox changes/updates */
static mailbox_notifyproc_t *updatenotifier = NULL;

/*
 * Set the updatenotifier function
 */
HIDDEN void mailbox_set_updatenotifier(mailbox_notifyproc_t *notifyproc)
{
    updatenotifier = notifyproc;
}

/*
 * Get the updatenotifier function
 */
mailbox_notifyproc_t *mailbox_get_updatenotifier(void)
{
    return updatenotifier;
}

/*
 * Create the unique identifier for a mailbox named 'name' with
 * uidvalidity 'uidvalidity'.  We use Ted Ts'o's libuuid if available,
 * otherwise we fall back to the legacy Cyrus algorithm which uses the
 * mailbox name hashed to 32 bits followed by the uid, both converted to
 * hex.
 */

static void mailbox_make_uniqueid(struct mailbox *mailbox)
{
#ifdef HAVE_LIBUUID
    uuid_t uu;

    uuid_clear(uu);	/* Just In Case */
    uuid_generate(uu);
    free(mailbox->uniqueid);
    /* 36 bytes of uuid plus \0 */
    mailbox->uniqueid = xmalloc(37);
    /* Solaris has an older libuuid which has uuid_unparse() but not
     * uuid_unparse_lower(), so we post-process the result ourself. */
    uuid_unparse(uu, mailbox->uniqueid);
    lcase(mailbox->uniqueid);
#else
#define PRIME (2147484043UL)
    unsigned hash = 0;
    const char *name = mailbox->name;

    while (*name) {
	hash *= 251;
	hash += *name++;
	hash %= PRIME;
    }

    free(mailbox->uniqueid);
    mailbox->uniqueid = xmalloc(32);

    snprintf(mailbox->uniqueid, 32, "%08x%08x",
	     hash, mailbox->i.uidvalidity);
#endif /* !HAVE_LIBUUID */

    mailbox->header_dirty = 1;
}

/*
 * Maps in the content for the message with UID 'uid' in 'mailbox',
 * into a read-only struct buf.  Use buf_free() to free the data.
 */
EXPORTED int mailbox_map_message(struct mailbox *mailbox, unsigned long uid,
				 struct buf *data)
{
    int msgfd;
    char *fname;
    struct stat sbuf;
    const char *base = NULL;
    size_t len = 0;

    xstats_inc(MESSAGE_MAP);
    fname = mailbox_message_fname(mailbox, uid);

    msgfd = open(fname, O_RDONLY, 0666);
    if (msgfd == -1) return errno;

    if (fstat(msgfd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on %s: %m", fname);
	fatal("can't fstat message file", EC_OSFILE);
    }
    buf_free(data);
    map_refresh(msgfd, 1, &base, &len, sbuf.st_size, fname, mailbox->name);
    buf_init_mmap(data, base, len);
    close(msgfd);

    return 0;
}

static void mailbox_release_resources(struct mailbox *mailbox)
{
    if (mailbox->i.dirty || mailbox->cache_dirty)
	abort();

    /* just close the header */
    if (mailbox->header_fd != -1) {
	close(mailbox->header_fd);
	mailbox->header_fd = -1;
    }

    /* release and unmap index */
    if (mailbox->index_fd != -1) {
	close(mailbox->index_fd);
	mailbox->index_fd = -1;
    }
    if (mailbox->index_base)
	map_free(&mailbox->index_base, &mailbox->index_len);

    /* release and unmap cache */
    if (mailbox->cache_fd != -1) {
	close(mailbox->cache_fd);
	mailbox->cache_fd = -1;
    }
    if (mailbox->cache_buf.s)
	map_free((const char **)&mailbox->cache_buf.s, &mailbox->cache_len);
    mailbox->cache_buf.len = 0;
}

/*
 * Open the index file for 'mailbox'
 */
static int mailbox_open_index(struct mailbox *mailbox)
{
    struct stat sbuf;
    char *fname;
    int openflags = mailbox->is_readonly ? O_RDONLY : O_RDWR;

    mailbox_release_resources(mailbox);

    /* open and map the index file */
    fname = mailbox_meta_fname(mailbox, META_INDEX);
    if (!fname)
	return IMAP_MAILBOX_BADNAME;

    mailbox->index_fd = open(fname, openflags, 0);
    if (mailbox->index_fd == -1)
	return IMAP_IOERROR;

    /* don't open the cache yet, it will be loaded by lazy-loading
     * later */

    fstat(mailbox->index_fd, &sbuf);
    mailbox->index_ino = sbuf.st_ino;
    mailbox->index_mtime = sbuf.st_mtime;
    mailbox->index_size = sbuf.st_size;
    map_refresh(mailbox->index_fd, 0, &mailbox->index_base,
		&mailbox->index_len, mailbox->index_size,
		"index", mailbox->name);

    return 0;
}

static int mailbox_mboxlock_reopen(struct mailboxlist *listitem, int locktype)
{
    struct mailbox *mailbox = &listitem->m;
    int r;

    mailbox_release_resources(mailbox);

    mboxname_release(&listitem->l);
    r = mboxname_lock(mailbox->name, &listitem->l, locktype);
    if (r) return r;

    return r;
}

/*
 * Open and read the header of the mailbox with name 'name'
 * The structure pointed to by 'mailbox' is initialized.
 */
static int mailbox_open_advanced(const char *name,
				 int locktype,
				 int index_locktype,
				 struct mailbox **mailboxptr)
{
    struct mboxlist_entry *mbentry = NULL;
    struct mailboxlist *listitem;
    struct mailbox *mailbox = NULL;
    int r = 0;

    assert(*mailboxptr == NULL);

    listitem = find_listitem(name);

    /* already open?  just use this one */
    if (listitem) {
	/* can't reuse an exclusive locked mailbox */
	if (listitem->l->locktype == LOCK_EXCLUSIVE)
	    return IMAP_MAILBOX_LOCKED;
	if (locktype == LOCK_EXCLUSIVE)
	    return IMAP_MAILBOX_LOCKED;
	/* can't reuse an already locked index */
	if (listitem->m.index_locktype)
	    return IMAP_MAILBOX_LOCKED;   

	r = mailbox_lock_index(&listitem->m, index_locktype);
	if (r) return r;

	listitem->nopen++;
	mailbox = &listitem->m;

	goto done;
    }

    listitem = create_listitem(name);
    mailbox = &listitem->m;

    r = mboxname_lock(name, &listitem->l, locktype);
    if (r) {
	/* locked is not an error - just means we asked for NONBLOCKING */
	if (r != IMAP_MAILBOX_LOCKED)
	    syslog(LOG_ERR, "IOERROR: locking %s: %m", mailbox->name);
	goto done;
    }

    r = mboxlist_lookup(name, &mbentry, NULL);
    if (r) goto done;

    if (mbentry->mbtype & MBTYPE_MOVING) {
	mboxlist_entry_free(&mbentry);
	r = IMAP_MAILBOX_MOVED;
	goto done;
    }

    mailbox->part = xstrdup(mbentry->partition);

    /* Note that the header does have the ACL information, but it is only
     * a backup, and the mboxlist data is considered authoritative, so
     * we will just use what we were passed */
    mailbox->acl = xstrdup(mbentry->acl);
    mailbox->mbtype = mbentry->mbtype;

    mboxlist_entry_free(&mbentry);

    if (index_locktype == LOCK_SHARED)
	mailbox->is_readonly = 1;

    r = mailbox_open_index(mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: opening index %s: %s",
	       mailbox->name, error_message(r));
	goto done;
    }

    /* this will open, map and parse the header file */
    r = mailbox_lock_index_internal(mailbox, index_locktype);
    if (r) {
	syslog(LOG_ERR, "IOERROR: locking index %s: %s",
	       mailbox->name, error_message(r));
	goto done;
    }

    /* oops, a race, it got deleted meanwhile.  That's OK */
    if (mailbox->i.options & OPT_MAILBOX_DELETED) {
	r = IMAP_MAILBOX_NONEXISTENT;
	goto done;
    }

done:
    if (r) mailbox_close(&mailbox);
    else *mailboxptr = mailbox;

    return r;
}

EXPORTED int mailbox_open_irl(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_SHARED, LOCK_SHARED,
				 mailboxptr);
}

EXPORTED int mailbox_open_iwl(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_SHARED, LOCK_EXCLUSIVE,
				 mailboxptr);
}

EXPORTED int mailbox_open_irlnb(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name,
				 LOCK_SHARED|LOCK_NONBLOCK,
				 /* cannot do nonblocking lock on index...why? */
				 LOCK_SHARED,
				 mailboxptr);
}

struct mailbox *mailbox_findopen(const char *name)
{
    struct mailboxlist *listitem = find_listitem(name);

    if (listitem) {
	struct mailbox *mailbox = &listitem->m;
	/* we only want exclusive locked - otherwise fall back to
	 * open_advanced and refcounting */
	if (mailbox->index_locktype == LOCK_EXCLUSIVE)
	    return mailbox;
    }

    return NULL;
}

HIDDEN int mailbox_open_exclusive(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_EXCLUSIVE, LOCK_EXCLUSIVE,
				 mailboxptr);
}

EXPORTED void mailbox_index_dirty(struct mailbox *mailbox)
{
    assert(mailbox_index_islocked(mailbox, 1));
    mailbox->i.dirty = 1;
}

EXPORTED void mailbox_modseq_dirty(struct mailbox *mailbox)
{
    assert(mailbox_index_islocked(mailbox, 1));

    if (mailbox->modseq_dirty)
	return;

    mailbox->i.highestmodseq = mboxname_nextmodseq(mailbox->name,
			       mailbox->i.highestmodseq);
    mailbox->last_updated = time(0);
    mailbox->modseq_dirty = 1;
    mailbox_index_dirty(mailbox);
}

HIDDEN void mailbox_ref(struct mailbox *mailbox)
{
    struct mailboxlist *listitem;

    if (!mailbox) return;

    listitem = find_listitem(mailbox->name);
    assert(listitem && &listitem->m == mailbox);
    listitem->nopen++;
}

/*
 * Close the mailbox 'mailbox', freeing all associated resources.
 */
EXPORTED void mailbox_close(struct mailbox **mailboxptr)
{
    int flag;
    struct mailbox *mailbox = *mailboxptr;
    struct mailboxlist *listitem;
    int expunge_days = config_getint(IMAPOPT_EXPUNGE_DAYS);

    /* be safe against double-close */
    if (!mailbox) return;

    listitem = find_listitem(mailbox->name);
    assert(listitem && &listitem->m == mailbox);

    *mailboxptr = NULL;

    /* open multiple times?  Just close this one */
    if (listitem->nopen > 1) {
	listitem->nopen--;
	mailbox_unlock_index(mailbox, NULL);
	return;
    }

    /* auto-cleanup */
    if (mailbox->i.first_expunged &&
	(mailbox->index_locktype == LOCK_EXCLUSIVE)) {
	time_t floor = time(NULL) - (expunge_days * 86400);
	/* but only if we're more than a full week older than 
	 * the expunge time, * so it doesn't turn into lots
	 * of bitty rewrites.
	 * Also, cyr_expire can get first bite if it's been set
	 * to run... */
	if (mailbox->i.first_expunged < floor - (8 * 86400)) {
	    mailbox_expunge_cleanup(mailbox, floor, NULL);
	    /* XXX - handle error code? */
	}
    }
    /* get a re-read of the options field for cleanup purposes */
    if (mailbox->index_fd != -1) {
	if (!mailbox->index_locktype)
	    mailbox_lock_index(mailbox, LOCK_SHARED);
	/* drop the index lock here because we'll lose our right to it
	 * when try to upgrade the mboxlock anyway. */
	mailbox_unlock_index(mailbox, NULL);
    }

    /* do we need to try and clean up? (not if doing a shutdown,
     * speed is probably more important!) */
    if (!in_shutdown && (mailbox->i.options & MAILBOX_CLEANUP_MASK)) {
	int r = mailbox_mboxlock_reopen(listitem, LOCK_NONBLOCKING);
	/* we need to re-open the index because we dropped the mboxname lock,
	 * so the file may have changed */
	if (!r) r = mailbox_open_index(mailbox);
	/* lock_internal so DELETED doesn't cause it to appear to be
	 * NONEXISTENT */
	if (!r) r = mailbox_lock_index_internal(mailbox, LOCK_EXCLUSIVE);
	if (!r) {
	    /* finish cleaning up */
	    if (mailbox->i.options & OPT_MAILBOX_DELETED)
		mailbox_delete_cleanup(mailbox->part, mailbox->name);
	    else if (mailbox->i.options & OPT_MAILBOX_NEEDS_REPACK)
		mailbox_index_repack(mailbox);
	    else if (mailbox->i.options & OPT_MAILBOX_NEEDS_UNLINK)
		mailbox_index_unlink(mailbox);
	    /* or we missed out - someone else beat us to it */

	    /* anyway, unlock again */
	    mailbox_unlock_index(mailbox, NULL);
	}
	/* otherwise someone else has the mailbox locked 
	 * already, so they can handle the cleanup in
	 * THEIR mailbox_close call */
    }

    mailbox_release_resources(mailbox);

    free(mailbox->name);
    free(mailbox->part);
    free(mailbox->acl);
    free(mailbox->uniqueid);
    free(mailbox->quotaroot);
    free(mailbox->specialuse);

    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	free(mailbox->flagname[flag]);
    }

    if (listitem->l) mboxname_release(&listitem->l);

    remove_listitem(listitem);
}

/*
 * Read the header of 'mailbox'
 * format:
 * MAGIC
 * quotaroot TAB uniqueid TAB specialuse
 * userflag1 SPACE userflag2 SPACE userflag3 [...] (with no trailing space)
 * user1 TAB user1acl TAB user2 TAB user2acl TAB (with trailing tab!)
 */
HIDDEN int mailbox_read_header(struct mailbox *mailbox, char **aclptr)
{
    int r = 0;
    int flag;
    const char *name, *p, *tab, *eol;
    const char *fname;
    struct stat sbuf;
    const char *base = NULL;
    size_t len = 0;
    unsigned magic_size = sizeof(MAILBOX_HEADER_MAGIC) - 1;

    /* can't be dirty if we're reading it */
    if (mailbox->header_dirty)
	abort();

    if (mailbox->header_fd != -1)
	close(mailbox->header_fd);

    fname = mailbox_meta_fname(mailbox, META_HEADER);
    mailbox->header_fd = open(fname, O_RDONLY, 0);

    if (mailbox->header_fd == -1) {
	r = IMAP_IOERROR;
	goto done;
    }

    if (fstat(mailbox->header_fd, &sbuf) == -1) {
	close(mailbox->header_fd);
	mailbox->header_fd = 1;
	r = IMAP_IOERROR;
	goto done;
    }

    map_refresh(mailbox->header_fd, 1, &base, &len,
		sbuf.st_size, "header", mailbox->name);
    mailbox->header_file_ino = sbuf.st_ino;
    mailbox->header_file_crc = crc32_map(base, sbuf.st_size);

    /* Check magic number */
    if ((unsigned) sbuf.st_size < magic_size ||
	strncmp(base, MAILBOX_HEADER_MAGIC, magic_size)) {
	r = IMAP_MAILBOX_BADFORMAT;
	goto done;
    }

    /* Read quota data line */
    p = base + sizeof(MAILBOX_HEADER_MAGIC)-1;
    tab = memchr(p, '\t', sbuf.st_size - (p - base));
    eol = memchr(p, '\n', sbuf.st_size - (p - base));
    if (!eol) {
	r = IMAP_MAILBOX_BADFORMAT;
	goto done;
    }

    /* quotaroot (if present) */
    free(mailbox->quotaroot);
    if (!tab || tab > eol) {
	syslog(LOG_DEBUG, "mailbox '%s' has old cyrus.header",
	       mailbox->name);
	tab = eol;
    }
    if (p < tab) {
	mailbox->quotaroot = xstrndup(p, tab - p);
    }
    else {
	mailbox->quotaroot = NULL;
    }

    /* read uniqueid (should always exist unless old format) */
    free(mailbox->uniqueid);
    if (tab < eol) {
	p = tab + 1;
	if (p == eol) {
	    r = IMAP_MAILBOX_BADFORMAT;
	    goto done;
	}
	tab = memchr(p, '\t', sbuf.st_size - (p - base));
	if (!tab || tab > eol) tab = eol;
	mailbox->uniqueid = xstrndup(p, tab - p);
    } else {
	/* uniqueid needs to be generated when we know the uidvalidity */
	mailbox->uniqueid = NULL;
    }

    /* read special use list flags (optional) */
    free(mailbox->specialuse);
    mailbox->specialuse = NULL;
    if (tab < eol) {
	p = tab + 1;
	if (p < eol)
	    mailbox->specialuse = xstrndup(p, eol - p);
    }

    /* Read names of user flags */
    p = eol + 1;
    eol = memchr(p, '\n', sbuf.st_size - (p - base));
    if (!eol) {
	r = IMAP_MAILBOX_BADFORMAT;
	goto done;
    }
    name = p;
    /* read the names of flags */
    for (flag = 0; name <= eol && flag < MAX_USER_FLAGS; flag++) {
	free(mailbox->flagname[flag]);
	mailbox->flagname[flag] = NULL;
	p = memchr(name, ' ', eol-name);
	if (!p) p = eol;
	if (name != p)
	    mailbox->flagname[flag] = xstrndup(name, p-name);
	name = p+1;
    }
    /* zero out the rest */
    for (; flag < MAX_USER_FLAGS; flag++) {
	free(mailbox->flagname[flag]);
	mailbox->flagname[flag] = NULL;
    }

    /* Read ACL */
    p = eol + 1;
    eol = memchr(p, '\n', sbuf.st_size - (p - base));
    if (!eol) {
	r = IMAP_MAILBOX_BADFORMAT;
	goto done;
    }

    if (aclptr)
	*aclptr = xstrndup(p, eol-p);

done:
    if (base) map_free(&base, &len);
    return r;
}

/* set a new ACL - only dirty if changed */
EXPORTED int mailbox_set_acl(struct mailbox *mailbox, const char *acl,
		    int dirty_modseq)
{
    if (mailbox->acl) {
	if (!strcmp(mailbox->acl, acl))
	    return 0; /* no change */
	free(mailbox->acl);
    }
    mailbox->acl = xstrdup(acl);
    mailbox->header_dirty = 1;
    if (dirty_modseq)
	mailbox_modseq_dirty(mailbox);
    return 0;
}

/* set a new QUOTAROOT - only dirty if changed */
EXPORTED int mailbox_set_quotaroot(struct mailbox *mailbox, const char *quotaroot)
{
    if (mailbox->quotaroot) {
	if (quotaroot && !strcmp(mailbox->quotaroot, quotaroot))
	    return 0; /* no change */
	free(mailbox->quotaroot);
	mailbox->quotaroot = NULL;
    }
    else {
	if (!quotaroot)
	    return 0; /* no change */
    }

    if (quotaroot) 
	mailbox->quotaroot = xstrdup(quotaroot);

    /* either way, it's changed, so dirty */
    mailbox->header_dirty = 1;

    return 0;
}

/* set a new XLISTFLAG - only dirty if changed */
HIDDEN int mailbox_set_specialuse(struct mailbox *mailbox, const char *specialuse)
{
    if (mailbox->specialuse) {
	if (specialuse && !strcmp(mailbox->specialuse, specialuse))
	    return 0; /* no change */
	free(mailbox->specialuse);
	mailbox->specialuse = NULL;
    }
    if (specialuse) 
	mailbox->specialuse = xstrdup(specialuse);
    mailbox->header_dirty = 1;
    return 0;
}

/* find or create a user flag - dirty header if change needed */
EXPORTED int mailbox_user_flag(struct mailbox *mailbox, const char *flag,
		      int *flagnum, int create)
{
    int userflag;
    int emptyflag = -1;

    if (!imparse_isatom(flag))
	return IMAP_INVALID_IDENTIFIER;

    for (userflag = 0; userflag < MAX_USER_FLAGS; userflag++) {
	if (mailbox->flagname[userflag]) {
	    if (!strcasecmp(flag, mailbox->flagname[userflag]))
		break;
	}
	else if (emptyflag == -1) {
	    emptyflag = userflag;
	}
    }

    if (userflag == MAX_USER_FLAGS) {
	if (!create)
	    return IMAP_NOTFOUND;

	if (emptyflag == -1) 
	    return IMAP_USERFLAG_EXHAUSTED;

	/* need to be index locked to make flag changes */
	if (!mailbox_index_islocked(mailbox, 1))
	    return IMAP_MAILBOX_LOCKED;

	/* set the flag and mark the header dirty */
	userflag = emptyflag;
	mailbox->flagname[userflag] = xstrdup(flag);
	mailbox->header_dirty = 1;
    }

    if (flagnum) *flagnum = userflag;

    return 0;
}

/* Remove a user flag from the mailbox, so that the slot can
 * be reused.  Called from cyr_expire when we've made certain
 * that no record uses the flag anymore. */
EXPORTED int mailbox_remove_user_flag(struct mailbox *mailbox, int flagnum)
{
    if (flagnum < 0 || flagnum >= MAX_USER_FLAGS)
	return IMAP_INTERNAL;	/* invalid flag number */

    if (!mailbox->flagname[flagnum])
	return 0;		/* already gone */

    /* need to be index locked to make flag changes */
    if (!mailbox_index_islocked(mailbox, 1))
	return IMAP_MAILBOX_LOCKED;

    free(mailbox->flagname[flagnum]);
    mailbox->flagname[flagnum] = NULL;
    mailbox->header_dirty = 1;
    return 0;
}

int mailbox_record_hasflag(struct mailbox *mailbox,
			   struct index_record *record,
			   const char *flag)
{
    int userflag;

    if (!mailbox) return 0;
    if (!flag) return 0;
    if (!record) return 0;

    if (flag[0] == '\\') {
	if (!strcasecmp(flag, "\\answered"))
	    return ((record->system_flags & FLAG_ANSWERED) ? 1 : 0);
	if (!strcasecmp(flag, "\\deleted"))
	    return ((record->system_flags & FLAG_DELETED) ? 1 : 0);
	if (!strcasecmp(flag, "\\draft"))
	    return ((record->system_flags & FLAG_DRAFT) ? 1 : 0);
	if (!strcasecmp(flag, "\\flagged"))
	    return ((record->system_flags & FLAG_FLAGGED) ? 1 : 0);
	if (!strcasecmp(flag, "\\seen")) {
	    /* NOTE: this is a special case because it depends
	     * who the userid is.  We will only return the user
	     * or global seen value */
	    return ((record->system_flags & FLAG_SEEN) ? 1 : 0);
	}
	/* unknown system flag is never present */
	return 0;
    }

    if (mailbox_user_flag(mailbox, flag, &userflag, 0))
	return 0;

    return ((record->user_flags[userflag/32] & (1<<(userflag&31))) ? 1 : 0);
}

HIDDEN int mailbox_buf_to_index_header(const char *buf, struct index_header *i)
{
    uint32_t crc;
    bit32 qannot;

    i->dirty = 0;

    i->generation_no = ntohl(*((bit32 *)(buf+OFFSET_GENERATION_NO)));
    i->format = ntohl(*((bit32 *)(buf+OFFSET_FORMAT)));
    i->minor_version = ntohl(*((bit32 *)(buf+OFFSET_MINOR_VERSION)));
    i->start_offset = ntohl(*((bit32 *)(buf+OFFSET_START_OFFSET)));
    i->record_size = ntohl(*((bit32 *)(buf+OFFSET_RECORD_SIZE)));
    i->num_records = ntohl(*((bit32 *)(buf+OFFSET_NUM_RECORDS)));
    i->last_appenddate = ntohl(*((bit32 *)(buf+OFFSET_LAST_APPENDDATE)));
    i->last_uid = ntohl(*((bit32 *)(buf+OFFSET_LAST_UID)));
    i->quota_mailbox_used = align_ntohll(buf+OFFSET_QUOTA_MAILBOX_USED);
    i->pop3_last_login = ntohl(*((bit32 *)(buf+OFFSET_POP3_LAST_LOGIN)));
    i->uidvalidity = ntohl(*((bit32 *)(buf+OFFSET_UIDVALIDITY)));
    i->deleted = ntohl(*((bit32 *)(buf+OFFSET_DELETED)));
    i->answered = ntohl(*((bit32 *)(buf+OFFSET_ANSWERED)));
    i->flagged = ntohl(*((bit32 *)(buf+OFFSET_FLAGGED)));
    i->options = ntohl(*((bit32 *)(buf+OFFSET_MAILBOX_OPTIONS)));
    i->leaked_cache_records = ntohl(*((bit32 *)(buf+OFFSET_LEAKED_CACHE)));
    i->highestmodseq = align_ntohll(buf+OFFSET_HIGHESTMODSEQ);
    i->deletedmodseq = align_ntohll(buf+OFFSET_DELETEDMODSEQ);
    i->exists = ntohl(*((bit32 *)(buf+OFFSET_EXISTS)));
    i->first_expunged = ntohl(*((bit32 *)(buf+OFFSET_FIRST_EXPUNGED)));
    i->last_repack_time = ntohl(*((bit32 *)(buf+OFFSET_LAST_REPACK_TIME)));
    i->header_file_crc = ntohl(*((bit32 *)(buf+OFFSET_HEADER_FILE_CRC)));
    i->sync_crc = ntohl(*((bit32 *)(buf+OFFSET_SYNC_CRC)));
    i->recentuid = ntohl(*((bit32 *)(buf+OFFSET_RECENTUID)));
    i->recenttime = ntohl(*((bit32 *)(buf+OFFSET_RECENTTIME)));
    i->header_crc = ntohl(*((bit32 *)(buf+OFFSET_HEADER_CRC)));
    i->pop3_show_after = ntohl(*((bit32 *)(buf+OFFSET_POP3_SHOW_AFTER)));
    qannot = ntohl(*((bit32 *)(buf+OFFSET_QUOTA_ANNOT_USED)));
    /* this field is stored as a 32b unsigned on disk but 64b signed
     * in memory, so we need to be careful about sign extension */
    i->quota_annot_used = (quota_t)((unsigned long long)qannot);
    i->sync_crc_vers = ntohl(*((bit32 *)(buf+OFFSET_SYNC_CRC_VERS)));

    if (!i->exists)
	i->options |= OPT_POP3_NEW_UIDL;

    crc = crc32_map(buf, OFFSET_HEADER_CRC);
    if (crc != i->header_crc)
	return IMAP_MAILBOX_CHECKSUM;

    return 0;
}

static int mailbox_refresh_index_map(struct mailbox *mailbox)
{
    size_t need_size;
    struct stat sbuf;

    /* check if we need to extend the mmaped space for the index file
     * (i.e. new records appended since last read) */
    need_size = mailbox->i.start_offset +
		mailbox->i.num_records * mailbox->i.record_size;
    if (mailbox->index_size < need_size) {
	if (fstat(mailbox->index_fd, &sbuf) == -1)
	    return IMAP_IOERROR;

	if (sbuf.st_size < (int)need_size)
	    return IMAP_MAILBOX_BADFORMAT;

	mailbox->index_size = sbuf.st_size;

    }

    /* always refresh, we may be using map_nommap */
    map_refresh(mailbox->index_fd, 1, &mailbox->index_base,
		&mailbox->index_len, mailbox->index_size,
		"index", mailbox->name);

    return 0;
}

static int mailbox_read_index_header(struct mailbox *mailbox)
{
    int r;

    /* no dirty mailboxes please */
    if (mailbox->i.dirty)
	abort();

    /* need to be locked to ensure a consistent read - otherwise
     * a busy mailbox will get CRC errors due to rewrite happening
     * under our feet! */
    if (!mailbox_index_islocked(mailbox, 0))
	return IMAP_MAILBOX_LOCKED;

    /* and of course it needs to exist and have at least a full
     * sized header */
    if (!mailbox->index_base)
	return IMAP_MAILBOX_BADFORMAT;
    if (mailbox->index_size < INDEX_HEADER_SIZE)
	return IMAP_MAILBOX_BADFORMAT;

    /* need to make sure we're reading fresh data! */
    map_refresh(mailbox->index_fd, 1, &mailbox->index_base,
		&mailbox->index_len, mailbox->index_size,
		"index", mailbox->name);

    r = mailbox_buf_to_index_header(mailbox->index_base, &mailbox->i);
    if (r) return r;

    r = mailbox_refresh_index_map(mailbox);
    if (r) return r;

    return 0;
}

/*
 * Read an index record from a mapped index file
 */
HIDDEN int mailbox_buf_to_index_record(const char *buf,
				struct index_record *record)
{
    uint32_t crc;
    int n;

    /* tracking fields - initialise */
    memset(record, 0, sizeof(struct index_record));

    /* parse buffer in to structure */
    record->uid = ntohl(*((bit32 *)(buf+OFFSET_UID)));
    record->internaldate = ntohl(*((bit32 *)(buf+OFFSET_INTERNALDATE)));
    record->sentdate = ntohl(*((bit32 *)(buf+OFFSET_SENTDATE)));
    record->size = ntohl(*((bit32 *)(buf+OFFSET_SIZE)));
    record->header_size = ntohl(*((bit32 *)(buf+OFFSET_HEADER_SIZE)));
    record->gmtime = ntohl(*((bit32 *)(buf+OFFSET_GMTIME)));
    record->cache_offset = ntohl(*((bit32 *)(buf+OFFSET_CACHE_OFFSET)));
    record->last_updated = ntohl(*((bit32 *)(buf+OFFSET_LAST_UPDATED)));
    record->system_flags = ntohl(*((bit32 *)(buf+OFFSET_SYSTEM_FLAGS)));
    for (n = 0; n < MAX_USER_FLAGS/32; n++) {
	record->user_flags[n] = ntohl(*((bit32 *)(buf+OFFSET_USER_FLAGS+4*n)));
    }
    record->content_lines = ntohl(*((bit32 *)(buf+OFFSET_CONTENT_LINES)));
    record->cache_version = ntohl(*((bit32 *)(buf+OFFSET_CACHE_VERSION)));
    message_guid_import(&record->guid, (unsigned char *)buf+OFFSET_MESSAGE_GUID);
    record->modseq = ntohll(*((bit64 *)(buf+OFFSET_MODSEQ)));
    record->cid = ntohll(*(bit64 *)(buf+OFFSET_CID));
    record->cache_crc = ntohl(*((bit32 *)(buf+OFFSET_CACHE_CRC)));
    record->record_crc = ntohl(*((bit32 *)(buf+OFFSET_RECORD_CRC)));

    /* check CRC32 */
    crc = crc32_map(buf, OFFSET_RECORD_CRC);
    if (crc != record->record_crc)
	return IMAP_MAILBOX_CHECKSUM;

    return 0;
}

/*
 * Read an index record from a mailbox
 */
EXPORTED int mailbox_read_index_record(struct mailbox *mailbox,
			      uint32_t recno,
			      struct index_record *record)
{
    const char *buf;
    unsigned offset;
    int r;

    offset = mailbox->i.start_offset + (recno-1) * mailbox->i.record_size;

    if (offset + mailbox->i.record_size > mailbox->index_size) {
	syslog(LOG_ERR,
	       "IOERROR: index record %u for %s past end of file",
	       recno, mailbox->name);
	return IMAP_IOERROR;
    }

    buf = mailbox->index_base + offset;

    r = mailbox_buf_to_index_record(buf, record);

    if (!r) record->recno = recno;

    return r;
}

EXPORTED int mailbox_has_conversations(struct mailbox *mailbox)
{
    char *path;

    /* not needed */
    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    /* we never store data about deleted mailboxes */
    if (mboxname_isdeletedmailbox(mailbox->name, NULL))
	return 0;

    path = conversations_getmboxpath(mailbox->name);
    if (!path) return 0;
    free(path);

    return 1;
}

static int mailbox_lock_conversations(struct mailbox *mailbox)
{
    /* does this mailbox have conversations? */
    if (!mailbox_has_conversations(mailbox))
	return 0;

    /* already locked */
    if (conversations_get_mbox(mailbox->name))
	return 0;

    return conversations_open_mbox(mailbox->name, &mailbox->local_cstate);
}

/*
 * bsearch() comparison function for searching on UID.
 */
static int rec_compar(const void *key, const void *mem)
{
    uint32_t uid = *((uint32_t *) key);
    uint32_t recuid = ntohl(*((bit32 *)((const char *)mem+OFFSET_UID)));
    if (uid < recuid) return -1;
    return (uid > recuid);
}

/*
 * Perform a binary search on the mailbox index file to read the record
 * for uid 'uid' into 'record'.  If 'oldrecord' is not NULL then it is
 * assumed to point a correct and current index record from an earlier
 * call, and the search is bounded by that record.  Returns 0 on success
 * or an IMAP error code on failure.
 */
EXPORTED int mailbox_find_index_record(struct mailbox *mailbox, uint32_t uid,
				       struct index_record *record,
				       const struct index_record *oldrecord)
{
    const char *mem, *base = mailbox->index_base + mailbox->i.start_offset;
    const char *low = base;
    size_t num_records = mailbox->i.num_records;
    size_t size = mailbox->i.record_size;
    int r;

    if (uid > mailbox->i.last_uid) return IMAP_NOTFOUND;

    if (oldrecord) {
	const char *oldmem = base + (oldrecord->recno-1) * size;
	if (uid == oldrecord->uid) {
	    /* already found it */
	    low = oldmem;
	    num_records = 1;
	}
	else if (uid == oldrecord->uid+1) {
	    /* Optimise for the common case of moving up by one uid.
	     * The index file is in UID order so the record we want
	     * is either the next one or is not present. */
	    low = oldmem + size;
	    num_records = 1;
	}
	else if (uid < oldrecord->uid) {
	    /* target is before the old record */
	    num_records = oldrecord->recno-1;
	}
	else {
	    /* target is after the old record */
	    low = oldmem + size;
	    num_records -= oldrecord->recno;
	}
    }

    mem =  bsearch(&uid, low, num_records, size, rec_compar);
    if (!mem) return IMAP_NOTFOUND;

    if ((r = mailbox_buf_to_index_record(mem, record))) return r;

    record->recno = ((mem - base) / size) + 1;

    return 0;
}

/*
 * Lock the index file for 'mailbox'.  Reread index file header if necessary.
 */
static int mailbox_lock_index_internal(struct mailbox *mailbox, int locktype)
{
    struct stat sbuf;
    int r = 0;
    const char *header_fname = mailbox_meta_fname(mailbox, META_HEADER);
    const char *index_fname = mailbox_meta_fname(mailbox, META_INDEX);

    assert(mailbox->index_fd != -1);
    assert(!mailbox->index_locktype);

restart:
    r = 0;

    if (locktype == LOCK_EXCLUSIVE) {
	/* handle read-only case cleanly - we need to re-open read-write first! */
	if (mailbox->is_readonly) {
	    mailbox->is_readonly = 0;
	    r = mailbox_open_index(mailbox);
	}
	/* XXX - this could be handled out a layer, but we always
	 * need to have a locked conversations DB */
	if (!r) r = mailbox_lock_conversations(mailbox);
	if (!r) r = lock_blocking(mailbox->index_fd, index_fname);
    }
    else if (locktype == LOCK_SHARED) {
	r = lock_shared(mailbox->index_fd, index_fname);
    }
    else {
	/* this function does not support nonblocking locks */
	fatal("invalid locktype for index", EC_SOFTWARE);
    }

    /* double check that the index exists and has at least enough
     * data to check the version number */
    if (!r) {
	if (!mailbox->index_base)
	    r = IMAP_MAILBOX_BADFORMAT;
	else if (mailbox->index_size < OFFSET_NUM_RECORDS)
	    r = IMAP_MAILBOX_BADFORMAT;
	if (r)
	    lock_unlock(mailbox->index_fd, index_fname);
    }

    if (r) {
	syslog(LOG_ERR, "IOERROR: locking index for %s: %s",
	       mailbox->name, error_message(r));
	return IMAP_IOERROR;
    }

    mailbox->index_locktype = locktype;
    gettimeofday(&mailbox->starttime, 0);

    r = stat(header_fname, &sbuf);
    if (r == -1) {
	syslog(LOG_ERR, "IOERROR: stating header %s for %s: %m",
	       header_fname, mailbox->name);
	mailbox_unlock_index(mailbox, NULL);
	return IMAP_IOERROR;
    }

    /* has the header file changed? */
    if (sbuf.st_ino != mailbox->header_file_ino) {
	r = mailbox_read_header(mailbox, NULL);
	if (r) {
	    syslog(LOG_ERR, "IOERROR: reading header for %s: %m",
		   mailbox->name);
	    mailbox_unlock_index(mailbox, NULL);
	    return r;
	}
    }

    /* make sure the mailbox is up to date if we haven't
     * already had a successful load */
    if (!mailbox->i.minor_version) {
	bit32 minor_version = ntohl(*((bit32 *)(mailbox->index_base+OFFSET_MINOR_VERSION)));
	if (minor_version != MAILBOX_MINOR_VERSION) {
	    struct mailboxlist *listitem = find_listitem(mailbox->name);
	    int prev_locktype;

	    assert(listitem);

	    prev_locktype = listitem->l->locktype;

	    /* we need to switch to an exclusive lock while upgrading */
	    r = mailbox_mboxlock_reopen(listitem, LOCK_EXCLUSIVE);
	    if (r) return r;
	    r = mailbox_open_index(mailbox);
	    if (r) return r;

	    /* lie about our index lock status - the exclusive namelock
	     * provides equivalent properties - and we know it won't
	     * leak because the 'restart' above will cover up our sins */
	    mailbox->index_locktype = LOCK_EXCLUSIVE;
	    r = upgrade_index(mailbox);
	    if (r) return r;

	    /* recalculate all counts */
	    r = mailbox_open_index(mailbox);
	    if (r) return r;
	    r = mailbox_read_index_header(mailbox);
	    if (r) return r;
	    r = mailbox_index_recalc(mailbox);
	    if (r) return r;
	    r = mailbox_commit(mailbox);
	    if (r) return r;

	    /* we have to downgrade again afterwards so a "SELECT" won't
	     * hold an exclusive lock forever */
	    r = mailbox_mboxlock_reopen(listitem, prev_locktype);
	    if (r) return r;
	    r = mailbox_open_index(mailbox);
	    if (r) return r;

	    goto restart;
	}
    }

    /* note: it's guaranteed by our outer cyrus.lock lock that the
     * cyrus.index and cyrus.cache files are never rewritten, so
     * we're safe to just extend the map if needed */
    r = mailbox_read_index_header(mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: refreshing index for %s: %m",
	       mailbox->name);
	mailbox_unlock_index(mailbox, NULL);
	return r;
    }

    /* check the CRC */
    if (mailbox->header_file_crc != mailbox->i.header_file_crc) {
	syslog(LOG_ERR, "IOERROR: header CRC mismatch %s: %08X %08X",
	       mailbox->name, (unsigned int)mailbox->header_file_crc,
	       (unsigned int)mailbox->i.header_file_crc);
	mailbox_unlock_index(mailbox, NULL);
	return IMAP_MAILBOX_CHECKSUM;
    }

    return 0;
}

EXPORTED int mailbox_lock_index(struct mailbox *mailbox, int locktype)
{
    int r = mailbox_lock_index_internal(mailbox, locktype);
    if (r) return r;

    /* otherwise, sanity checks for regular use, but not for internal
     * use during cleanup */

    /* we may be in the process of deleting this mailbox */
    if (mailbox->i.options & OPT_MAILBOX_DELETED) {
	mailbox_unlock_index(mailbox, NULL);
	return IMAP_MAILBOX_NONEXISTENT;
    }

    return 0;
}

/*
 * Release lock on the index file for 'mailbox'
 */
EXPORTED void mailbox_unlock_index(struct mailbox *mailbox, struct statusdata *sdata)
{
    struct timeval endtime;
    double timediff;
    int r;
    const char *index_fname = mailbox_meta_fname(mailbox, META_INDEX);

    /* naughty - you can't unlock a dirty mailbox! */
    r = mailbox_commit(mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: failed to commit mailbox %s, "
	       "probably need to reconstruct",
	       mailbox->name);
	abort();
    }

    if (mailbox->has_changed) {
	if (updatenotifier) updatenotifier(mailbox->name);
	sync_log_mailbox(mailbox->name);
	statuscache_invalidate(mailbox->name, sdata);

	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: modseq sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> highestmodseq=<" MODSEQ_FMT ">",
		session_id(), mailbox->name, mailbox->uniqueid,
		mailbox->i.highestmodseq);

	if (config_getstring(IMAPOPT_MAILBOX_UPDATE_NOTIFIER_SOCKET))
	    send_push_notification(mailbox);

	mailbox->has_changed = 0;
    }
    else if (sdata) {
	/* updated data, always write */
	statuscache_invalidate(mailbox->name, sdata);
    }

    if (mailbox->index_locktype) {
	if (lock_unlock(mailbox->index_fd, index_fname))
	    syslog(LOG_ERR, "IOERROR: unlocking index of %s: %m", 
		mailbox->name);
	mailbox->index_locktype = 0;
    }

    gettimeofday(&endtime, 0);
    timediff = timesub(&mailbox->starttime, &endtime);
    if (timediff > 1.0) {
	syslog(LOG_NOTICE, "mailbox: longlock %s for %0.1f seconds",
	       mailbox->name, timediff);
    }

    if (mailbox->local_cstate) {
	int r = conversations_commit(&mailbox->local_cstate);
	if (r)
	    syslog(LOG_ERR, "Error committing to conversations database for mailbox %s: %s",
		   mailbox->name, error_message(r));
    }
}

EXPORTED int mailbox_yield_index(struct mailbox *mailbox)
{
    int locktype = mailbox->index_locktype;

    if (!locktype) return 0;

    mailbox_unlock_index(mailbox, NULL);
    return mailbox_lock_index(mailbox, locktype);
}

/*
 * Write the header file for 'mailbox'
 */
static int mailbox_commit_header(struct mailbox *mailbox)
{
    int flag;
    int fd;
    int r = 0;
    const char *quotaroot;
    const char *newfname;
    struct iovec iov[10];
    int niov;

    if (!mailbox->header_dirty)
	return 0; /* nothing to write! */

    /* we actually do all header actions under an INDEX lock, because
     * we need to write the crc32 to be consistent! */
    assert(mailbox_index_islocked(mailbox, 1));

    newfname = mailbox_meta_newfname(mailbox, META_HEADER);

    fd = open(newfname, O_CREAT | O_TRUNC | O_RDWR, 0666);
    if (fd == -1) {
	syslog(LOG_ERR, "IOERROR: opening %s: %m", newfname);
	return IMAP_IOERROR;
    }

    /* Write magic header, do NOT write the trailing NUL */
    r = write(fd, MAILBOX_HEADER_MAGIC,
	      sizeof(MAILBOX_HEADER_MAGIC) - 1);

    if (r != -1) {
	niov = 0;
	quotaroot = mailbox->quotaroot ? mailbox->quotaroot : "";
	WRITEV_ADDSTR_TO_IOVEC(iov,niov,quotaroot);
	WRITEV_ADD_TO_IOVEC(iov,niov,"\t",1);
	WRITEV_ADDSTR_TO_IOVEC(iov,niov,mailbox->uniqueid);
	if (mailbox->specialuse) {
	    WRITEV_ADD_TO_IOVEC(iov,niov,"\t",1);
	    WRITEV_ADDSTR_TO_IOVEC(iov,niov,mailbox->specialuse);
	}
	WRITEV_ADD_TO_IOVEC(iov,niov,"\n",1);
	r = retry_writev(fd, iov, niov);
    }

    if (r != -1) {
	for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	    if (mailbox->flagname[flag]) {
		niov = 0;
		WRITEV_ADDSTR_TO_IOVEC(iov,niov,mailbox->flagname[flag]);
		WRITEV_ADD_TO_IOVEC(iov,niov," ",1);
		r = retry_writev(fd, iov, niov);
		if(r == -1) break;
	    }
	}
    }

    if (r != -1) {
	niov = 0;
	WRITEV_ADD_TO_IOVEC(iov,niov,"\n",1);
	WRITEV_ADDSTR_TO_IOVEC(iov,niov,mailbox->acl);
	WRITEV_ADD_TO_IOVEC(iov,niov,"\n",1);
	r = retry_writev(fd, iov, niov);
    }

    if (r == -1 || fsync(fd)) {
	syslog(LOG_ERR, "IOERROR: writing %s: %m", newfname);
	close(fd);
	unlink(newfname);
	return IMAP_IOERROR;
    }

    close(fd);

    /* rename the new header file over the old one */
    r = mailbox_meta_rename(mailbox, META_HEADER);
    if (r) return r;
    mailbox->header_dirty = 0; /* we wrote it out, so not dirty any more */

    /* re-read the header */
    r = mailbox_read_header(mailbox, NULL);
    if (r) return r;

    /* copy the new CRC into the index header */
    mailbox->i.header_file_crc = mailbox->header_file_crc;
    mailbox_index_dirty(mailbox);

    return 0;
}

static bit32 mailbox_index_header_to_buf(struct index_header *i, unsigned char *buf)
{
    bit32 crc;
    bit32 options = i->options & MAILBOX_OPT_VALID;

    *((bit32 *)(buf+OFFSET_GENERATION_NO)) = htonl(i->generation_no);
    *((bit32 *)(buf+OFFSET_FORMAT)) = htonl(i->format);
    *((bit32 *)(buf+OFFSET_MINOR_VERSION)) = htonl(i->minor_version);
    *((bit32 *)(buf+OFFSET_START_OFFSET)) = htonl(i->start_offset);
    *((bit32 *)(buf+OFFSET_RECORD_SIZE)) = htonl(i->record_size);
    *((bit32 *)(buf+OFFSET_NUM_RECORDS)) = htonl(i->num_records);
    *((bit32 *)(buf+OFFSET_LAST_APPENDDATE)) = htonl(i->last_appenddate);
    *((bit32 *)(buf+OFFSET_LAST_UID)) = htonl(i->last_uid);

    /* quotas may be 64bit now */
    align_htonll(buf+OFFSET_QUOTA_MAILBOX_USED, i->quota_mailbox_used);

    *((bit32 *)(buf+OFFSET_POP3_LAST_LOGIN)) = htonl(i->pop3_last_login);
    *((bit32 *)(buf+OFFSET_UIDVALIDITY)) = htonl(i->uidvalidity);
    *((bit32 *)(buf+OFFSET_DELETED)) = htonl(i->deleted);
    *((bit32 *)(buf+OFFSET_ANSWERED)) = htonl(i->answered);
    *((bit32 *)(buf+OFFSET_FLAGGED)) = htonl(i->flagged);
    *((bit32 *)(buf+OFFSET_MAILBOX_OPTIONS)) = htonl(options);
    *((bit32 *)(buf+OFFSET_LEAKED_CACHE)) = htonl(i->leaked_cache_records);
    align_htonll(buf+OFFSET_HIGHESTMODSEQ, i->highestmodseq);
    align_htonll(buf+OFFSET_DELETEDMODSEQ, i->deletedmodseq);
    *((bit32 *)(buf+OFFSET_EXISTS)) = htonl(i->exists);
    *((bit32 *)(buf+OFFSET_FIRST_EXPUNGED)) = htonl(i->first_expunged);
    *((bit32 *)(buf+OFFSET_LAST_REPACK_TIME)) = htonl(i->last_repack_time);
    *((bit32 *)(buf+OFFSET_HEADER_FILE_CRC)) = htonl(i->header_file_crc);
    *((bit32 *)(buf+OFFSET_SYNC_CRC)) = htonl(i->sync_crc);
    *((bit32 *)(buf+OFFSET_RECENTUID)) = htonl(i->recentuid);
    *((bit32 *)(buf+OFFSET_RECENTTIME)) = htonl(i->recenttime);
    *((bit32 *)(buf+OFFSET_POP3_SHOW_AFTER)) = htonl(i->pop3_show_after);
    /* this field is 64b in memory but 32b on disk - as it counts
     * bytes stored in dbs and the dbs are 32b anyway there should
     * be no problem */
    *((bit32 *)(buf+OFFSET_QUOTA_ANNOT_USED)) = htonl((bit32)i->quota_annot_used);
    *((bit32 *)(buf+OFFSET_SYNC_CRC_VERS)) = htonl(i->sync_crc_vers);

    /* Update checksum */
    crc = htonl(crc32_map((char *)buf, OFFSET_HEADER_CRC));
    *((bit32 *)(buf+OFFSET_HEADER_CRC)) = crc;

    return crc;
}

HIDDEN int mailbox_commit_quota(struct mailbox *mailbox)
{
    int res;
    int changed = 0;
    quota_t quota_usage[QUOTA_NUMRESOURCES];

    /* not dirty */
    if (!mailbox->quota_dirty)
	return 0;

    mailbox->quota_dirty = 0;

    /* no quota root means we don't track quota.  That's OK */
    if (!mailbox->quotaroot)
	return 0;

    mailbox_get_usage(mailbox, quota_usage);
    for (res = 0; res < QUOTA_NUMRESOURCES; res++) {
	quota_usage[res] -= mailbox->quota_previously_used[res];
	if (quota_usage[res] != 0) {
	    changed++;
	}
    }
    /* unchanged */
    if (!changed)
	return 0;

    assert(mailbox_index_islocked(mailbox, 1));

    quota_update_useds(mailbox->quotaroot, quota_usage, mailbox->name);
    /* XXX - fail upon issue?  It's tempting */

    return 0;
}



/*
 * Write the index header for 'mailbox'
 */
EXPORTED int mailbox_commit(struct mailbox *mailbox)
{
    /* XXX - ibuf for alignment? */
    static unsigned char buf[INDEX_HEADER_SIZE];
    int n, r;

    /* try to commit sub parts first */
    r = mailbox_commit_cache(mailbox);
    if (r) return r;

    r = mailbox_commit_quota(mailbox);
    if (r) return r;

    r = annotate_state_commit(&mailbox->annot_state);
    if (r) return r;

    r = mailbox_commit_header(mailbox);
    if (r) return r;

    if (!mailbox->i.dirty)
	return 0;

    assert(mailbox_index_islocked(mailbox, 1));

    if (mailbox->i.start_offset < INDEX_HEADER_SIZE)
	fatal("Mailbox offset bug", EC_SOFTWARE);

    mailbox_index_header_to_buf(&mailbox->i, buf);

    lseek(mailbox->index_fd, 0, SEEK_SET);
    n = retry_write(mailbox->index_fd, buf, INDEX_HEADER_SIZE);
    if ((unsigned long)n != INDEX_HEADER_SIZE || fsync(mailbox->index_fd)) {
	syslog(LOG_ERR, "IOERROR: writing index header for %s: %m",
	       mailbox->name);
	return IMAP_IOERROR;
    }

    /* remove all dirty flags! */
    mailbox->i.dirty = 0;
    mailbox->modseq_dirty = 0;
    mailbox->header_dirty = 0;

    /* label changes for later logging */
    mailbox->has_changed = 1;

    return 0;
}

/*
 * Put an index record into a buffer suitable for writing to a file.
 */
static bit32 mailbox_index_record_to_buf(struct index_record *record,
				  unsigned char *buf)
{
    int n;
    bit32 crc;

    *((bit32 *)(buf+OFFSET_UID)) = htonl(record->uid);
    *((bit32 *)(buf+OFFSET_INTERNALDATE)) = htonl(record->internaldate);
    *((bit32 *)(buf+OFFSET_SENTDATE)) = htonl(record->sentdate);
    *((bit32 *)(buf+OFFSET_SIZE)) = htonl(record->size);
    *((bit32 *)(buf+OFFSET_HEADER_SIZE)) = htonl(record->header_size);
    *((bit32 *)(buf+OFFSET_GMTIME)) = htonl(record->gmtime);
    *((bit32 *)(buf+OFFSET_CACHE_OFFSET)) = htonl(record->cache_offset);
    *((bit32 *)(buf+OFFSET_LAST_UPDATED)) = htonl(record->last_updated);
    *((bit32 *)(buf+OFFSET_SYSTEM_FLAGS)) = htonl(record->system_flags);
    for (n = 0; n < MAX_USER_FLAGS/32; n++) {
	*((bit32 *)(buf+OFFSET_USER_FLAGS+4*n)) = htonl(record->user_flags[n]);
    }
    *((bit32 *)(buf+OFFSET_CONTENT_LINES)) = htonl(record->content_lines);
    *((bit32 *)(buf+OFFSET_CACHE_VERSION)) = htonl(record->cache_version);
    message_guid_export(&record->guid, buf+OFFSET_MESSAGE_GUID);
    *((bit64 *)(buf+OFFSET_MODSEQ)) = htonll(record->modseq);
    *((bit64 *)(buf+OFFSET_CID)) = htonll(record->cid);
    *((bit32 *)(buf+OFFSET_CACHE_CRC)) = htonl(record->cache_crc);   

    /* calculate the checksum */
    crc = crc32_map((char *)buf, OFFSET_RECORD_CRC);
    *((bit32 *)(buf+OFFSET_RECORD_CRC)) = htonl(crc);

    return crc;
}


static void mailbox_quota_dirty(struct mailbox *mailbox)
{
    /* track quota use */
    if (!mailbox->quota_dirty) {
	mailbox->quota_dirty = 1;
	mailbox_get_usage(mailbox, mailbox->quota_previously_used);
    }
}

static void header_update_counts(struct index_header *i,
				 struct index_record *record,
				 int is_add)
{
    int num = is_add ? 1 : -1;

    /* we don't track counts for EXPUNGED records */
    if (record->system_flags & FLAG_EXPUNGED)
	return;

    /* update mailbox header fields */
    if (record->system_flags & FLAG_ANSWERED)
	i->answered += num;

    if (record->system_flags & FLAG_FLAGGED)
	i->flagged += num;

    if (record->system_flags & FLAG_DELETED)
	i->deleted += num;

    if (is_add) {
	i->exists++;
	i->quota_mailbox_used += record->size;
    }
    else {
	if (i->exists) i->exists--;

	/* corruption prevention - check we don't go negative */
	if (i->quota_mailbox_used > record->size)
	    i->quota_mailbox_used -= record->size;
	else
	    i->quota_mailbox_used = 0;
    }
}

/*************************** Sync CRC algorithms ***************************/

typedef struct mailbox_crcalgo mailbox_crcalgo_t;
struct mailbox_crcalgo {
    unsigned version;
    uint32_t (*record)(const struct mailbox *, const struct index_record *);
    uint32_t (*annot)(unsigned int uid, const char *entry,
		   const char *userid, const struct buf *value);
};

struct annot_calc_rock
{
    const mailbox_crcalgo_t *algo;
    uint32_t crc;
    quota_t used;
};

static uint32_t crc32_record(const struct mailbox *mailbox,
			  const struct index_record *record)
{
    char buf[4096];
    uint32_t flagcrc = 0;
    int flag;

    /* expunged flags have no sync CRC */
    if (record->system_flags & FLAG_EXPUNGED)
	return 0;

    /* calculate an XORed CRC32 over all the flags on the message, so no
     * matter what order they are store in the header, the final value 
     * is the same */
    if (record->system_flags & FLAG_DELETED)
	flagcrc ^= crc32_cstring("\\deleted");
    if (record->system_flags & FLAG_ANSWERED)
	flagcrc ^= crc32_cstring("\\answered");
    if (record->system_flags & FLAG_FLAGGED)
	flagcrc ^= crc32_cstring("\\flagged");
    if (record->system_flags & FLAG_DRAFT)
	flagcrc ^= crc32_cstring("\\draft");
    if (record->system_flags & FLAG_SEEN)
	flagcrc ^= crc32_cstring("\\seen");

    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	if (!mailbox->flagname[flag])
	    continue;
	if (!(record->user_flags[flag/32] & (1<<(flag&31))))
	    continue;
	/* need to compare without case being significant */
	strlcpy(buf, mailbox->flagname[flag], 4096);
	lcase(buf);
	flagcrc ^= crc32_cstring(buf);
    }

    snprintf(buf, sizeof(buf), "%u " MODSEQ_FMT " %lu (%u) %lu %s",
	    record->uid, record->modseq, record->last_updated,
	    flagcrc,
	    record->internaldate,
	    message_guid_encode(&record->guid));

    return crc32_cstring(buf);
}

static int cmpcase(const void *a, const void *b)
{
    return strcasecmp(*(const char **)a, *(const char **)b);
}

static uint32_t md5_record(const struct mailbox *mailbox,
			const struct index_record *record)
{
    MD5_CTX ctx;
    union {
	uint32_t b32;
	unsigned char md5[16];
    } result;
    unsigned int i;
    unsigned int nflags = 0;
    int n;
    const char *flags[MAX_USER_FLAGS + /*system flags*/5];
    char buf[256];
    static struct buf flagbuf = BUF_INITIALIZER;

    /* expunged flags have no sync CRC */
    if (record->system_flags & FLAG_EXPUNGED)
	return 0;

    MD5Init(&ctx);

    /* system flags - already sorted lexically */
    if (record->system_flags & FLAG_ANSWERED)
	flags[nflags++] = "\\answered";
    if (record->system_flags & FLAG_DELETED)
	flags[nflags++] = "\\deleted";
    if (record->system_flags & FLAG_DRAFT)
	flags[nflags++] = "\\draft";
    if (record->system_flags & FLAG_FLAGGED)
	flags[nflags++] = "\\flagged";
    if (record->system_flags & FLAG_SEEN)
	flags[nflags++] = "\\seen";

    /* user flags */
    for (i = 0; i < MAX_USER_FLAGS; i++) {
	if (!mailbox->flagname[i])
	    continue;
	if (!(record->user_flags[i/32] & (1<<(i&31))))
	    continue;
	flags[nflags++] = mailbox->flagname[i];
    }

    /*
     * There is a potential optimisation here: we only need to sort if
     * there were any user flags because the system flags are added
     * pre-sorted.  However, we expect never to achieve that in
     * production, so we don't code it.
     */
    qsort(flags, nflags, sizeof(char *), cmpcase);

    n = snprintf(buf, sizeof(buf), "%u", record->uid);
    MD5Update(&ctx, buf, n);

    MD5Update(&ctx, " ", 1);

    n = snprintf(buf, sizeof(buf), "%llu", record->modseq);
    MD5Update(&ctx, buf, n);

    MD5Update(&ctx, " ", 1);

    n = snprintf(buf, sizeof(buf), "%lu", record->last_updated);
    MD5Update(&ctx, buf, n);

    MD5Update(&ctx, " (", 2);

    for (i = 0 ; i < nflags ; i++) {
	if (i)
	    MD5Update(&ctx, " ", 1);

	buf_reset(&flagbuf);
	buf_appendcstr(&flagbuf, flags[i]);
	buf_cstring(&flagbuf);
	lcase(flagbuf.s);
	MD5Update(&ctx, flagbuf.s, flagbuf.len);
    }

    MD5Update(&ctx, ") ", 2);

    n = snprintf(buf, sizeof(buf), "%lu", record->internaldate);
    MD5Update(&ctx, buf, n);

    MD5Update(&ctx, " ", 1);

    MD5Update(&ctx, message_guid_encode(&record->guid), 2*MESSAGE_GUID_SIZE);

    MD5Update(&ctx, " ", 1);

    n = snprintf(buf, sizeof(buf), "%llu", record->cid);
    MD5Update(&ctx, buf, n);

    MD5Final(result.md5, &ctx);

    return ntohl(result.b32);
}

static uint32_t md5_annot(unsigned int uid, const char *entry,
		       const char *userid, const struct buf *value)
{
    MD5_CTX ctx;
    union {
	uint32_t b32;
	unsigned char md5[16];
    } result;
    char buf[32];

    MD5Init(&ctx);

    snprintf(buf, sizeof(buf), "%u", uid);
    MD5Update(&ctx, buf, strlen(buf));
    MD5Update(&ctx, " ", 1);
    MD5Update(&ctx, entry, strlen(entry));
    MD5Update(&ctx, " ", 1);
    MD5Update(&ctx, userid, strlen(userid));
    MD5Update(&ctx, " ", 1);
    MD5Update(&ctx, value->s, value->len);

    MD5Final(result.md5, &ctx);

    return ntohl(result.b32);
}

static const mailbox_crcalgo_t crcalgos[] = {
    {
	1,		    /* historical 2.4.x CRC algorithm */
	crc32_record,
	NULL },
    {
	2,		    /* XOR the first 16 bytes of md5s instead */
	md5_record,
	md5_annot },
    { 0, NULL, NULL }
};

static const mailbox_crcalgo_t *mailbox_find_crcalgo(unsigned minvers, unsigned maxvers)
{
    const mailbox_crcalgo_t *alg;
    const mailbox_crcalgo_t *best = NULL;

    for (alg = crcalgos ; alg->version ; alg++) {
	if (alg->version < minvers)
	    continue;
	if (alg->version > maxvers)
	    continue;
	if (best && best->version > alg->version)
	    continue;
	best = alg;
    }
    return best;
}

EXPORTED unsigned mailbox_best_crcvers(unsigned minvers, unsigned maxvers)
{
    const mailbox_crcalgo_t *alg = mailbox_find_crcalgo(minvers, maxvers);
    if (!alg) return 0;
    return alg->version;
}

static const mailbox_crcalgo_t *mailbox_get_crcalgo(struct mailbox *mailbox)
{
    const mailbox_crcalgo_t *alg = NULL;

    if (mailbox->i.sync_crc_vers) {
	alg = mailbox_find_crcalgo(mailbox->i.sync_crc_vers,
				   mailbox->i.sync_crc_vers);
	if (!alg && mailbox_index_islocked(mailbox, /*write*/1)) {
	    mailbox->i.sync_crc_vers = 0;	/* invalidate the CRC version */
	    mailbox_index_dirty(mailbox);
	}
    }

    return alg;
}

EXPORTED void mailbox_annot_changed(struct mailbox *mailbox,
			   unsigned int uid,
			   const char *entry,
			   const char *userid,
			   const struct buf *oldval,
			   const struct buf *newval)
{
    const mailbox_crcalgo_t *alg = mailbox_get_crcalgo(mailbox);

    /* we are dirtying both index and quota */
    mailbox_index_dirty(mailbox);
    mailbox_quota_dirty(mailbox);

    /* update sync_crc - NOTE, only per-message annotations count */
    if (uid && alg && alg->annot) {
	if (oldval->len)
	    mailbox->i.sync_crc ^= alg->annot(uid, entry, userid, oldval);
	if (newval->len)
	    mailbox->i.sync_crc ^= alg->annot(uid, entry, userid, newval);
    }

    /* corruption prevention - check we don't go negative */
    if (mailbox->i.quota_annot_used > oldval->len)
	mailbox->i.quota_annot_used -= oldval->len;
    else
	mailbox->i.quota_annot_used = 0;

    mailbox->i.quota_annot_used += newval->len;
}

static int calc_one_annot(const char *mailbox __attribute__((unused)),
			  uint32_t uid,
			  const char *entry,
			  const char *userid,
			  const struct buf *value,
			  void *rock)
{
    struct annot_calc_rock *cr = (struct annot_calc_rock *)rock;

    /* update sync_crc - NOTE, only per-message annotations count */
    if (uid && cr->algo && cr->algo->annot)
	cr->crc ^= cr->algo->annot(uid, entry, userid, value);

    /* always count the size */
    cr->used += value->len;

    return 0;
}

static void mailbox_annot_update_counts(struct mailbox *mailbox,
					struct index_record *record,
					int is_add)
{
    struct annot_calc_rock cr = { mailbox_get_crcalgo(mailbox), 0, 0 };

    /* expunged records don't count */
    if (record && record->system_flags & FLAG_EXPUNGED) return;

    annotatemore_findall(mailbox->name, record ? record->uid : 0, /* all entries*/"*",
			 calc_one_annot, &cr);

    mailbox->i.sync_crc ^= cr.crc;

    if (is_add)
	mailbox->i.quota_annot_used += cr.used;
    else {
	/* corruption prevention - check we don't go negative */
	if (mailbox->i.quota_annot_used > cr.used)
	    mailbox->i.quota_annot_used -= cr.used;
	else
	    mailbox->i.quota_annot_used = 0;
    }
}

/*
 * Calculate a sync CRC for the entire @mailbox using CRC algorithm
 * version @vers, optionally forcing recalculation
 */
EXPORTED uint32_t mailbox_sync_crc(struct mailbox *mailbox, unsigned vers, int force)
{
    annotate_state_t *astate = NULL;
    const mailbox_crcalgo_t *alg;
    struct index_record record;
    uint32_t recno;
    uint32_t crc = 0;

    /* check if we can use the persistent incremental CRC */
    if (vers == mailbox->i.sync_crc_vers && !force) {
	return mailbox->i.sync_crc;
    }
    /* otherwise, we're on the slow path */

    /* find the algorithm */
    alg = mailbox_find_crcalgo(vers, vers);
    if (!alg) return 0;

    if (alg->annot) {
	/* hold annotations DB open - failure to load is an error */
	if (mailbox_get_annotate_state(mailbox, ANNOTATE_ANY_UID, &astate))
	    return 0;

	/* and make sure it stays locked for the whole process */
	annotate_state_begin(astate);
    }

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	/* we can't send bogus records, just skip them! */
	if (mailbox_read_index_record(mailbox, recno, &record))
	    continue;

	/* always skip EXPUNGED messages, they have no CRC */
	if (record.system_flags & FLAG_EXPUNGED)
	    continue;

	if (alg->record) 
	    crc ^= alg->record(mailbox, &record);

	if (alg->annot) {
	    struct annot_calc_rock cr = { alg, 0, 0 };
	    annotatemore_findall(mailbox->name, record.uid, /* all entries*/"*",
				 calc_one_annot, &cr);
	    crc ^= cr.crc;
	}
    }

    /* possibly upgrade the persistent CRC version */
    if (mailbox_index_islocked(mailbox, /*write*/1)) {
	mailbox->i.sync_crc = crc;
	mailbox->i.sync_crc_vers = vers;
	mailbox_index_dirty(mailbox);
    }

    /* return the newly calculated CRC */
    return crc;
}

static void mailbox_index_update_counts(struct mailbox *mailbox,
					struct index_record *record,
					int is_add)
{
    const mailbox_crcalgo_t *alg = mailbox_get_crcalgo(mailbox);

    mailbox_quota_dirty(mailbox);
    mailbox_index_dirty(mailbox);
    header_update_counts(&mailbox->i, record, is_add);

    if (alg && alg->record)
	mailbox->i.sync_crc ^= alg->record(mailbox, record);
}


EXPORTED int mailbox_index_recalc(struct mailbox *mailbox)
{
    annotate_state_t *astate = NULL;
    struct index_record record;
    uint32_t recno;
    int r = 0;

    assert(mailbox_index_islocked(mailbox, 1));

    /* cache the old used quota */
    mailbox_quota_dirty(mailbox);
    mailbox_index_dirty(mailbox);

    mailbox->i.answered = 0;
    mailbox->i.flagged = 0;
    mailbox->i.deleted = 0;
    mailbox->i.exists = 0;
    mailbox->i.quota_mailbox_used = 0;
    mailbox->i.quota_annot_used = 0;
    mailbox->i.sync_crc = 0;

    /* mailbox level annotations */
    mailbox_annot_update_counts(mailbox, NULL, 1);

    /* hold annotations DB open */
    r = mailbox_get_annotate_state(mailbox, ANNOTATE_ANY_UID, &astate);
    if (r) goto out;

    /* and make sure it stays locked for the whole process */
    annotate_state_begin(astate);

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) goto out;

	mailbox_index_update_counts(mailbox, &record, 1);
	mailbox_annot_update_counts(mailbox, &record, 1);
    }

out:
    return r;
}

EXPORTED int mailbox_update_conversations(struct mailbox *mailbox,
				 struct index_record *old,
				 struct index_record *new)
{
    int r = 0;
    conversation_t *conv = NULL;
    int delta_num_records = 0;
    int delta_exists = 0;
    int delta_unseen = 0;
    int delta_size = 0;
    int *delta_counts = NULL;
    int i;
    modseq_t modseq = 0;
    struct index_record *record = NULL;
    struct conversations_state *cstate = NULL;

    if (!mailbox_has_conversations(mailbox))
	return 0;

    cstate = conversations_get_mbox(mailbox->name);
    if (!cstate)
	return IMAP_CONVERSATIONS_NOT_OPEN;

    /* handle unlinked items as if they didn't exist */
    if (old && (old->system_flags & FLAG_UNLINKED)) old = NULL;
    if (new && (new->system_flags & FLAG_UNLINKED)) new = NULL;

    if (!old && !new)
	return 0;

    if (old && new) {
	assert(old->uid == new->uid);
	assert(old->modseq <= new->modseq);
	/* this flag cannot go away */
	if ((old->system_flags & FLAG_EXPUNGED))
	    assert((new->system_flags & FLAG_EXPUNGED));

	if (old->cid != new->cid) {
	    /* handle CID being renamed, by calling ourselves */
	    r = mailbox_update_conversations(mailbox, NULL, new);
	    if (!r)
		r = mailbox_update_conversations(mailbox, old, NULL);
	    return r;
	}
    }

    if (!old && new) {
	/* add the conversation */
	mailbox_cacherecord(mailbox, new); /* make sure it's loaded */
	r = message_update_conversations(cstate, new, &conv);
	if (r) return r;
	record = new;
    }
    else {
	record = new ? new : old;
	/* skip out on non-CIDed records */
	if (!record->cid) return 0;

	r = conversation_load(cstate, record->cid, &conv);
	if (r)
	    return r;
	if (!conv) {
	    if (!new) {
		/* We're trying to delete a conversation that's already
		 * gone...don't try to hard */
		syslog(LOG_NOTICE, "conversation "CONV_FMT" already "
				   "deleted, ignoring", record->cid);
		return 0;
	    }
	    conv = conversation_new(cstate);
	}
    }

    if (cstate->counted_flags)
	delta_counts = xzmalloc(sizeof(int) * cstate->counted_flags->count);

    /* calculate the changes */
    if (old) {
	/* decrease any relevent counts */
	if (!(old->system_flags & FLAG_EXPUNGED)) {
	    delta_exists--;
	    delta_size -= old->size;
	    /* drafts are never unseen */
	    if (!(old->system_flags & (FLAG_SEEN|FLAG_DRAFT)))
		delta_unseen--;
	    if (cstate->counted_flags) {
		for (i = 0; i < cstate->counted_flags->count; i++) {
		    const char *flag = strarray_nth(cstate->counted_flags, i);
		    if (mailbox_record_hasflag(mailbox, old, flag))
			delta_counts[i]--;
		}
	    }
	}
	delta_num_records--;
	modseq = MAX(modseq, old->modseq);
    }
    if (new) {
	/* add any counts */
	if (!(new->system_flags & FLAG_EXPUNGED)) {
	    delta_exists++;
	    delta_size += new->size;
	    /* drafts are never unseen */
	    if (!(new->system_flags & (FLAG_SEEN|FLAG_DRAFT)))
		delta_unseen++;
	    if (cstate->counted_flags) {
		for (i = 0; i < cstate->counted_flags->count; i++) {
		    const char *flag = strarray_nth(cstate->counted_flags, i);
		    if (mailbox_record_hasflag(mailbox, new, flag))
			delta_counts[i]++;
		}
	    }
	}
	delta_num_records++;
	modseq = MAX(modseq, new->modseq);
    }

    /* XXX - combine this with the earlier cache parsing */
    if (!mailbox_cacherecord(mailbox, record)) {
	char *env = NULL;
	char *envtokens[NUMENVTOKENS];
	struct address addr = { NULL, NULL, NULL, NULL, NULL, NULL };

	/* Need to find the sender */

	/* +1 -> skip the leading paren */
	env = xstrndup(cacheitem_base(record, CACHE_ENVELOPE) + 1,
		       cacheitem_size(record, CACHE_ENVELOPE) - 1);

	parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

	if (envtokens[ENV_FROM])
	    message_parse_env_address(envtokens[ENV_FROM], &addr);

	/* XXX - internaldate vs gmtime? */
	conversation_update_sender(conv,
				   addr.name, addr.route,
				   addr.mailbox, addr.domain,
				   record->gmtime, delta_exists);
	free(env);
    }

    conversation_update(cstate, conv, mailbox->name,
			delta_num_records,
			delta_exists, delta_unseen,
			delta_size, delta_counts, modseq);

    r = conversation_save(cstate, record->cid, conv);

    conversation_free(conv);
    free(delta_counts);
    return r;
}

EXPORTED int mailbox_get_xconvmodseq(struct mailbox *mailbox, modseq_t *modseqp)
{
    conv_status_t status = CONV_STATUS_INIT;
    int r;

    if (modseqp)
	*modseqp = 0;

    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    if (!mailbox->local_cstate)
	return IMAP_INTERNAL;

    r = conversation_getstatus(mailbox->local_cstate, mailbox->name, &status);
    if (r) return r;

    *modseqp = status.modseq;

    return 0;
}

/* Used in replication */
EXPORTED int mailbox_update_xconvmodseq(struct mailbox *mailbox, modseq_t newmodseq)
{
    conv_status_t status = CONV_STATUS_INIT;
    int r;

    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    if (!mailbox->local_cstate)
	return IMAP_INTERNAL;

    r = conversation_getstatus(mailbox->local_cstate, mailbox->name, &status);
    if (r) return r;

    if (newmodseq > status.modseq) {
	status.modseq = newmodseq;
	r = conversation_setstatus(mailbox->local_cstate, mailbox->name, &status);
    }

    return r;
}



/*
 * Rewrite an index record in a mailbox - updates all
 * necessary tracking fields automatically.
 */
EXPORTED int mailbox_rewrite_index_record(struct mailbox *mailbox,
				 struct index_record *record)
{
    int n;
    int r;
    struct index_record oldrecord;
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    size_t offset;
    int expunge_mode = config_getenum(IMAPOPT_EXPUNGE_MODE);
    int immediate = (expunge_mode == IMAP_ENUM_EXPUNGE_MODE_IMMEDIATE ||
		     expunge_mode == IMAP_ENUM_EXPUNGE_MODE_DEFAULT);

    assert(mailbox_index_islocked(mailbox, 1));
    assert(record->recno > 0 &&
	   record->recno <= mailbox->i.num_records);

    r = mailbox_read_index_record(mailbox, record->recno, &oldrecord);
    if (r) {
	syslog(LOG_ERR, "IOERROR: re-reading: %s %u",
	       mailbox->name, record->uid);
	return r;
    }

    /* the UID has to match, of course, for it to be the same
     * record.  XXX - test fields like "internaldate", etc here
     * too?  Maybe replication should be more strict about it */
    assert(record->uid == oldrecord.uid);
    assert(message_guid_equal(&oldrecord.guid, &record->guid));
    assert(record->modseq >= oldrecord.modseq);

    if (oldrecord.system_flags & FLAG_EXPUNGED) {
	/* it is a sin to unexpunge a message.  unexpunge.c copies
	 * the data from the old record and appends it with a new
	 * UID, which is righteous in the eyes of the IMAP client */
	assert(record->system_flags & FLAG_EXPUNGED);
    }

    /* handle immediate expunges here... */
    if (immediate && (record->system_flags & FLAG_EXPUNGED))
	record->system_flags |= FLAG_UNLINKED;

    /* make sure highestmodseq gets updated unless we're
     * being silent about it (i.e. marking an already EXPUNGED
     * message as UNLINKED, or just updating the content_lines
     * field or cache_offset) */
    if (record->silent) {
	mailbox_index_dirty(mailbox);
    }
    else {
	mailbox_modseq_dirty(mailbox);
	record->modseq = mailbox->i.highestmodseq;
	record->last_updated = mailbox->last_updated;
    }

    if (record->system_flags & FLAG_UNLINKED) {
	/* mark required actions */
	if (expunge_mode == IMAP_ENUM_EXPUNGE_MODE_IMMEDIATE)
	    mailbox->i.options |= OPT_MAILBOX_NEEDS_REPACK;
	mailbox->i.options |= OPT_MAILBOX_NEEDS_UNLINK;
    }
    else {
	/* write the cache record before buffering the message, it
	 * will set the cache_offset field. */
	r = mailbox_append_cache(mailbox, record);
	if (r) return r;
    }

    r = mailbox_update_conversations(mailbox, &oldrecord, record);
    if (r) return r;

    /* remove the counts for the old copy, and add them for
     * the new copy */

    mailbox_index_update_counts(mailbox, &oldrecord, 0);
    mailbox_index_update_counts(mailbox, record, 1);

    mailbox_index_record_to_buf(record, buf);

    offset = mailbox->i.start_offset +
	     (record->recno-1) * mailbox->i.record_size;

    n = lseek(mailbox->index_fd, offset, SEEK_SET);
    if (n == -1) {
	syslog(LOG_ERR, "IOERROR: seeking index record %u for %s: %m",
	       record->recno, mailbox->name);
	return IMAP_IOERROR;
    }

    n = retry_write(mailbox->index_fd, buf, INDEX_RECORD_SIZE);
    if (n != INDEX_RECORD_SIZE) {
	syslog(LOG_ERR, "IOERROR: writing index record %u for %s: %m",
	       record->recno, mailbox->name);
	return IMAP_IOERROR;
    }

    /* expunged tracking */
    if ((record->system_flags & FLAG_EXPUNGED) && 
	!(oldrecord.system_flags & FLAG_EXPUNGED)) {

	if (!mailbox->i.first_expunged ||
	    mailbox->i.first_expunged > record->last_updated)
	    mailbox->i.first_expunged = record->last_updated;

	mailbox_annot_update_counts(mailbox, &oldrecord, 0);

	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: expunge sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u> guid=<%s>",
		session_id(), mailbox->name, mailbox->uniqueid,
		record->uid, message_guid_encode(&record->guid));
    }

    return mailbox_refresh_index_map(mailbox);
}

/* append a single message to a mailbox - also updates everything
 * automatically.  These two functions are the ONLY way to modify
 * the contents or tracking fields of a message */
EXPORTED int mailbox_append_index_record(struct mailbox *mailbox,
				struct index_record *record)
{
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    size_t offset;
    int r;
    int n;
    struct utimbuf settime;
    uint32_t recno;

    assert(mailbox_index_islocked(mailbox, 1));

    /* Append MUST be a higher UID than any we've yet seen */
    assert(record->uid > mailbox->i.last_uid)

    /* Append MUST have a message with data */
    assert(record->size);

    /* GUID must not be null */
    assert(!message_guid_isnull(&record->guid));

    /* belt AND suspenders - check the previous record too */
    if (mailbox->i.num_records) {
	struct index_record prev;
	r = mailbox_read_index_record(mailbox, mailbox->i.num_records, &prev);
	if (r) return r;
	assert(prev.uid <= mailbox->i.last_uid);
	if (message_guid_equal(&prev.guid, &record->guid)) {
	    syslog(LOG_INFO, "%s: same message appears twice %u %u",
		   mailbox->name, prev.uid, record->uid);
	    /* but it's OK, we won't reject it */
	}
    }

    if (!record->internaldate)
	record->internaldate = time(NULL);
    if (!record->gmtime)
	record->gmtime = record->internaldate;
    if (!record->sentdate) {
	struct tm *tm = localtime(&record->internaldate);
	/* truncate to the day */
	tm->tm_sec = 0;
	tm->tm_min = 0;
	tm->tm_hour = 0;
	record->sentdate = mktime(tm);
    }

    /* update the highestmodseq if needed */
    if (record->silent) {
	mailbox_index_dirty(mailbox);
    }
    else {
	mailbox_modseq_dirty(mailbox);
	record->modseq = mailbox->i.highestmodseq;
	record->last_updated = mailbox->last_updated;
    }

    if (!(record->system_flags & FLAG_UNLINKED)) {
	/* make the file timestamp correct */
	settime.actime = settime.modtime = record->internaldate;
	if (utime(mailbox_message_fname(mailbox, record->uid), &settime) == -1)
	    return IMAP_IOERROR;

	/* write the cache record before buffering the message, it
	 * will set the cache_offset field. */
	r = mailbox_append_cache(mailbox, record);
	if (r) return r;
    }

    r = mailbox_update_conversations(mailbox, NULL, record);
    if (r) return r;

    /* add counts */
    mailbox_index_update_counts(mailbox, record, 1);

    mailbox_index_record_to_buf(record, buf);
    
    recno = mailbox->i.num_records + 1;

    offset = mailbox->i.start_offset +
	     ((recno - 1) * mailbox->i.record_size);

    n = lseek(mailbox->index_fd, offset, SEEK_SET);
    if (n == -1) {
	syslog(LOG_ERR, "IOERROR: seeking to append for %s: %m",
	       mailbox->name);
	return IMAP_IOERROR;
    }

    n = retry_write(mailbox->index_fd, buf, INDEX_RECORD_SIZE);
    if (n != INDEX_RECORD_SIZE) {
	syslog(LOG_ERR, "IOERROR: appending index record for %s: %m",
	       mailbox->name);
	return IMAP_IOERROR;
    }

    mailbox->i.last_uid = record->uid;
    mailbox->i.num_records = recno;
    mailbox->index_size += INDEX_RECORD_SIZE;

    if (config_auditlog)
	syslog(LOG_NOTICE, "auditlog: append sessionid=<%s> mailbox=<%s> uniqueid=<%s> uid=<%u> guid=<%s>",
	    session_id(), mailbox->name, mailbox->uniqueid, record->uid,
	    message_guid_encode(&record->guid));

    /* expunged tracking */
    if (record->system_flags & FLAG_EXPUNGED) {
	if (!mailbox->i.first_expunged ||
	    mailbox->i.first_expunged > record->last_updated)
	    mailbox->i.first_expunged = record->last_updated;

	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: expunge sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u> guid=<%s>",
		   session_id(), mailbox->name, mailbox->uniqueid,
		   record->uid, message_guid_encode(&record->guid));
    }

    /* yep, it could even be pre-unlinked in 'default' expunge mode, joy */
    if (record->system_flags & FLAG_UNLINKED) {
	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: unlink sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u>",
		   session_id(), mailbox->name, mailbox->uniqueid,
		   record->uid);
    }

    return mailbox_refresh_index_map(mailbox);
}

static void mailbox_message_unlink(struct mailbox *mailbox, uint32_t uid)
{
    const char *fname = mailbox_message_fname(mailbox, uid);
    int r;

    /* XXX - reports errors other than ENOENT ? */

    /* no error, we removed a file */
    if (unlink(fname) == 0) {
	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: unlink sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u>",
		   session_id(), mailbox->name, mailbox->uniqueid, uid);
    }

    r = mailbox_get_annotate_state(mailbox, uid, NULL);
    if (r) {
	syslog(LOG_ERR, "IOERROR: failed to open annotations %s %u: %s",
	       mailbox->name, uid, error_message(r));
	return;
    }

    r = annotate_msg_cleanup(mailbox, uid);
    if (r) {
	syslog(LOG_ERR, "IOERROR: failed to cleanup annotations %s %u: %s",
	       mailbox->name, uid, error_message(r));
	return;
    }
}

/* need a mailbox exclusive lock, we're removing files */
static int mailbox_index_unlink(struct mailbox *mailbox)
{
    struct index_record record;
    uint32_t recno;
    int r;

    syslog(LOG_INFO, "Unlinking files in mailbox %s", mailbox->name);

    /* note: this may try to unlink the same files more than once,
     * but them's the breaks - the alternative is yet another
     * system flag which gets updated once done! */
    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) return r;

	if (record.system_flags & FLAG_UNLINKED)
	    mailbox_message_unlink(mailbox, record.uid);
    }

    /* need to clear the flag, even if nothing needed unlinking! */
    mailbox_index_dirty(mailbox);
    mailbox->i.options &= ~OPT_MAILBOX_NEEDS_UNLINK;
    mailbox_commit(mailbox);

    return 0;
}

HIDDEN int mailbox_repack_setup(struct mailbox *mailbox,
			 struct mailbox_repack **repackptr)
{
    struct mailbox_repack *repack = xzmalloc(sizeof(struct mailbox_repack));
    const char *fname;
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    int n;

    /* init */
    repack->mailbox = mailbox;
    repack->i = mailbox->i; /* struct copy */
    repack->newindex_fd = -1;
    repack->newcache_fd = -1;

    /* new files */
    fname = mailbox_meta_newfname(mailbox, META_INDEX);
    repack->newindex_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (repack->newindex_fd == -1) goto fail;

    fname = mailbox_meta_newfname(mailbox, META_CACHE);
    repack->newcache_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (repack->newcache_fd == -1) goto fail;

    /* update the generation number */
    repack->i.generation_no++;

    /* zero out some values */
    repack->i.num_records = 0;
    repack->i.quota_mailbox_used = 0;
    repack->i.num_records = 0;
    /*
     * Note, we don't recalculate the mailbox' sync CRC on repack, because
     * the sync CRC may depend on annotation values which we don't want to
     * go looking up at this time.  A call to mailbox_index_recalc() will
     * however recalculate the sync CRC from scratch.
     */
    repack->i.answered = 0;
    repack->i.deleted = 0;
    repack->i.flagged = 0;
    repack->i.exists = 0;   
    repack->i.first_expunged = 0;
    repack->i.leaked_cache_records = 0;

    /* prepare initial header buffer */
    mailbox_index_header_to_buf(&repack->i, buf);

    /* write initial headers */
    n = retry_write(repack->newcache_fd, buf, 4);
    if (n == -1) goto fail;

    n = retry_write(repack->newindex_fd, buf, INDEX_HEADER_SIZE);
    if (n == -1) goto fail;    
    
    *repackptr = repack;
    return 0;

 fail:
    mailbox_repack_abort(&repack);
    return IMAP_IOERROR;
}

HIDDEN int mailbox_repack_add(struct mailbox_repack *repack,
		       struct index_record *record)
{
    int r;
    int n;
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;

    /* write out the new cache record - need to clear the cache_offset
     * so it gets reset in the new record */
    record->cache_offset = 0;
    r = cache_append_record(repack->newcache_fd, record);
    if (r) return r;

    /* update counters */
    header_update_counts(&repack->i, record, 1);

    /* write the index record out */
    mailbox_index_record_to_buf(record, buf);
    n = retry_write(repack->newindex_fd, buf, INDEX_RECORD_SIZE);
    if (n == -1)
	return IMAP_IOERROR;

    repack->i.num_records++;

    return 0;
}

/* clean up memory structures and abort repack */
HIDDEN void mailbox_repack_abort(struct mailbox_repack **repackptr)
{
    struct mailbox_repack *repack = *repackptr;
    if (!repack) return; /* safe against double-free */
    if (repack->newcache_fd != -1) close(repack->newcache_fd);
    unlink(mailbox_meta_newfname(repack->mailbox, META_CACHE));
    if (repack->newindex_fd != -1) close(repack->newindex_fd);
    unlink(mailbox_meta_newfname(repack->mailbox, META_INDEX));
    free(repack);
    *repackptr = NULL;
}

HIDDEN int mailbox_repack_commit(struct mailbox_repack **repackptr)
{
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    struct mailbox_repack *repack = *repackptr;
    int r = IMAP_IOERROR;

    assert(repack);

    repack->i.last_repack_time = time(0);

    assert(repack->i.sync_crc_vers == repack->mailbox->i.sync_crc_vers);
    assert(repack->i.sync_crc == repack->mailbox->i.sync_crc);

    /* rewrite the header with updated details */
    mailbox_index_header_to_buf(&repack->i, buf);

    if (lseek(repack->newindex_fd, 0, SEEK_SET) < 0)
	goto fail;

    if (retry_write(repack->newindex_fd, buf, INDEX_HEADER_SIZE) < 0)
	goto fail;

    /* ensure everything is committed to disk */
    if (fsync(repack->newindex_fd) < 0)
	goto fail;

    if (fsync(repack->newcache_fd) < 0)
	goto fail;

    close(repack->newcache_fd);
    repack->newcache_fd = -1;
    close(repack->newindex_fd);
    repack->newindex_fd = -1;

    /* rename index first - loader will handle un-renamed cache if
     * the generation is lower */
    r = mailbox_meta_rename(repack->mailbox, META_INDEX);
    if (r) goto fail;

    mailbox_meta_rename(repack->mailbox, META_CACHE);

    free(repack);
    *repackptr = NULL;
    return 0;

 fail:
    mailbox_repack_abort(repackptr);
    return r;
}

/* need a mailbox exclusive lock, we're rewriting files */
static int mailbox_index_repack(struct mailbox *mailbox)
{
    struct mailbox_repack *repack = NULL;
    uint32_t recno;
    struct index_record record;
    int r = IMAP_IOERROR;

    syslog(LOG_INFO, "Repacking mailbox %s", mailbox->name);

    r = mailbox_repack_setup(mailbox, &repack);
    if (r) goto fail;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) goto fail;

	/* been marked for removal, just skip */
	if (!record.uid) continue;

	/* we aren't keeping unlinked files, that's kind of the point */
	if (record.system_flags & FLAG_UNLINKED) {
	    /* just in case it was left lying around */
	    mailbox_message_unlink(mailbox, record.uid);

	    /* track the modseq for QRESYNC purposes */
	    if (record.modseq > repack->i.deletedmodseq)
		repack->i.deletedmodseq = record.modseq;

	    continue;
	}

	/* read in the old cache record */
	r = mailbox_cacherecord(mailbox, &record);
	if (r) goto fail;

	r = mailbox_repack_add(repack, &record);
	if (r) goto fail;
    }

    /* we unlinked any "needs unlink" in the process */
    repack->i.options &= ~(OPT_MAILBOX_NEEDS_REPACK|OPT_MAILBOX_NEEDS_UNLINK);

    r = mailbox_repack_commit(&repack);
    if (r) goto fail;

    return 0;

fail:
    mailbox_repack_abort(&repack);
    return r;
}

/*
 * Used by mailbox_rename() to expunge all messages in INBOX
 */
static unsigned expungeall(struct mailbox *mailbox __attribute__((unused)),
			   struct index_record *record __attribute__((unused)),
			   void *rock __attribute__((unused)))
{
    return 1;
}

/*
 * Expunge decision proc used by mailbox_expunge()
 * to expunge \Deleted messages.
 */
static unsigned expungedeleted(struct mailbox *mailbox __attribute__((unused)),
			       struct index_record *record,
			       void *rock __attribute__((unused)))
{
    if (record->system_flags & FLAG_DELETED)
	return 1;

    return 0;
}

/*
 * Perform an expunge operation on 'mailbox'.  If nonzero, the
 * function pointed to by 'decideproc' is called (with 'deciderock') to
 * determine which messages to expunge.  If 'decideproc' is a null pointer,
 * then messages with the \Deleted flag are expunged.
 */
EXPORTED int mailbox_expunge(struct mailbox *mailbox,
		    mailbox_decideproc_t *decideproc, void *deciderock,
		    unsigned *nexpunged)
{
    int r = 0;
    int numexpunged = 0;
    uint32_t recno;
    struct index_record record;

    assert(mailbox_index_islocked(mailbox, 1));

    /* anything to do? */
    if (!mailbox->i.num_records) {
	if (nexpunged) *nexpunged = 0;
	return 0;
    }

    if (!decideproc) decideproc = expungedeleted;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) continue;

	/* skip already expunged records */
	if (record.system_flags & FLAG_EXPUNGED)
	    continue;

	if (decideproc(mailbox, &record, deciderock)) {
	    numexpunged++;

	    /* mark deleted */
	    record.system_flags |= FLAG_EXPUNGED;

	    r = mailbox_rewrite_index_record(mailbox, &record);
	    if (r) return IMAP_IOERROR;
	}
    }

    if (numexpunged > 0) {
	syslog(LOG_NOTICE, "Expunged %d messages from %s",
	       numexpunged, mailbox->name);
    }

    if (nexpunged) *nexpunged = numexpunged;

    return 0;
}

EXPORTED int mailbox_expunge_cleanup(struct mailbox *mailbox, time_t expunge_mark,
			    unsigned *ndeleted)
{
    uint32_t recno;
    int dirty = 0;
    unsigned numdeleted = 0;
    struct index_record record;
    time_t first_expunged = 0;
    int r = 0;

    /* run the actual expunge phase */
    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	if (mailbox_read_index_record(mailbox, recno, &record))
	    continue;

	/* already unlinked, skip it (but dirty so we mark a repack is needed) */
	if (record.system_flags & FLAG_UNLINKED) {
	    dirty = 1;
	    continue;
	}

	/* not actually expunged, skip it */
	if (!(record.system_flags & FLAG_EXPUNGED))
	    continue;

	/* not stale enough yet, skip it - but track the updated time
	 * so we know when to run again */
	if (record.last_updated > expunge_mark) {
	    if (!first_expunged || (first_expunged > record.last_updated))
		first_expunged = record.last_updated;
	    continue;
	}

	dirty = 1;

	numdeleted++;

	record.system_flags |= FLAG_UNLINKED;
	record.silent = 1;
	if (mailbox_rewrite_index_record(mailbox, &record)) {
	    syslog(LOG_ERR, "IOERROR: failed to mark unlinked %s %u (recno %d)",
		   mailbox->name, record.uid, recno);
	    break;
	}
    }

    if (dirty) {
	mailbox_index_dirty(mailbox);
	mailbox->i.options |= OPT_MAILBOX_NEEDS_REPACK;
	mailbox->i.first_expunged = first_expunged;
    }

    if (ndeleted) *ndeleted = numdeleted;

    return r;
}

EXPORTED int mailbox_internal_seen(struct mailbox *mailbox, const char *userid)
{
    /* shared seen - everyone's state is internal */
    if (mailbox->i.options & OPT_IMAP_SHAREDSEEN)
	return 1;

    /* no username => use internal as well */
    if (!userid)
	return 1;

    /* otherwise the owner's seen state is internal */
    return mboxname_userownsmailbox(userid, mailbox->name);
}

/* returns a mailbox locked in MAILBOX EXCLUSIVE mode, so you
 * don't need to lock the index file to work with it :) */
EXPORTED int mailbox_create(const char *name,
		   const char *part,
		   const char *acl,
		   const char *uniqueid,
		   const char *specialuse,
		   int options,
		   unsigned uidvalidity,
		   modseq_t highestmodseq,
		   struct mailbox **mailboxptr)
{
    int r = 0;
    char quotaroot[MAX_MAILBOX_BUFFER];
    int hasquota;
    const char *fname;
    struct mailbox *mailbox = NULL;
    int n;
    uint32_t generation_buf;
    int createfnames[] = { META_INDEX, META_CACHE, META_HEADER, 0 };
    struct mailboxlist *listitem;
    strarray_t *initial_flags = NULL;

    /* if we already have this name open then that's an error too */
    listitem = find_listitem(name);
    if (listitem) return IMAP_MAILBOX_LOCKED;

    listitem = create_listitem(name);
    mailbox = &listitem->m;

    /* if we can't get an exclusive lock first try, there's something
     * racy going on! */
    r = mboxname_lock(name, &listitem->l, LOCK_NONBLOCKING);
    if (r) goto done;

    mailbox->part = xstrdup(part);
    mailbox->acl = xstrdup(acl);
    if (specialuse) mailbox->specialuse = xstrdup(specialuse);

    hasquota = quota_findroot(quotaroot, sizeof(quotaroot), name);

    /* ensure all paths exist */
    for (n = 0; createfnames[n]; n++) {
	fname = mailbox_meta_fname(mailbox, createfnames[n]);
	if (!fname) {
	    syslog(LOG_ERR, "IOERROR: Mailbox name too long (%s)", mailbox->name);
	    r = IMAP_MAILBOX_BADNAME;
	    goto done;
	}
	if (cyrus_mkdir(fname, 0755) == -1) {
	    syslog(LOG_ERR, "IOERROR: creating %s: %m", fname);
	    r = IMAP_IOERROR;
	    goto done;
	}
    }

    /* ensure we can fit the longest possible file name */
    fname = mailbox_message_fname(mailbox, UINT32_MAX);
    if (!fname) {
	syslog(LOG_ERR, "IOERROR: Mailbox name too long (%s)", mailbox->name);
	r = IMAP_MAILBOX_BADNAME;
	goto done;
    }
    /* and create the directory too :) */
    if (cyrus_mkdir(fname, 0755) == -1) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", fname);
	r = IMAP_IOERROR;
	goto done;
    }

    fname = mailbox_meta_fname(mailbox, META_INDEX);
    if (!fname) {
	syslog(LOG_ERR, "IOERROR: Mailbox name too long (%s)", mailbox->name);
	r = IMAP_MAILBOX_BADNAME;
	goto done;
    }
    mailbox->index_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (mailbox->index_fd == -1) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", fname);
	r = IMAP_IOERROR;
	goto done;
    }
    r = lock_blocking(mailbox->index_fd, fname);
    if (r) {
	syslog(LOG_ERR, "IOERROR: locking %s: %m", fname);
	r = IMAP_IOERROR;
	goto done;
    }
    mailbox->index_locktype = LOCK_EXCLUSIVE;
    r = mailbox_lock_conversations(mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: locking conversations %s %s",
	       mailbox->name, error_message(r));
	r = IMAP_IOERROR;
	goto done;
    }

    fname = mailbox_meta_fname(mailbox, META_CACHE);
    if (!fname) {
	syslog(LOG_ERR, "IOERROR: Mailbox name too long (%s)", mailbox->name);
	r = IMAP_MAILBOX_BADNAME;
	goto done;
    }
    mailbox->cache_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (mailbox->cache_fd == -1) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", fname);
	r = IMAP_IOERROR;
	goto done;
    }
        
    if (hasquota) {
	mailbox_set_quotaroot(mailbox, quotaroot);
	memset(mailbox->quota_previously_used, 0, sizeof(mailbox->quota_previously_used));
	mailbox->quota_dirty = 1;
    }

    /* ensure a UIDVALIDITY is set */
    if (!uidvalidity)
	uidvalidity = mboxname_nextuidvalidity(name, time(0));
    else
	mboxname_setuidvalidity(mailbox->name, uidvalidity);

    /* and highest modseq */
    if (!highestmodseq)
	highestmodseq = mboxname_nextmodseq(mailbox->name, 0);
    else
	mboxname_setmodseq(mailbox->name, highestmodseq);

    /* init non-zero fields */
    mailbox_index_dirty(mailbox);
    mailbox->i.minor_version = MAILBOX_MINOR_VERSION;
    mailbox->i.start_offset = INDEX_HEADER_SIZE;
    mailbox->i.record_size = INDEX_RECORD_SIZE;
    mailbox->i.options = options;
    mailbox->i.uidvalidity = uidvalidity;
    mailbox->i.highestmodseq = highestmodseq;
    mailbox->i.sync_crc_vers = MAILBOX_CRC_VERSION_MAX;

    /* initialise header size field so appends calculate the
     * correct map size */
    mailbox->index_size = INDEX_HEADER_SIZE;

    mailbox->header_dirty = 1;
    if (!uniqueid) {
	mailbox_make_uniqueid(mailbox);
    } else {
	mailbox->uniqueid = xstrdup(uniqueid);
    }

    /* pre-set any required permanent flags */
    if (config_getstring(IMAPOPT_MAILBOX_INITIAL_FLAGS)) {
	const char *val = config_getstring(IMAPOPT_MAILBOX_INITIAL_FLAGS);
	int i;

	initial_flags = strarray_split(val, NULL, 0);

	for (i = 0; i < initial_flags->count; i++) {
	    const char *flag = strarray_nth(initial_flags, i);
	    r = mailbox_user_flag(mailbox, flag, NULL, /*create*/1);
	    if (r) goto done;
	}
    }

    /* write out the initial generation number to the cache file */
    generation_buf = htonl(mailbox->i.generation_no);
    n = retry_write(mailbox->cache_fd, (char *)&generation_buf, 4);
    if (n != 4 || fsync(mailbox->cache_fd)) {
	syslog(LOG_ERR, "IOERROR: writing initial cache for %s: %m",
	       mailbox->name);
	r = IMAP_IOERROR;
	goto done;
    }

    r = seen_create_mailbox(NULL, mailbox);
    if (r) goto done;
    r = mailbox_commit(mailbox);
    if (r) goto done;

    if (config_auditlog)
	syslog(LOG_NOTICE, "auditlog: create sessionid=<%s> "
			   "mailbox=<%s> uniqueid=<%s>",
			   session_id(), 
			   mailbox->name, mailbox->uniqueid);

done:
    if (!r && mailboxptr)
	*mailboxptr = mailbox;
    else
	mailbox_close(&mailbox);

    strarray_free(initial_flags);

    return r;
}

/*
 * Remove all files in directory
 */
static void mailbox_delete_files(char *path)
{
    DIR *dirp;
    struct dirent *f;
    char buf[MAX_MAILBOX_PATH+1];
    char *tail;

    strlcpy(buf, path, sizeof(buf));

    if(strlen(buf) >= sizeof(buf) - 2) {
	syslog(LOG_ERR, "IOERROR: Path too long (%s)", buf);
	fatal("path too long", EC_OSFILE);
    }

    tail = buf + strlen(buf);
    *tail++ = '/';
    *tail = '\0';
    dirp = opendir(path);
    if (dirp) {
	while ((f = readdir(dirp))!=NULL) {
	    if (f->d_name[0] == '.'
		&& (f->d_name[1] == '\0'
		    || (f->d_name[1] == '.' &&
			f->d_name[2] == '\0'))) {
		/* readdir() can return "." or "..", and I got a bug report
		   that SCO might blow the file system to smithereens if we
		   unlink("..").  Let's not do that. */
		continue;
	    }

	    if(strlen(buf) + strlen(f->d_name) >= sizeof(buf)) {
		syslog(LOG_ERR, "IOERROR: Path too long (%s + %s)",
		       buf, f->d_name);
		fatal("Path too long", EC_OSFILE);
	    }
	    strcpy(tail, f->d_name);
	    unlink(buf);
	    *tail = '\0';
	}
	closedir(dirp);
    }
}

/* Callback for use by cmd_delete */
static int chkchildren(char *name,
		       int matchlen __attribute__((unused)),
		       int maycreate __attribute__((unused)),
		       void *rock)
{
    const char *part = (const char *)rock;
    struct mboxlist_entry *mbentry;
    int r;

    r = mboxlist_lookup(name, &mbentry, 0);
    if (r) return r;

    if (!strcmp(part, mbentry->partition))
	r = CYRUSDB_DONE;

    mboxlist_entry_free(&mbentry);

    return r;
}

EXPORTED int mailbox_add_conversations(struct mailbox *mailbox)
{
    struct index_record record;
    uint32_t recno;
    int r = 0;

    if (!mailbox_has_conversations(mailbox))
	return 0;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) return r;

	/* not assigned, skip */
	if (!record.cid)
	    continue;

	/* unlinked, skip */
	if (record.system_flags & FLAG_UNLINKED)
	    continue;

	r = mailbox_update_conversations(mailbox, NULL, &record);
	if (r) return r;
    }

    return 0;
}

static int mailbox_delete_conversations(struct mailbox *mailbox)
{
    struct conversations_state *cstate;
    struct index_record record;
    uint32_t recno;
    int r;

    if (!mailbox_has_conversations(mailbox))
	return 0;

    cstate = conversations_get_mbox(mailbox->name);
    if (!cstate)
	return IMAP_CONVERSATIONS_NOT_OPEN;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) return r;

	/* not assigned, skip */
	if (!record.cid)
	    continue;

	/* unlinked, skip */
	if (record.system_flags & FLAG_UNLINKED)
	    continue;

	r = mailbox_update_conversations(mailbox, &record, NULL);
	if (r) return r;
    }

    return conversations_rename_folder(cstate, mailbox->name, NULL);
}

static int mailbox_delete_internal(struct mailbox **mailboxptr)
{
    int r = 0;
    struct mailbox *mailbox = *mailboxptr;

    /* mark the quota removed */
    mailbox_quota_dirty(mailbox);

    /* mark the mailbox deleted */
    mailbox_index_dirty(mailbox);
    mailbox->i.options |= OPT_MAILBOX_DELETED;

    /* commit the changes */
    r = mailbox_commit(mailbox);
    if (r) return r;

    /* remove any seen */
    seen_delete_mailbox(NULL, mailbox);

    /* clean up annotations */
    r = annotate_delete_mailbox(mailbox);
    if (r) return r;

    /* can't unlink any files yet, because our promise to other
     * users of the mailbox applies! Can only unlink with an
     * exclusive lock.  mailbox_close will try to get one of 
     * those.
     */

    syslog(LOG_NOTICE, "Deleted mailbox %s", mailbox->name);

    if (config_auditlog)
	syslog(LOG_NOTICE, "auditlog: delete sessionid=<%s> "
			   "mailbox=<%s> uniqueid=<%s>",
			   session_id(), 
			   mailbox->name, mailbox->uniqueid);

    proc_killmbox(mailbox->name);

    mailbox_close(mailboxptr);

    return 0;
}

/*
 * Delete and close the mailbox 'mailbox'.  Closes 'mailbox' whether
 * or not the deletion was successful.  Requires a locked mailbox.
 */
EXPORTED int mailbox_delete(struct mailbox **mailboxptr)
{
    struct mailbox *mailbox = *mailboxptr;
    int r;

    r = mailbox_delete_conversations(mailbox);
    if (r) return r;

    return mailbox_delete_internal(mailboxptr);
}

/* XXX - move this part of cleanup into mboxlist.  Really
 * needs to be done with mailboxes.db locked so nobody can
 * try to create a mailbox while the delete is underway.
 * VERY tight race condition exists right now... */
/* we need an exclusive namelock for this */
HIDDEN int mailbox_delete_cleanup(const char *part, const char *name)
{
    char nbuf[MAX_MAILBOX_BUFFER];
    char pbuf[MAX_MAILBOX_PATH+1], mbuf[MAX_MAILBOX_PATH+1];
    char *ntail, *ptail, *mtail = NULL;
    char *path, *mpath;
    struct mboxlist_entry *mbentry;
    int r;

    /* XXX - use explicit paths to each type of file */

    /* Flush data (message file) directory */
    path = mboxname_datapath(part, name, 0);
    mailbox_delete_files(path);
    strlcpy(pbuf, path, sizeof(pbuf));
    ptail = pbuf + strlen(pbuf);

    /* Flush metadata directory */
    mpath = mboxname_metapath(part, name, 0, 0);
    if (strcmp(path, mpath)) {
	mailbox_delete_files(mpath);
	strlcpy(mbuf, mpath, sizeof(mbuf));
	mtail = mbuf + strlen(mbuf);
    }

    strlcpy(nbuf, name, sizeof(nbuf));
    ntail = nbuf + strlen(nbuf);

    do {
	/* Check if the mailbox has children */
	strcpy(ntail, ".*");
	r = mboxlist_findall(NULL, nbuf, 1, NULL, NULL, chkchildren, (void *)part);
	if (r != 0) break; /* We short-circuit with CYRUSDB_DONE */

	/* No children, remove mailbox spool dir(s) */
	if (rmdir(pbuf)) {
	    syslog(LOG_NOTICE,
		   "Remove of supposedly empty directory %s failed: %m",
		   pbuf);
	}
	ptail = strrchr(pbuf, '/');
	*ptail ='\0';

	if (mtail) {
	    if (rmdir(mbuf)) {
		syslog(LOG_NOTICE,
		       "Remove of supposedly empty directory %s failed: %m",
		       mbuf);
	    }
	    mtail = strrchr(mbuf, '/');
	    *mtail ='\0';
	}

	/* Check if parent mailbox exists */
	*ntail = '\0';
	ntail = strrchr(nbuf, '.');
	if (!ntail || strchr(ntail, '!')) {
	    /* Hit top of hierarchy or domain separator */
	    break;
	}
	*ntail = '\0';
	if (!strcmp(nbuf, "user") ||
	    ((ntail - nbuf > 5) && !strcmp(ntail-5, "!user"))) {
	    /* Hit top of 'user' hierarchy */
	    break;
	}

	r = mboxlist_lookup(nbuf, &mbentry, NULL);
	/* if it's not being moved, and not the same partition, then it's safe to
	 * clean up the parent directory too */
	if (!r) {
	    if (!(mbentry->mbtype & MBTYPE_MOVING) && strcmp(mbentry->partition, part))
		r = IMAP_MAILBOX_NONEXISTENT;
	    mboxlist_entry_free(&mbentry);
	}
    } while (r == IMAP_MAILBOX_NONEXISTENT);

    return 0;
}

struct meta_file {
    unsigned long metaflag;
    int optional;
    int nolink;
};

static struct meta_file meta_files[] = {
    { META_HEADER, 0, 1 },
    { META_INDEX,  0, 1 },
    { META_CACHE,  0, 1 },
    { META_SQUAT,  1, 0 },
    { META_ANNOTATIONS,  1, 0 },
    { 0, 0, 0 }
};

EXPORTED int mailbox_copy_files(struct mailbox *mailbox, const char *newpart,
		       const char *newname)
{
    char oldbuf[MAX_MAILBOX_PATH], newbuf[MAX_MAILBOX_PATH];
    struct meta_file *mf;
    uint32_t recno;
    struct index_record record;
    int r = 0;

    /* Copy over meta files */
    for (mf = meta_files; mf->metaflag; mf++) {
	struct stat sbuf;

	strncpy(oldbuf, mailbox_meta_fname(mailbox, mf->metaflag),
		MAX_MAILBOX_PATH);
	strncpy(newbuf, mboxname_metapath(newpart, newname, mf->metaflag, 0),
		MAX_MAILBOX_PATH);

	unlink(newbuf); /* Make link() possible */

	if (!mf->optional || stat(oldbuf, &sbuf) != -1) {
	    r = mailbox_copyfile(oldbuf, newbuf, mf->nolink);
	    if (r) return r;
	}
    }

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) return r;

	if (record.system_flags & FLAG_UNLINKED)
	    continue;

	strncpy(oldbuf, mailbox_message_fname(mailbox, record.uid),
		MAX_MAILBOX_PATH);
	strncpy(newbuf, mboxname_datapath(newpart, newname, record.uid),
		MAX_MAILBOX_PATH);

	r = mailbox_copyfile(oldbuf, newbuf, 0);
	if (r) return r;
    }

    return 0;
}

/* if 'userid' is set, we perform the funky RENAME INBOX INBOX.old
   semantics, regardless of whether or not the name of the mailbox is
   'user.foo'.*/
/* requires a write-locked oldmailbox pointer, since we delete it 
   immediately afterwards */
HIDDEN int mailbox_rename_copy(struct mailbox *oldmailbox,
			const char *newname,
			const char *newpartition,
			unsigned uidvalidity,
			const char *userid, int ignorequota,
			struct mailbox **newmailboxptr)
{
    int r;
    struct mailbox *newmailbox = NULL;
    struct conversations_state *oldcstate = NULL;
    struct conversations_state *newcstate = NULL;
    char *newquotaroot = NULL;

    assert(mailbox_index_islocked(oldmailbox, 1));

    /* we can't rename back from a deleted mailbox, because the conversations
     * information will be wrong.  Ideally we might re-calculate, but for now
     * we just throw a big fat error */
    if (mboxname_isdeletedmailbox(oldmailbox->name, NULL)) {
	syslog(LOG_ERR, "can't rename a deleted mailbox %s", oldmailbox->name);
	return IMAP_MAILBOX_BADNAME;
    }

    /* create uidvalidity if not explicitly requested */
    if (!uidvalidity)
	uidvalidity = mboxname_nextuidvalidity(newname, oldmailbox->i.uidvalidity);

    /* Create new mailbox */
    r = mailbox_create(newname, newpartition,
		       oldmailbox->acl, (userid ? NULL : oldmailbox->uniqueid),
		       oldmailbox->specialuse, oldmailbox->i.options,
		       uidvalidity, oldmailbox->i.highestmodseq, &newmailbox);

    if (r) return r;

    /* Check quota if necessary */
    if (!ignorequota && newmailbox->quotaroot &&
	strcmpsafe(oldmailbox->quotaroot, newmailbox->quotaroot)) {

	quota_t usage[QUOTA_NUMRESOURCES];
	mailbox_get_usage(oldmailbox, usage);
	r = mailbox_quota_check(newmailbox, usage);
	/* then we abort - no space to rename */
	if (r)
	    goto fail;
    }
    newquotaroot = xstrdupnull(newmailbox->quotaroot);

    r = mailbox_copy_files(oldmailbox, newpartition, newname);
    if (r) goto fail;

    /* Re-open index file  */
    r = mailbox_open_index(newmailbox);
    if (r) goto fail;

    /* Re-open header file */
    r = mailbox_read_index_header(newmailbox);
    if (r) goto fail;

    /* read in the flags */
    r = mailbox_read_header(newmailbox, NULL);
    if (r) goto fail;

    /* INBOX rename - change uniqueid */
    if (userid) mailbox_make_uniqueid(newmailbox);

    r = seen_copy(userid, oldmailbox, newmailbox);
    if (r) goto fail;

    /* copy any mailbox annotations */
    r = annotate_rename_mailbox(oldmailbox, newmailbox);
    if (r) goto fail;

    /* mark the "used" back to zero, so it updates the new quota! */
    mailbox_set_quotaroot(newmailbox, newquotaroot);
    mailbox_quota_dirty(newmailbox);
    memset(newmailbox->quota_previously_used, 0, sizeof(newmailbox->quota_previously_used));

    /* NOTE: in the case of renaming a user to another user, we
     * don't rename the conversations DB - instead we re-create
     * the records in the target user.  Sorry, was too complex
     * otherwise handling all the special cases */
    if (mailbox_has_conversations(oldmailbox)) {
	oldcstate = conversations_get_mbox(oldmailbox->name);
	assert(oldcstate);
    }

    if (mailbox_has_conversations(newmailbox)) {
	newcstate = conversations_get_mbox(newmailbox->name);
	assert(newcstate);
    }

    if (oldcstate && newcstate && !strcmp(oldcstate->path, newcstate->path)) {
	/* we can just rename within the same user */
	r = conversations_rename_folder(oldcstate, oldmailbox->name, newname);
    }
    else {
	/* have to handle each one separately */
	if (oldcstate)
	    r = mailbox_delete_conversations(oldmailbox);
	if (newcstate)
	    r = mailbox_add_conversations(newmailbox);
    }
    if (r) goto fail;

    /* commit the index changes */
    r = mailbox_commit(newmailbox);
    if (r) goto fail;

    if (config_auditlog)
	syslog(LOG_NOTICE, "auditlog: rename sessionid=<%s> "
			   "oldmailbox=<%s> newmailbox=<%s> uniqueid=<%s>",
			   session_id(), 
			   oldmailbox->name, newname, newmailbox->uniqueid);

    if (newmailboxptr) *newmailboxptr = newmailbox;
    else mailbox_close(&newmailbox);
    free(newquotaroot);

    return 0;

fail:
    /* first unlock so we don't need to write anything new down */
    mailbox_unlock_index(newmailbox, NULL);
    /* then remove all the files */
    mailbox_delete_cleanup(newmailbox->part, newmailbox->name);
    /* and finally, abort */
    mailbox_close(&newmailbox);
    free(newquotaroot);

    return r;
}

EXPORTED int mailbox_rename_cleanup(struct mailbox **mailboxptr, int isinbox)
{
    int r = 0;
    struct mailbox *oldmailbox = *mailboxptr;
    char *name = xstrdup(oldmailbox->name);

    if (isinbox) {
	/* Expunge old mailbox */
	r = mailbox_expunge(oldmailbox, expungeall, (char *)0, NULL);
	if (!r) r = mailbox_commit(oldmailbox);
	mailbox_close(mailboxptr);
    } else {
	r = mailbox_delete_internal(mailboxptr);
    }

    if (r) {
	syslog(LOG_CRIT,
	       "Rename Failure during mailbox_rename_cleanup (%s), " \
	       "potential leaked space (%s)", name,
	       error_message(r));
    }
    free(name);

    return r;
}

/*
 * Copy (or link) the file 'from' to the file 'to'
 */
EXPORTED int mailbox_copyfile(const char *from, const char *to, int nolink)
{
    int flags = COPYFILE_MKDIR;
    if (nolink) flags |= COPYFILE_NOLINK;

    if (cyrus_copyfile(from, to, flags))
	return IMAP_IOERROR;

    return 0;
}

/* ---------------------------------------------------------------------- */
/*                      RECONSTRUCT SUPPORT                               */
/* ---------------------------------------------------------------------- */

#define UIDGROW 300

struct found_uids {
    unsigned long *uids;
    unsigned nalloc;
    unsigned nused;
    unsigned pos;
};
#define FOUND_UIDS_INITIALIZER \
    { NULL, 0, 0, 0 }

static int sort_uid(const void *a, const void *b)
{
    return *(unsigned long *)a - *(unsigned long *)b;
}

static void add_found(struct found_uids *ff, unsigned long uid)
{
    /* make sure there's space */
    if (ff->nused >= ff->nalloc) {
	ff->nalloc += UIDGROW;
	ff->uids = xrealloc(ff->uids, ff->nalloc * sizeof(unsigned long));
    }
    ff->uids[ff->nused++] = uid;
}

static void free_found(struct found_uids *ff)
{
    free(ff->uids);
    ff->uids = NULL;
    ff->nalloc = 0;
    ff->nused = 0;
    ff->pos = 0;
}

static int parse_datafilename(const char *name, uint32_t *uidp)
{
    const char *p = name;

    /* must be at least one digit */
    if (!cyrus_isdigit(*p)) return IMAP_MAILBOX_BADNAME;
    do {
	p++;
    } while cyrus_isdigit(*p);

    /* has to end with a dot */
    if (*p != '.') return IMAP_MAILBOX_BADNAME;
    if (p[1]) return IMAP_MAILBOX_BADNAME;

    return parseuint32(name, &p, uidp);
}

static int find_files(struct mailbox *mailbox, struct found_uids *files,
		      int flags)
{
    const char *dirpath;
    DIR *dirp;
    struct dirent *dirent;
    uint32_t uid;
    const char *p;
    char buf[MAX_MAILBOX_PATH];
    struct stat sbuf;
    int r;

    dirpath = mailbox_datapath(mailbox);
    if (!dirpath) return IMAP_MAILBOX_BADNAME;

    dirp = opendir(dirpath);
    if (!dirp) {
	printf("%s data directory is missing %s\n", mailbox->name, dirpath);
	/* need to re-create data directory */
	if (cyrus_mkdir(dirpath, 0755) == -1)
	    return IMAP_IOERROR;
	if (mkdir(dirpath, 0755) == -1) 
	    return IMAP_IOERROR;
	return 0;
    }

    /* data directory is fine */
    while ((dirent = readdir(dirp)) != NULL) {
	p = dirent->d_name;
	if (*p == '.') continue; /* dot files */
	if (!strncmp(p, "cyrus.", 6)) continue; /* cyrus.* files */

	r = parse_datafilename(p, &uid);

	if (r) {
	    /* check if it's a directory */
	    snprintf(buf, MAX_MAILBOX_PATH, "%s/%s", dirpath, dirent->d_name);
	    if (stat(buf, &sbuf) == -1) continue; /* ignore ephemeral */
	    if (!S_ISDIR(sbuf.st_mode)) {
		if (!(flags & RECONSTRUCT_IGNORE_ODDFILES)) {
		    printf("%s odd file %s\n", mailbox->name, buf);
		    syslog(LOG_ERR, "%s odd file %s", mailbox->name, buf);
		    if (flags & RECONSTRUCT_REMOVE_ODDFILES)
			unlink(buf);
		    else {
			printf("run reconstruct with -O to remove odd files\n");
			syslog(LOG_ERR, "run reconstruct with -O to "
					"remove odd files");
		    }
		}
	    }
	}
	else {
	    /* it's one of ours :) */
	    add_found(files, uid);
	}
    }

    closedir(dirp);

    /* make sure UIDs are sorted for comparison */
    qsort(files->uids, files->nused, sizeof(unsigned long), sort_uid);

    return 0;
}

static void cleanup_stale_expunged(struct mailbox *mailbox)
{
    const char *fname;
    int expunge_fd = -1;
    const char *expunge_base = NULL;
    size_t expunge_len = 0;   /* mapped size */
    unsigned long expunge_num;
    unsigned long emapnum;
    uint32_t erecno;
    uint32_t uid;
    bit32 eoffset, expungerecord_size;
    const char *bufp;
    struct stat sbuf;
    int count = 0;
    int r;

    /* it's always read-writes */
    fname = mailbox_meta_fname(mailbox, META_EXPUNGE);
    expunge_fd = open(fname, O_RDWR, 0);
    if (expunge_fd == -1)
	goto done; /* yay, no crappy expunge file */

    /* boo - gotta read and find out the UIDs */
    r = fstat(expunge_fd, &sbuf);
    if (r == -1)
	goto done;

    if (sbuf.st_size < INDEX_HEADER_SIZE)
	goto done;

    map_refresh(expunge_fd, 1, &expunge_base,
		&expunge_len, sbuf.st_size, "expunge",
		mailbox->name);

    /* use the expunge file's header information just in case
     * versions are skewed for some reason */
    eoffset = ntohl(*((bit32 *)(expunge_base+OFFSET_START_OFFSET)));
    expungerecord_size = ntohl(*((bit32 *)(expunge_base+OFFSET_RECORD_SIZE)));

    /* bogus data at the start of the expunge file? */
    if (!eoffset || !expungerecord_size)
	goto done;

    expunge_num = ntohl(*((bit32 *)(expunge_base+OFFSET_NUM_RECORDS)));
    emapnum = (sbuf.st_size - eoffset) / expungerecord_size;
    if (emapnum < expunge_num) {
	expunge_num = emapnum;
    }

    /* add every UID to the files list */
    for (erecno = 1; erecno <= expunge_num; erecno++) {
	bufp = expunge_base + eoffset + (erecno-1)*expungerecord_size;
	uid = ntohl(*((bit32 *)(bufp+OFFSET_UID)));
	fname = mailbox_message_fname(mailbox, uid);
	unlink(fname);
	count++;
    }

    printf("%s removed %d records from stale cyrus.expunge\n",
	   mailbox->name, count);

    fname = mailbox_meta_fname(mailbox, META_EXPUNGE);
    unlink(fname);

done:
    if (expunge_base) map_free(&expunge_base, &expunge_len);
    if (expunge_fd != -1) close(expunge_fd);
}

/* this is kind of like mailbox_create, but we try to rescue
 * what we can from the filesystem! */
static int mailbox_reconstruct_create(const char *name, struct mailbox **mbptr)
{
    struct mailbox *mailbox = NULL;
    int options = config_getint(IMAPOPT_MAILBOX_DEFAULT_OPTIONS)
		| OPT_POP3_NEW_UIDL;
    struct mboxlist_entry *mbentry = NULL;
    struct mailboxlist *listitem;
    int r;

    /* make sure it's not already open.  Very odd, since we already
     * discovered it's not openable! */
    listitem = find_listitem(name);
    if (listitem) return IMAP_MAILBOX_LOCKED;

    listitem = create_listitem(name);
    mailbox = &listitem->m;

    /* if we can't get an exclusive lock first try, there's something
     * racy going on! */
    r = mboxname_lock(name, &listitem->l, LOCK_NONBLOCKING);
    if (r) goto done;

    /* Start by looking up current data in mailbox list */
    /* XXX - no mboxlist entry?  Can we recover? */
    r = mboxlist_lookup(name, &mbentry, NULL);
    if (r) goto done;

    mailbox->part = xstrdup(mbentry->partition);
    mailbox->acl = xstrdup(mbentry->acl);

    syslog(LOG_NOTICE, "create new mailbox %s", name);
 
    /* Attempt to open index */
    r = mailbox_open_index(mailbox);
    if (!r) r = mailbox_read_index_header(mailbox);
    if (r) {
	printf("%s: failed to read index header\n", mailbox->name);
	syslog(LOG_ERR, "failed to read index header for %s", mailbox->name);
	/* no cyrus.index file at all - well, we're in a pickle!
         * no point trying to rescue anything else... */
	mailbox_close(&mailbox);
	r = mailbox_create(name, mbentry->partition, mbentry->acl,
			   mbentry->specialuse, NULL, options, 0, 0, mbptr);
	mboxlist_entry_free(&mbentry);
	return r;
    }

    mboxlist_entry_free(&mbentry);

    /* read header, if it is not there, we need to create it */
    r = mailbox_read_header(mailbox, NULL);
    if (r) {
	/* Header failed to read - recreate it */
	printf("%s: failed to read header file\n", mailbox->name);
	syslog(LOG_ERR, "failed to read header file for %s", mailbox->name);

	mailbox_make_uniqueid(mailbox);
	r = mailbox_commit(mailbox);
	if (r) goto done;
    }

    if (mailbox->header_file_crc != mailbox->i.header_file_crc) {
	mailbox->i.header_file_crc = mailbox->header_file_crc;
	printf("%s: header file CRC mismatch, correcting\n", mailbox->name);
	syslog(LOG_ERR, "%s: header file CRC mismatch, correcting", mailbox->name);
	mailbox_index_dirty(mailbox);
	r = mailbox_commit(mailbox);
	if (r) goto done;
    }

done:
    if (r) mailbox_close(&mailbox);
    else *mbptr = mailbox;

    return r;
}

static int mailbox_reconstruct_acl(struct mailbox *mailbox, int flags)
{
    int make_changes = flags & RECONSTRUCT_MAKE_CHANGES;
    char *acl = NULL;
    int r;

    r = mailbox_read_header(mailbox, &acl);
    if (r) return r;

    if (strcmp(mailbox->acl, acl)) {
	printf("%s: update acl from header %s => %s\n", mailbox->name,
	       mailbox->acl, acl);
	if (make_changes) {
	    struct mboxlist_entry *mbentry = NULL;
	    r = mboxlist_lookup(mailbox->name, &mbentry, NULL);
	    if (!r) {
		mbentry->acl = acl;
		r = mboxlist_update(mbentry, 0);
	    }
	    mboxlist_entry_free(&mbentry);
	}
    }

    free(acl);

    return r;
}

static int records_match(const char *mboxname,
			 struct index_record *old,
			 struct index_record *new)
{
    int i;
    int match = 1;
    int userflags_dirty = 0;

    if (old->internaldate != new->internaldate) {
	printf("%s uid %u mismatch: internaldate\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->sentdate != new->sentdate) {
	printf("%s uid %u mismatch: sentdate\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->size != new->size) {
	printf("%s uid %u mismatch: size\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->header_size != new->header_size) {
	printf("%s uid %u mismatch: header_size\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->gmtime != new->gmtime) {
	printf("%s uid %u mismatch: gmtime\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->content_lines != new->content_lines) {
	printf("%s uid %u mismatch: content_lines\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (old->system_flags != new->system_flags) {
	printf("%s uid %u mismatch: systemflags\n",
	       mboxname, new->uid);
	match = 0;
    }
    for (i = 0; i < MAX_USER_FLAGS/32; i++) {
	if (old->user_flags[i] != new->user_flags[i])
	    userflags_dirty = 1;
    }
    if (userflags_dirty) {
	printf("%s uid %u mismatch: userflags\n",
	       mboxname, new->uid);
	match = 0;
    }
    if (!message_guid_equal(&old->guid, &new->guid)) {
	printf("%s uid %u mismatch: guid\n",
	       mboxname, new->uid);
	match = 0;
    }

    if (!match) {
	syslog(LOG_ERR, "%s uid %u record mismatch, rewriting",
	       mboxname, new->uid);
    }

    /* cache issues - don't print, probably just a version
     * upgrade... */
    if (old->cache_version != new->cache_version) {
	match = 0;
    }
    if (old->cache_crc != new->cache_crc) {
	match = 0;
    }
    if (cache_size(old) != cache_size(new)) {
	match = 0;
    }
    /* only compare cache records if size matches */
    else if (memcmp(cache_base(old), cache_base(new), cache_size(new))) {
	match = 0;
    }

    return match;
}

static int mailbox_reconstruct_compare_update(struct mailbox *mailbox,
					      struct index_record *record,
					      bit32 *valid_user_flags,
					      int flags, int have_file,
					      struct found_uids *discovered)
{
    char *fname = mailbox_message_fname(mailbox, record->uid);
    int r = 0;
    int i;
    struct index_record copy;
    struct stat sbuf;
    int make_changes = flags & RECONSTRUCT_MAKE_CHANGES;
    int re_parse = flags & RECONSTRUCT_ALWAYS_PARSE;
    int do_stat = flags & RECONSTRUCT_DO_STAT;
    int re_pack = 0;
    int did_stat = 0;

    /* does the file actually exist? */
    if (have_file && do_stat) {
    	if (stat(fname, &sbuf) == -1 || (sbuf.st_size == 0)) {
	    have_file = 0;
	}
	else if (record->size != (unsigned) sbuf.st_size) {
	    re_parse = 1;
	}
	did_stat = 1;
    }
	
    if (!have_file) {
	/* well, that's OK if it's supposed to be missing! */
	if (record->system_flags & FLAG_UNLINKED)
	    return 0;

	printf("%s uid %u not found\n", mailbox->name, record->uid);
	syslog(LOG_ERR, "%s uid %u not found", mailbox->name, record->uid);

	if (!make_changes) return 0;

	/* otherwise we have issues, mark it unlinked */
	unlink(fname);
	record->system_flags |= FLAG_EXPUNGED | FLAG_UNLINKED;
	mailbox->i.options |= OPT_MAILBOX_NEEDS_REPACK;
	return mailbox_rewrite_index_record(mailbox, record);
    }

    if (mailbox_cacherecord(mailbox, record) || record->crec.len == 0) {
	re_parse = 1;
	re_pack = 1; /* cache record will have to be rewritten */
    }

    /* copy once the cache record is read in... */
    copy = *record;

    if (!record->internaldate) {
	re_parse = 1;
    }

    /* re-calculate all the "derived" fields by parsing the file on disk */
    if (re_parse) {
	/* set NULL in case parse finds a new value */
	record->internaldate = 0;

	r = message_parse(fname, record);
	if (r) return r;

	/* unchanged, keep the old value */
	if (!record->internaldate)
	    record->internaldate = copy.internaldate;

	/* it's not the same message! */
	if (!message_guid_equal(&record->guid, &copy.guid)) {
	    int do_unlink = 0;

	    printf("%s uid %u guid mismatch\n",
		   mailbox->name, record->uid);
	    syslog(LOG_ERR, "%s uid %u guid mismatch",
		   mailbox->name, record->uid);

	    if (!make_changes) return 0;

	    if (record->system_flags & FLAG_EXPUNGED) {
		/* already expunged, just unlink it */
		printf("%s uid %u already expunged, unlinking\n",
		       mailbox->name, record->uid);
		syslog(LOG_ERR, "%s uid %u already expunged, unlinking",
		       mailbox->name, record->uid);
		do_unlink = 1;
	    }
	    else if (flags & RECONSTRUCT_GUID_REWRITE) {
		/* treat this file as discovered */
		add_found(discovered, record->uid);
		printf("%s uid %u marking for uid upgrade\n",
		       mailbox->name, record->uid);
		syslog(LOG_ERR, "%s uid %u marking for uid upgrade",
		       mailbox->name, record->uid);
		do_unlink = 1;
	    }
	    else if (flags & RECONSTRUCT_GUID_UNLINK) {
		printf("%s uid %u unlinking as requested with -U\n",
		       mailbox->name, record->uid);
		syslog(LOG_ERR, "%s uid %u unlinking as requested with -U",
		       mailbox->name, record->uid);
		do_unlink = 1;
	    }

	    if (do_unlink) {
		/* rewrite with the original so we don't break the
		 * expectation that GUID never changes */
		copy.system_flags |= FLAG_EXPUNGED | FLAG_UNLINKED;
		mailbox->i.options |= OPT_MAILBOX_NEEDS_UNLINK;
		return mailbox_rewrite_index_record(mailbox, &copy);
	    }

	    /* otherwise we just report it and move on - hopefully the
	     * correct file can be restored from backup or something */
	    printf("run reconstruct with -R to fix or -U to remove\n");
	    syslog(LOG_ERR, "run reconstruct with -R to fix or -U to remove");
	    return 0;
	}
    }

    /* get internaldate from the file if not set */
    if (!record->internaldate) {
	if (did_stat || stat(fname, &sbuf) != -1)
	    record->internaldate = sbuf.st_mtime;
	else
	    record->internaldate = time(NULL);
    }

    /* XXX - conditions under which modseq or uid or internaldate could be bogus? */
    if (record->modseq > mailbox->i.highestmodseq) {
	printf("%s uid %u future modseq " MODSEQ_FMT " found\n",
		   mailbox->name, record->uid, record->modseq);
	syslog(LOG_ERR, "%s uid %u future modseq " MODSEQ_FMT " found",
		   mailbox->name, record->uid, record->modseq);
	mailbox_index_dirty(mailbox);
	mailbox->i.highestmodseq = mboxname_setmodseq(mailbox->name,
						      record->modseq);
    }

    if (record->uid > mailbox->i.last_uid) {
	printf("%s future uid %u found\n",
	       mailbox->name, record->uid);
	syslog(LOG_ERR, "%s future uid %u found",
	       mailbox->name, record->uid);
	mailbox_index_dirty(mailbox);
	mailbox->i.last_uid = record->uid;
    }

    /* remove any user_flags that are missing from the header */
    for (i = 0; i < MAX_USER_FLAGS/32; i++) {
	record->user_flags[i] &= valid_user_flags[i];
    }

    /* after all this - if it still matches in every respect, we don't need
     * to rewrite the record - just return */
    if (records_match(mailbox->name, &copy, record))
	return 0;

    /* XXX - inform of changes */
    if (!make_changes)
	return 0;

    /* rewrite the cache record */
    if (re_pack || record->cache_crc != copy.cache_crc) {
	mailbox->i.options |= OPT_MAILBOX_NEEDS_REPACK;
	record->cache_offset = 0;
	r = mailbox_append_cache(mailbox, record);
	if (r) return r;
    }

    return mailbox_rewrite_index_record(mailbox, record);
}

static int mailbox_reconstruct_append(struct mailbox *mailbox, uint32_t uid,
				      int flags)
{
    char *fname = mailbox_message_fname(mailbox, uid);
    int r = 0;
    struct index_record record;
    struct stat sbuf;
    int make_changes = flags & RECONSTRUCT_MAKE_CHANGES;

    /* possible if '0.' file exists */
    if (!uid) {
	/* filthy hack - copy the path to '1.' and replace 1 with 0 */
	fname = xstrdup(mailbox_message_fname(mailbox, 1));
	fname[strlen(fname)-2] = '0';
    }

    if (stat(fname, &sbuf) == -1) r = IMAP_MAILBOX_NONEXISTENT;
    else if (sbuf.st_size == 0) r = IMAP_MAILBOX_NONEXISTENT;

    /* no file, nothing to do! */
    if (r) {
	syslog(LOG_ERR, "%s uid %u not found", mailbox->name, uid);
	printf("%s uid %u not found", mailbox->name, uid);
	if (!make_changes) return 0;
	unlink(fname);
	return 0;
    }

    memset(&record, 0, sizeof(struct index_record));

    r = message_parse(fname, &record);
    if (r) return r;

    if (uid > mailbox->i.last_uid) {
	printf("%s uid %u found - adding\n", mailbox->name, uid);
	syslog(LOG_ERR, "%s uid %u found - adding", mailbox->name, uid);
	record.uid = uid;
    }
    else {
	char *oldfname;
	char *newfname;

	printf("%s uid %u rediscovered - appending\n", mailbox->name, uid);
	syslog(LOG_ERR, "%s uid %u rediscovered - appending", mailbox->name, uid);
	/* XXX - check firstexpunged? */
	record.uid = mailbox->i.last_uid + 1;

	if (!make_changes) return 0;

	oldfname = xstrdup(fname);
	newfname = xstrdup(mailbox_message_fname(mailbox, record.uid));
	r = rename(oldfname, newfname);
	free(oldfname);
	free(newfname);
	if (r) return IMAP_IOERROR;
    }


    /* XXX - inform of changes */
    if (!make_changes)
	return 0;

    r = mailbox_append_index_record(mailbox, &record);

    /* XXX - copy per-message annotations? */

    return r;
}


static void reconstruct_compare_headers(struct mailbox *mailbox,
					struct index_header *old,
					struct index_header *new)
{
    if (old->quota_mailbox_used != new->quota_mailbox_used) {
	printf("%s updating quota_mailbox_used: "
	       QUOTA_T_FMT " => " QUOTA_T_FMT "\n", mailbox->name,
	       old->quota_mailbox_used, new->quota_mailbox_used);
	syslog(LOG_ERR, "%s updating quota_mailbox_used: "
	       QUOTA_T_FMT " => " QUOTA_T_FMT, mailbox->name,
	       old->quota_mailbox_used, new->quota_mailbox_used);
    }

    if (old->quota_annot_used != new->quota_annot_used) {
	printf("%s updating quota_annot_used: "
	       QUOTA_T_FMT " => " QUOTA_T_FMT "\n", mailbox->name,
	       old->quota_annot_used, new->quota_annot_used);
	syslog(LOG_ERR, "%s updating quota_annot_used: "
	       QUOTA_T_FMT " => " QUOTA_T_FMT, mailbox->name,
	       old->quota_annot_used, new->quota_annot_used);
    }

    if (old->answered != new->answered) {
	syslog(LOG_ERR, "%s: updating answered %u => %u",
	       mailbox->name, old->answered, new->answered);
	printf("%s: updating answered %u => %u\n",
	       mailbox->name, old->answered, new->answered);
    }

    if (old->flagged != new->flagged) {
	syslog(LOG_ERR, "%s: updating flagged %u => %u",
	       mailbox->name, old->flagged, new->flagged);
	printf("%s: updating flagged %u => %u\n",
	       mailbox->name, old->flagged, new->flagged);
    }

    if (old->deleted != new->deleted) {
	syslog(LOG_ERR, "%s: updating deleted %u => %u",
	       mailbox->name, old->deleted, new->deleted);
	printf("%s: updating deleted %u => %u\n",
	       mailbox->name, old->deleted, new->deleted);
    }

    if (old->exists != new->exists) {
	syslog(LOG_ERR, "%s: updating exists %u => %u",
	       mailbox->name, old->exists, new->exists);
	printf("%s: updating exists %u => %u\n",
	       mailbox->name, old->exists, new->exists);
    }

    if (old->sync_crc_vers != new->sync_crc_vers) {
	syslog(LOG_ERR, "%s: updating sync_crc_vers %u => %u",
	       mailbox->name, old->sync_crc_vers, new->sync_crc_vers);
	printf("%s: updating sync_crc_vers %u => %u\n",
	       mailbox->name, old->sync_crc_vers, new->sync_crc_vers);
    }
    else if (old->sync_crc != new->sync_crc) {
	/* note that the sync_crc can't be compared if the
	 * algorithm versions are different */
	syslog(LOG_ERR, "%s: updating sync_crc %u => %u",
	       mailbox->name, old->sync_crc, new->sync_crc);
	printf("%s: updating sync_crc %u => %u\n",
	       mailbox->name, old->sync_crc, new->sync_crc);
    }
}

static int mailbox_wipe_index_record(struct mailbox *mailbox,
				     struct index_record *record)
{
    int n;
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    size_t offset;

    assert(mailbox_index_islocked(mailbox, 1));
    assert(record->recno > 0 &&
	   record->recno <= mailbox->i.num_records);

    record->uid = 0;
    record->system_flags |= FLAG_EXPUNGED | FLAG_UNLINKED;

    mailbox->i.options |= OPT_MAILBOX_NEEDS_REPACK;
    mailbox_index_dirty(mailbox);

    mailbox_index_record_to_buf(record, buf);

    offset = mailbox->i.start_offset +
	     (record->recno-1) * mailbox->i.record_size;

    n = lseek(mailbox->index_fd, offset, SEEK_SET);
    if (n == -1) {
	syslog(LOG_ERR, "IOERROR: seeking index record %u for %s: %m",
	       record->recno, mailbox->name);
	return IMAP_IOERROR;
    }

    n = retry_write(mailbox->index_fd, buf, INDEX_RECORD_SIZE);
    if (n != INDEX_RECORD_SIZE) {
	syslog(LOG_ERR, "IOERROR: writing index record %u for %s: %m",
	       record->recno, mailbox->name);
	return IMAP_IOERROR;
    }

    return 0;
}

static int addannot_uid(const char *mailbox __attribute__((unused)),
                        uint32_t uid,
                        const char *entry __attribute__((unused)),
                        const char *userid __attribute__((unused)),
                        const struct buf *value __attribute__((unused)),
                        void *rock)
{
    struct found_uids *annots = (struct found_uids *)rock;

    /* take advantage of the guarantee that all annotations with the same UID
     * will be together in a 'foreach' response */
    if (!annots->nused || annots->uids[annots->nused-1] != uid) {
	add_found(annots, uid);
    }

    return 0;
}


static int find_annots(struct mailbox *mailbox, struct found_uids *annots)
{
    int r = 0;

    r = annotatemore_findall(mailbox->name, ANNOTATE_ANY_UID, "*",
			     addannot_uid, annots);
    if (r) return r;

    /* make sure UIDs are sorted for comparison */
    qsort(annots->uids, annots->nused, sizeof(unsigned long), sort_uid);

    return 0;
}

static int reconstruct_delannots(struct mailbox *mailbox,
				 struct found_uids *delannots,
				 int flags)
{
    int make_changes = (flags & RECONSTRUCT_MAKE_CHANGES);
    int r = 0;

    r = mailbox_get_annotate_state(mailbox, ANNOTATE_ANY_UID, NULL);
    if (r) {
	syslog(LOG_ERR, "IOERROR: failed to open annotations %s: %s",
	       mailbox->name, error_message(r));
	goto out;
    }

    while (delannots->pos < delannots->nused) {
	unsigned uid = delannots->uids[delannots->pos];
	syslog(LOG_NOTICE, "removing stale annotations for %u", uid);
	printf("removing stale annotations for %u\n", uid);
	if (make_changes) {
	    r = annotate_msg_cleanup(mailbox, uid);
	    if (r) goto out;
	}
	delannots->pos++;
    }

out:
    return r;
}


/*
 * Reconstruct the single mailbox named 'name'
 */
EXPORTED int mailbox_reconstruct(const char *name, int flags)
{
    /* settings */
    int make_changes = (flags & RECONSTRUCT_MAKE_CHANGES);

    int r = 0;
    int i, flag;
    struct index_record record;
    struct mailbox *mailbox = NULL;
    struct found_uids files = FOUND_UIDS_INITIALIZER;
    struct found_uids discovered = FOUND_UIDS_INITIALIZER;
    struct found_uids annots = FOUND_UIDS_INITIALIZER;
    struct found_uids delannots = FOUND_UIDS_INITIALIZER;
    struct index_header old_header;
    int have_file;
    uint32_t recno;
    uint32_t last_seen_uid = 0;
    bit32 valid_user_flags[MAX_USER_FLAGS/32];

    if (make_changes && !(flags & RECONSTRUCT_QUIET)) {
	syslog(LOG_NOTICE, "reconstructing %s", name);
    }

    r = mailbox_open_iwl(name, &mailbox);
    if (r) {
	if (!make_changes) return r;
	/* returns a locktype == LOCK_EXCLUSIVE mailbox */
	r = mailbox_reconstruct_create(name, &mailbox);
    }
    if (r) return r;

    r = mailbox_reconstruct_acl(mailbox, flags);
    if (r) goto close;

    /* Validate user flags */
    for (i = 0; i < MAX_USER_FLAGS/32; i++) {
	valid_user_flags[i] = 0;
    }
    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	if (!mailbox->flagname[flag]) continue;
	if ((flag && !mailbox->flagname[flag-1]) ||
	    !imparse_isatom(mailbox->flagname[flag])) {
	    printf("%s: bogus flag name %d:%s",
		   mailbox->name, flag, mailbox->flagname[flag]);
	    syslog(LOG_ERR, "%s: bogus flag name %d:%s",
		   mailbox->name, flag, mailbox->flagname[flag]);
	    mailbox->header_dirty = 1;
	    free(mailbox->flagname[flag]);
	    mailbox->flagname[flag] = NULL;
	    continue;
	}
	valid_user_flags[flag/32] |= 1<<(flag&31);
    }

    r = mailbox_ensure_cache(mailbox, 0);
    if (r) {
	const char *fname = mailbox_meta_fname(mailbox, META_CACHE);
	uint32_t buf;
	int n;

	printf("%s: missing cache file, recreating\n",
	      mailbox->name);
	syslog(LOG_ERR, "%s: missing cache file, recreating",
	      mailbox->name);

	if (!make_changes) goto close;

	if (cyrus_mkdir(fname, 0755)) goto close;
	mailbox->cache_fd = open(fname, O_RDWR|O_TRUNC|O_CREAT, 0666);
	if (mailbox->cache_fd == -1) goto close;

	/* set the generation number */
	buf = htonl(mailbox->i.generation_no);
	n = retry_write(mailbox->cache_fd, (char *)&buf, 4);
	if (n != 4) goto close;
    }

    /* find cyrus.expunge file if present */
    cleanup_stale_expunged(mailbox);

    r = find_files(mailbox, &files, flags);
    if (r) goto close;

    r = find_annots(mailbox, &annots);
    if (r) goto close;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) {
	    printf("%s: record corrupted %u (maybe uid %u)\n",
		   mailbox->name, recno, record.uid);
	    continue;
	}

	if (record.uid <= last_seen_uid) {
	    if (record.uid)
		syslog(LOG_ERR, "%s out of order uid %u at record %u, wiping",
		       mailbox->name, record.uid, recno);
	    mailbox_wipe_index_record(mailbox, &record);
	    continue;
	}

	last_seen_uid = record.uid;

	/* bogus annotations? */
	while (annots.pos < annots.nused && annots.uids[annots.pos] < record.uid) {
	    add_found(&delannots, annots.uids[annots.pos]);
	    annots.pos++;
	}

	/* skip over current */
	if (annots.pos < annots.nused && annots.uids[annots.pos] == record.uid) {
	    annots.pos++;
	}

	/* lower UID file exists */
	while (files.pos < files.nused && files.uids[files.pos] < record.uid) {
	    add_found(&discovered, files.uids[files.pos]);
	    files.pos++;
	}

	/* if they match, advance the pointer */
	have_file = 0;
	if (files.pos < files.nused && files.uids[files.pos] == record.uid) {
	    have_file = 1;
	    files.pos++;
	}

	r = mailbox_reconstruct_compare_update(mailbox, &record,
					       valid_user_flags,
					       flags, have_file,
					       &discovered);
	if (r) goto close;
    }

    /* add discovered messages before last_uid to the list in order */
    while (files.pos < files.nused && files.uids[files.pos] <= mailbox->i.last_uid) {
	add_found(&discovered, files.uids[files.pos]);
	files.pos++;
    }

    /* messages AFTER last_uid can keep the same UID (see also, restore
     * from lost .index file) - so don't bother moving those */
    while (files.pos < files.nused) {
	unsigned uid = files.uids[files.pos];
	r = mailbox_reconstruct_append(mailbox, files.uids[files.pos], flags);
	if (r) goto close;
	files.pos++;

	/* we can keep this annotation too... */

	/* bogus annotations? */
	while (annots.pos < annots.nused && annots.uids[annots.pos] < uid) {
	    add_found(&delannots, annots.uids[annots.pos]);
	    annots.pos++;
	}

	/* skip over current */
	if (annots.pos < annots.nused && annots.uids[annots.pos] == uid) {
	    annots.pos++;
	}
    }

    /* bogus annotations after the end? */
    while (annots.pos < annots.nused) {
	add_found(&delannots, annots.uids[annots.pos]);
	annots.pos++;
    }
    
    /* handle new list - note, we don't copy annotations for these */
    while (discovered.pos < discovered.nused) {
	r = mailbox_reconstruct_append(mailbox, discovered.uids[discovered.pos], flags);
	if (r) goto close;
	discovered.pos++;
    }

    if (delannots.nused) {
	r = reconstruct_delannots(mailbox, &delannots, flags);
	if (r) goto close;
    }

    /* make sure we have enough index file mmaped */
    r = mailbox_refresh_index_map(mailbox);

    old_header = mailbox->i;

    /* re-calculate derived fields */
    r = mailbox_index_recalc(mailbox);
    if (r) goto close;

    /* inform users of any changed header fields */
    reconstruct_compare_headers(mailbox, &old_header, &mailbox->i);

    /* fix up 2.4.0 bug breakage */
    if (!mailbox->i.uidvalidity) {
	if (make_changes) {
	    mailbox->i.uidvalidity = mboxname_nextuidvalidity(mailbox->name,
							      time(0));
	    mailbox_index_dirty(mailbox);
	}
	syslog(LOG_ERR, "%s: zero uidvalidity", mailbox->name);
    }
    if (!mailbox->i.highestmodseq) {
	if (make_changes) {
	    mailbox_index_dirty(mailbox);
	    mailbox->i.highestmodseq = mboxname_nextmodseq(mailbox->name, 0);
	}
	syslog(LOG_ERR, "%s:  zero highestmodseq", mailbox->name);
    }

    if (make_changes) {
	r = mailbox_commit(mailbox);
    }
    else {
	/* undo any dirtyness before we close, we didn't actually
	 * write any changes */
	mailbox->i.dirty = 0;
	mailbox->quota_dirty = 0;
	mailbox->cache_dirty = 0;
	mailbox->modseq_dirty = 0;
	mailbox->header_dirty = 0;
    }

close:
    free_found(&files);
    free_found(&discovered);
    free_found(&annots);
    free_found(&delannots);
    mailbox_close(&mailbox);
    return r;
}

/*
 * Gets messages usage.
 */
EXPORTED void mailbox_get_usage(struct mailbox *mailbox,
			quota_t usage[QUOTA_NUMRESOURCES])
{
    int res;

    for (res = 0; res < QUOTA_NUMRESOURCES; res++) {
	usage[res] = 0;
    }

    if (!(mailbox->i.options & OPT_MAILBOX_DELETED)) {
	usage[QUOTA_STORAGE] = mailbox->i.quota_mailbox_used;
	usage[QUOTA_MESSAGE] = mailbox->i.exists;
	usage[QUOTA_ANNOTSTORAGE] = mailbox->i.quota_annot_used;
	usage[QUOTA_NUMFOLDERS] = 1;
    }
    /* else: mailbox is being deleted, thus its new usage is 0 */
}

EXPORTED int mailbox_get_annotate_state(struct mailbox *mailbox,
			       unsigned int uid,
			       annotate_state_t **statep)
{
    int r = 0;

    if (statep) *statep = NULL;

    if (!mailbox->annot_state)
	mailbox->annot_state = annotate_state_new();

    r = annotate_state_set_message(mailbox->annot_state, mailbox, uid);
    if (r) return r;

    /* lock immediately if we have a write lock */
    if (mailbox_index_islocked(mailbox, /*write*/1))
	annotate_state_begin(mailbox->annot_state);

    if (statep) *statep = mailbox->annot_state;

    return 0;
}

int mailbox_cid_rename(struct mailbox *mailbox,
		       conversation_id_t from_cid,
		       conversation_id_t to_cid)
{
    uint32_t recno, num_records;
    struct index_record record;
    int r;

    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    num_records = mailbox->i.num_records;
    for (recno = 1; recno <= num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) {
	    syslog(LOG_ERR, "mailbox_cid_rename: error "
			    "reading record %u, mailbox %s: %s",
			    recno, mailbox->name, error_message(r));
	    return r;
	}

	if (record.system_flags & FLAG_EXPUNGED)
	    continue;
	if (record.cid != from_cid)
	    continue;

	/*
	 * Just rename the CID in place - injecting a copy at the end
	 * messes with clients that just use UID ordering, like Apple's
	 * IOS email client */

	record.cid = to_cid;
	r = mailbox_rewrite_index_record(mailbox, &record);

	if (r) {
	    syslog(LOG_ERR, "mailbox_cid_rename: error "
			    "rewriting record %u, mailbox %s: %s from %llu to %llu",
			    recno, mailbox->name, error_message(r), from_cid, to_cid);
	    return r;
	}
    }

    return 0;
}
