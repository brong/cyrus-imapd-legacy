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

#include "acl.h"
#include "assert.h"
#include "crc32.h"
#include "exitcodes.h"
#include "global.h"
#include "imap_err.h"
#include "imparse.h"
#include "cyr_lock.h"
#include "mailbox.h"
#include "message.h"
#include "map.h"
#include "mboxlist.h"
#include "parseaddr.h"
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

#ifdef HAVE_GPB
#include "mailbox_update_notifier.h"
#endif

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
static int mailbox_post_action(const char *name, const struct buf *);
static void mailbox_execute_actions_file(struct mailbox *mailbox,
				         FILE *fp, const char *fname);
static int mailbox_execute_actions(struct mailbox *mailbox);

static struct mailboxlist *create_listitem(const char *name)
{
    struct mailboxlist *item = xmalloc(sizeof(struct mailboxlist));
    item->next = open_mailboxes;
    open_mailboxes = item;

    item->nopen = 1;
    item->l = NULL;
    zeromailbox(item->m);
    item->m.name = xstrdup(name);

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

char *mailbox_meta_fname(struct mailbox *mailbox, int metafile)
{
    static char fnamebuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_metapath(mailbox->part, mailbox->name, metafile, 0);
    if (!src) return NULL;

    strncpy(fnamebuf, src, MAX_MAILBOX_PATH);
    return fnamebuf;
}

char *mailbox_meta_newfname(struct mailbox *mailbox, int metafile)
{
    static char fnamebuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_metapath(mailbox->part, mailbox->name, metafile, 1);
    if (!src) return NULL;

    strncpy(fnamebuf, src, MAX_MAILBOX_PATH);
    return fnamebuf;
}

int mailbox_meta_rename(struct mailbox *mailbox, int metafile)
{
    char *fname = mailbox_meta_fname(mailbox, metafile);
    char *newfname = mailbox_meta_newfname(mailbox, metafile);

    if (rename(newfname, fname))
	return IMAP_IOERROR;

    return 0;
}

char *mailbox_message_fname(struct mailbox *mailbox, unsigned long uid)
{
    static char localbuf[MAX_MAILBOX_PATH];
    const char *src;

    src = mboxname_datapath(mailbox->part, mailbox->name, uid);
    if (!src) return NULL;

    strncpy(localbuf, src, MAX_MAILBOX_PATH);
    return localbuf;
}

char *mailbox_datapath(struct mailbox *mailbox)
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
unsigned mailbox_cached_header(const char *s) 
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
unsigned mailbox_cached_header_inline(const char *text)
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

const char *cacheitem_base(struct index_record *record, int field)
{
    const char *base = record->crec.base->s;
    return base + record->crec.item[field].offset;
}

unsigned cacheitem_size(struct index_record *record, int field)
{
    return record->crec.item[field].len;
}

struct buf *cacheitem_buf(struct index_record *record, int field)
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
	syslog(LOG_ERR, "IOERROR: offset greater than cache size");
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
	    syslog(LOG_ERR, "IOERROR: offset greater than cache size");
	    return IMAP_IOERROR;
	}
    }

    /* all fit within the cache, it's gold as far as we can tell */
    crec->base = cachebase;
    crec->len = offset - cache_offset;
    crec->offset = cache_offset;

    return 0;
}

int mailbox_open_cache(struct mailbox *mailbox)
{
    struct stat sbuf;
    unsigned generation;
    int retry = 0;
    int openflags = mailbox->is_readonly ? O_RDONLY : O_RDWR;

    /* already got everything? great */
    if (mailbox->cache_fd != -1 && !mailbox->need_cache_refresh)
	return 0;

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
    }

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

    mailbox->need_cache_refresh = 0;

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

    mailbox->need_cache_refresh = 0;
    return 0;
}

int mailbox_index_islocked(struct mailbox *mailbox, int write)
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
    r = mailbox_open_cache(mailbox);
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
    mailbox->need_cache_refresh = 1;

    return 0;
}

int mailbox_cacherecord(struct mailbox *mailbox,
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

    r = mailbox_open_cache(mailbox);
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

int mailbox_commit_cache(struct mailbox *mailbox)
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
void mailbox_set_updatenotifier(mailbox_notifyproc_t *notifyproc)
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

/* create the unique identifier for a mailbox named 'name' with
 * uidvalidity 'uidvalidity'.  'uniqueid' should be at least 17 bytes
 * long.  the unique identifier is just the mailbox name hashed to 32
 * bits followed by the uid, both converted to hex. 
 */
#define PRIME (2147484043UL)

void mailbox_make_uniqueid(struct mailbox *mailbox)
{
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

    mailbox->header_dirty = 1;
}

/*
 * Maps in the content for the message with UID 'uid' in 'mailbox'.
 * Returns map in 'basep' and 'lenp'
 */
int mailbox_map_message(struct mailbox *mailbox, unsigned long uid,
			const char **basep, unsigned long *lenp)
{
    int msgfd;
    char *fname;
    struct stat sbuf;

    fname = mailbox_message_fname(mailbox, uid);

    msgfd = open(fname, O_RDONLY, 0666);
    if (msgfd == -1) return errno;

    if (fstat(msgfd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on %s: %m", fname);
	fatal("can't fstat message file", EC_OSFILE);
    }
    *basep = 0;
    *lenp = 0;
    map_refresh(msgfd, 1, basep, lenp, sbuf.st_size, fname, mailbox->name);
    close(msgfd);

    return 0;
}

/*
 * Releases the buffer obtained from mailbox_map_message()
 */
void mailbox_unmap_message(struct mailbox *mailbox __attribute__((unused)),
			   unsigned long uid __attribute__((unused)),
			   const char **basep, unsigned long *lenp)
{
    map_free(basep, lenp);
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
}

/*
 * Open the index file for 'mailbox'
 */
int mailbox_open_index(struct mailbox *mailbox)
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

int mailbox_mboxlock_reopen(struct mailboxlist *listitem, int locktype)
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
    r = mailbox_lock_index(mailbox, index_locktype);
    if (r) {
	syslog(LOG_ERR, "IOERROR: locking index %s: %s",
	       mailbox->name, error_message(r));
	goto done;
    }

    /* we may be in the process of deleting this mailbox */
    if (mailbox->i.options & OPT_MAILBOX_DELETED) {
	r = IMAP_MAILBOX_NONEXISTENT;
	goto done;
    }

    if (index_locktype == LOCK_EXCLUSIVE) {
	r = mailbox_execute_actions(mailbox);
	if (r) {
	    syslog(LOG_ERR, "Failed to perform delayed open "
			    "actions on mailbox %s", mailbox->name);
	    goto done;
	}
    }

done:
    if (r) mailbox_close(&mailbox);
    else *mailboxptr = mailbox;

    return r;
}

int mailbox_open_irl(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_SHARED, LOCK_SHARED,
				 mailboxptr);
}

int mailbox_open_iwl(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_SHARED, LOCK_EXCLUSIVE,
				 mailboxptr);
}

int mailbox_open_exclusive(const char *name, struct mailbox **mailboxptr)
{
    return mailbox_open_advanced(name, LOCK_EXCLUSIVE, LOCK_EXCLUSIVE,
				 mailboxptr);
}

void mailbox_index_dirty(struct mailbox *mailbox)
{
    assert(mailbox_index_islocked(mailbox, 1));
    mailbox->i.dirty = 1;
}

void mailbox_modseq_dirty(struct mailbox *mailbox)
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

/*
 * Close the mailbox 'mailbox', freeing all associated resources.
 */
void mailbox_close(struct mailbox **mailboxptr)
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
	if (!r) r = mailbox_open_index(mailbox);
	if (!r) r = mailbox_lock_index(mailbox, LOCK_EXCLUSIVE);
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
int mailbox_read_header(struct mailbox *mailbox, char **aclptr)
{
    int r = 0;
    int flag;
    const char *name, *p, *tab, *eol;
    const char *fname;
    struct stat sbuf;
    const char *base = NULL;
    unsigned long len = 0;
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
int mailbox_set_acl(struct mailbox *mailbox, const char *acl,
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
int mailbox_set_quotaroot(struct mailbox *mailbox, const char *quotaroot)
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
int mailbox_set_specialuse(struct mailbox *mailbox, const char *specialuse)
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
int mailbox_user_flag(struct mailbox *mailbox, const char *flag,
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

    *flagnum = userflag;

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

    return ((record->user_flags[userflag/32] | 1<<(userflag&31)) ? 1 : 0);
}

int mailbox_buf_to_index_header(const char *buf, struct index_header *i)
{
    uint32_t crc;

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
    /* sync_crc was here */
    i->recentuid = ntohl(*((bit32 *)(buf+OFFSET_RECENTUID)));
    i->recenttime = ntohl(*((bit32 *)(buf+OFFSET_RECENTTIME)));
    i->header_crc = ntohl(*((bit32 *)(buf+OFFSET_HEADER_CRC)));
    i->pop3_show_after = ntohl(*((bit32 *)(buf+OFFSET_POP3_SHOW_AFTER)));

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

	/* need to map some more space! */
	map_refresh(mailbox->index_fd, 1, &mailbox->index_base,
		    &mailbox->index_len, mailbox->index_size,
		    "index", mailbox->name);

	/* and the cache will be stale too */
	mailbox->need_cache_refresh = 1;
    }

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
int mailbox_buf_to_index_record(const char *buf,
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
int mailbox_read_index_record(struct mailbox *mailbox,
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

int mailbox_lock_conversations(struct mailbox *mailbox)
{
    /* not needed */
    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    /* already locked */
    if (conversations_get_mbox(mailbox->name))
	return 0;

    return conversations_open_mbox(mailbox->name, &mailbox->local_cstate);
}

/*
 * bsearch() function to compare two index record buffers by UID
 */
static int rec_compar(const void *key, const void *mem)
{
    uint32_t uid = *((uint32_t *) key);
    struct index_record record;
    int r;

    if ((r = mailbox_buf_to_index_record(mem, &record))) return r;

    if (uid < record.uid) return -1;
    return (uid > record.uid);
}

/*
 * Find the index record in mailbox corresponding to UID
 */
int mailbox_find_index_record(struct mailbox *mailbox, uint32_t uid,
			      struct index_record *record)
{
    const void *mem, *base = mailbox->index_base + mailbox->i.start_offset;
    size_t num_records = mailbox->i.num_records;
    size_t size = mailbox->i.record_size;
    int r;

    mem =  bsearch(&uid, base, num_records, size, rec_compar);
    if (!mem) return CYRUSDB_NOTFOUND;

    if ((r = mailbox_buf_to_index_record(mem, record))) return r;

    record->recno = ((mem - base) / size) + 1;

    return 0;
}

/*
 * Lock the index file for 'mailbox'.  Reread index file header if necessary.
 */
int mailbox_lock_index(struct mailbox *mailbox, int locktype)
{
    char *fname;
    struct stat sbuf;
    int r = 0;

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
	if (!r) r = lock_blocking(mailbox->index_fd);
    }
    else if (locktype == LOCK_SHARED) {
	r = lock_shared(mailbox->index_fd);
    }
    else {
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
	    lock_unlock(mailbox->index_fd);
    }

    if (r) {
	syslog(LOG_ERR, "IOERROR: locking index for %s: %s",
	       mailbox->name, error_message(r));
	return IMAP_IOERROR;
    }

    mailbox->index_locktype = locktype;

    fname = mailbox_meta_fname(mailbox, META_HEADER);
    r = stat(fname, &sbuf);
    if (r == -1) {
	syslog(LOG_ERR, "IOERROR: stating header %s for %s: %m",
	       fname, mailbox->name);
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

	    if (prev_locktype != LOCK_EXCLUSIVE) {
		/* we need to switch to an exclusive lock while upgrading */
		r = mailbox_mboxlock_reopen(listitem, LOCK_EXCLUSIVE);
		if (r) return r;
		r = mailbox_open_index(mailbox);
		if (r) return r;
	    }

	    /* lie about our index lock status - the exclusive namelock
	     * provides equivalent properties - and we know it won't
	     * leak because the 'restart' above will cover up our sins */
	    mailbox->index_locktype = LOCK_EXCLUSIVE;
	    r = upgrade_index(mailbox);
	    if (r) return r;

	    /* we have to downgrade again afterwards so a "SELECT" won't
	     * hold an exclusive lock forever */
	    if (prev_locktype != LOCK_EXCLUSIVE) {
		r = mailbox_mboxlock_reopen(listitem, prev_locktype);
		if (r) return r;
	    }
	    /* either way, must refresh index here.  The old one is stale */
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

    /* fix up 2.4.0 bug breakage */
    if (!mailbox->i.uidvalidity) {
	mailbox->i.uidvalidity = mboxname_nextuidvalidity(mailbox->name,
							  time(0));
	if (locktype == LOCK_EXCLUSIVE) {
	    mailbox_index_dirty(mailbox);
	    mailbox_commit(mailbox);
	    syslog(LOG_ERR, "%s: fixing zero uidvalidity", mailbox->name);
	}
    }
    if (!mailbox->i.highestmodseq) {
	mailbox->i.highestmodseq = mboxname_nextmodseq(mailbox->name, 0);
	if (locktype == LOCK_EXCLUSIVE) {
	    mailbox_index_dirty(mailbox);
	    mailbox_commit(mailbox);
	    syslog(LOG_ERR, "%s: fixing zero highestmodseq", mailbox->name);
	}
    }

    return 0;
}

/*
 * Release lock on the index file for 'mailbox'
 */
void mailbox_unlock_index(struct mailbox *mailbox, struct statusdata *sdata)
{
    /* naughty - you can't unlock a dirty mailbox! */
    int r = mailbox_commit(mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: failed to commit mailbox %s, "
	       "probably need to reconstruct",
	       mailbox->name);
	abort();
    }

    if (mailbox->has_changed) {
	if (updatenotifier) updatenotifier(mailbox->name);
	sync_log_mailbox(mailbox->name);
	if (config_getswitch(IMAPOPT_STATUSCACHE))
	    statuscache_invalidate(mailbox->name, sdata);

#ifdef HAVE_GPB
	if (config_getstring(IMAPOPT_MAILBOX_UPDATE_NOTIFIER_SOCKET))
	    send_push_notification(mailbox);
#endif

	mailbox->has_changed = 0;
    }

    if (mailbox->index_locktype) {
	if (lock_unlock(mailbox->index_fd))
	    syslog(LOG_ERR, "IOERROR: unlocking index of %s: %m", 
		mailbox->name);
	mailbox->index_locktype = 0;
    }

    if (mailbox->local_cstate) {
	int r = conversations_commit(&mailbox->local_cstate);
	if (r)
	    syslog(LOG_ERR, "Error committing to conversations database for mailbox %s: %s",
		   mailbox->name, error_message(r));
    }
}

/*
 * Write the header file for 'mailbox'
 */
int mailbox_commit_header(struct mailbox *mailbox)
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

bit32 mailbox_index_header_to_buf(struct index_header *i, unsigned char *buf)
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
    /* sync_crc was here */
    *((bit32 *)(buf+OFFSET_RECENTUID)) = htonl(i->recentuid);
    *((bit32 *)(buf+OFFSET_RECENTTIME)) = htonl(i->recenttime);
    *((bit32 *)(buf+OFFSET_POP3_SHOW_AFTER)) = htonl(i->pop3_show_after);
    *((bit32 *)(buf+OFFSET_SPARE1)) = htonl(0); /* RESERVED */
    *((bit32 *)(buf+OFFSET_SPARE2)) = htonl(0); /* RESERVED */

    /* Update checksum */
    crc = htonl(crc32_map((char *)buf, OFFSET_HEADER_CRC));
    *((bit32 *)(buf+OFFSET_HEADER_CRC)) = crc;

    return crc;
}

int mailbox_commit_quota(struct mailbox *mailbox)
{
    struct txn *tid = NULL;
    int r;
    struct quota q;
    quota_t qdiff;

    /* not dirty */
    if (!mailbox->quota_dirty)
	return 0;

    mailbox->quota_dirty = 0;

    /* unchanged */
    qdiff = mailbox->i.quota_mailbox_used - mailbox->quota_previously_used;
    if (!qdiff)
	return 0;

    /* no quota root means we don't track quota.  That's OK */
    if (!mailbox->quotaroot)
	return 0;

    assert(mailbox_index_islocked(mailbox, 1));

    q.root = mailbox->quotaroot;
    r = quota_read(&q, &tid, 1);
    if (!r) {
	/* check we won't underflow */
	if ((quota_t)-qdiff > (quota_t)q.used)
	    q.used = 0;
	else
	    q.used += qdiff;
	r = quota_write(&q, &tid);
    }

    if (!r) quota_commit(&tid);
    else {
	quota_abort(&tid);
	/* XXX - fail here?  It's tempting */
	syslog(LOG_ERR, "LOSTQUOTA: unable to record quota file %s",
	       mailbox->quotaroot);
    }

    return 0;
}



/*
 * Write the index header for 'mailbox'
 */
int mailbox_commit(struct mailbox *mailbox)
{
    /* XXX - ibuf for alignment? */
    static unsigned char buf[INDEX_HEADER_SIZE];
    int n, r;

    /* try to commit sub parts first */
    r = mailbox_commit_cache(mailbox);
    if (r) return r;

    r = mailbox_commit_quota(mailbox);
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
bit32 mailbox_index_record_to_buf(struct index_record *record,
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
	mailbox->quota_previously_used = mailbox->i.quota_mailbox_used;
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

static void mailbox_index_update_counts(struct mailbox *mailbox,
					struct index_record *record,
					int is_add)
{
    mailbox_quota_dirty(mailbox);
    mailbox_index_dirty(mailbox);
    header_update_counts(&mailbox->i, record, is_add);
}

int mailbox_index_recalc(struct mailbox *mailbox)
{
    struct index_record record;
    int r = 0;
    uint32_t recno;

    assert(mailbox_index_islocked(mailbox, 1));

    /* cache the old used quota */
    mailbox_quota_dirty(mailbox);
    mailbox_index_dirty(mailbox);

    mailbox->i.answered = 0;
    mailbox->i.flagged = 0;
    mailbox->i.deleted = 0;
    mailbox->i.exists = 0;
    mailbox->i.quota_mailbox_used = 0;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) return r;
	mailbox_index_update_counts(mailbox, &record, 1);
    }

    return 0;
}

int mailbox_update_conversations(struct mailbox *mailbox,
				 struct index_record *old,
				 struct index_record *new)
{
    int r = 0;
    conversation_t *conv = NULL;
    int delta_exists = 0;
    int delta_unseen = 0;
    int *delta_counts = NULL;
    int i;
    modseq_t modseq = 0;
    conversation_id_t cid = NULLCONVERSATION;
    struct conversations_state *cstate = NULL;

    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return 0;

    cstate = conversations_get_mbox(mailbox->name);
    if (!cstate)
	return IMAP_CONVERSATIONS_NOT_OPEN;

    if (!old && !new)
	return IMAP_INTERNAL;

    if (old && new) {
	assert(old->uid == new->uid);
	assert(old->modseq <= new->modseq);
	/* this flag cannot go away */
	if ((old->system_flags & FLAG_EXPUNGED))
	    assert((new->system_flags & FLAG_EXPUNGED));

	if (old->cid != new->cid) {
	    /* handle CID being renamed, by calling ourselves */
	    r = mailbox_update_conversations(mailbox, old, NULL);
	    if (!r)
		r = mailbox_update_conversations(mailbox, NULL, new);
	    return r;
	}
    }
    cid = (new ? new->cid : old->cid);

    r = conversation_load(cstate, cid, &conv);
    if (r)
	return r;
    if (!conv)
	conv = conversation_new();

    if (config_counted_flags)
	delta_counts = xzmalloc(sizeof(int) * config_counted_flags->count);

    /* calculate the changes */
    if (old) {
	/* decrease any relevent counts */
	if (!(old->system_flags & FLAG_EXPUNGED)) {
	    delta_exists--;
	    /* drafts are never unseen */
	    if (!(old->system_flags & (FLAG_SEEN|FLAG_DRAFT)))
		delta_unseen--;
	    if (config_counted_flags) {
		for (i = 0; i < config_counted_flags->count; i++) {
		    const char *flag = strarray_nth(config_counted_flags, i);
		    if (mailbox_record_hasflag(mailbox, old, flag))
			delta_counts[i]--;
		}
	    }
	}
	modseq = MAX(modseq, old->modseq);
    }
    if (new) {
	/* add any counts */
	if (!(new->system_flags & FLAG_EXPUNGED)) {
	    delta_exists++;
	    /* drafts are never unseen */
	    if (!(new->system_flags & (FLAG_SEEN|FLAG_DRAFT)))
		delta_unseen++;
	    if (config_counted_flags) {
		for (i = 0; i < config_counted_flags->count; i++) {
		    const char *flag = strarray_nth(config_counted_flags, i);
		    if (mailbox_record_hasflag(mailbox, new, flag))
			delta_counts[i]++;
		}
	    }
	}
	modseq = MAX(modseq, new->modseq);
    }

    /* drafts don't generate sender records so you don't spuriously get
     * yourself just for clicking on "reply" then aborting */
    if (!old && new && !(new->system_flags & (FLAG_EXPUNGED|FLAG_DRAFT))) {
	if (!mailbox_cacherecord(mailbox, new)) {
	    char *env = NULL;
	    char *envtokens[NUMENVTOKENS];
	    struct address addr = { NULL, NULL, NULL, NULL, NULL, NULL };

	    /* Need to find the sender */

	    /* +1 -> skip the leading paren */
	    env = xstrndup(cacheitem_base(new, CACHE_ENVELOPE) + 1,
			   cacheitem_size(new, CACHE_ENVELOPE) - 1);

	    parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

	    if (envtokens[ENV_FROM])
		message_parse_env_address(envtokens[ENV_FROM], &addr);

	    conversation_add_sender(conv, addr.name, addr.route,
				    addr.mailbox, addr.domain);

	    free(env);
	}
    }

    conversation_update(conv, mailbox->name,
			delta_exists, delta_unseen,
			delta_counts, modseq);

    r = conversation_save(cstate, cid, conv);

    conversation_free(conv);
    return r;
}

/*
 * Rewrite an index record in a mailbox - updates all
 * necessary tracking fields automatically.
 */
int mailbox_rewrite_index_record(struct mailbox *mailbox,
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
    if (r) return r;

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

    if (record->system_flags & FLAG_UNLINKED) {
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

	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: expunge sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u> guid=<%s>",
		session_id(), mailbox->name, mailbox->uniqueid,
		record->uid, message_guid_encode(&record->guid));
    }

    r = mailbox_update_conversations(mailbox, &oldrecord, record);

    return r;
}

/* append a single message to a mailbox - also updates everything
 * automatically.  These two functions are the ONLY way to modify
 * the contents or tracking fields of a message */
int mailbox_append_index_record(struct mailbox *mailbox,
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

    /* update the highestmodseq if needed */
    if (record->silent) {
	mailbox_index_dirty(mailbox);
    }
    else {
	mailbox_modseq_dirty(mailbox);
	record->modseq = mailbox->i.highestmodseq;
	record->last_updated = mailbox->last_updated;
    }

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

    /* extend the mmaped space for the index file */
    if (mailbox->index_len < mailbox->index_size) {
	map_refresh(mailbox->index_fd, 1, &mailbox->index_base,
		    &mailbox->index_len, mailbox->index_size,
		    "index", mailbox->name);
    }

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

    r = mailbox_update_conversations(mailbox, NULL, record);
    
    return r;
}

static void mailbox_message_unlink(struct mailbox *mailbox, uint32_t uid)
{
    const char *fname = mailbox_message_fname(mailbox, uid);

    /* no error, we removed a file */
    if (unlink(fname) == 0) {
	if (config_auditlog)
	    syslog(LOG_NOTICE, "auditlog: unlink sessionid=<%s> "
		   "mailbox=<%s> uniqueid=<%s> uid=<%u>",
		   session_id(), mailbox->name, mailbox->uniqueid, uid);
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

int mailbox_repack_setup(struct mailbox *mailbox,
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

int mailbox_repack_add(struct mailbox_repack *repack,
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
void mailbox_repack_abort(struct mailbox_repack **repackptr)
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

int mailbox_repack_commit(struct mailbox_repack **repackptr)
{
    indexbuffer_t ibuf;
    unsigned char *buf = ibuf.buf;
    struct mailbox_repack *repack = *repackptr;
    int n;
    int r;

    assert(repack);

    repack->i.last_repack_time = time(0);

    /* rewrite the header with updated details */
    mailbox_index_header_to_buf(&repack->i, buf);
    n = lseek(repack->newindex_fd, 0, SEEK_SET);
    if (n == -1) {
	r = IMAP_IOERROR;
	goto fail;
    }
    n = retry_write(repack->newindex_fd, buf, INDEX_HEADER_SIZE);
    if (n == -1) {
	r = IMAP_IOERROR;
	goto fail;
    }

    /* ensure everything is committed to disk */
    if (fsync(repack->newindex_fd) || fsync(repack->newcache_fd)) {
	r = IMAP_IOERROR;
	goto fail;
    }

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
	    /* XXX - log error if unlink fails */
	    mailbox_message_unlink(mailbox, record.uid);
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

    return mailbox_repack_commit(&repack);

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
int mailbox_expunge(struct mailbox *mailbox,
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

int mailbox_expunge_cleanup(struct mailbox *mailbox, time_t expunge_mark,
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
	    syslog(LOG_ERR, "failed to write changes to %s recno %d",
		   mailbox->name, recno);
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

int mailbox_internal_seen(struct mailbox *mailbox, const char *userid)
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
int mailbox_create(const char *name,
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
    char *fname;
    struct mailbox *mailbox = NULL;
    int n;
    uint32_t generation_buf;
    int createfnames[] = { META_INDEX, META_CACHE, META_HEADER, 0 };
    struct mailboxlist *listitem;

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
    r = lock_blocking(mailbox->index_fd);
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
        
    if (hasquota) mailbox_set_quotaroot(mailbox, quotaroot);

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

    /* initialise header size field so appends calculate the
     * correct map size */
    mailbox->index_size = INDEX_HEADER_SIZE;

    mailbox->header_dirty = 1;
    if (!uniqueid) {
	mailbox_make_uniqueid(mailbox);
    } else {
	mailbox->uniqueid = xstrdup(uniqueid);
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

    return 0;
}

/*
 * Delete and close the mailbox 'mailbox'.  Closes 'mailbox' whether
 * or not the deletion was successful.  Requires a locked mailbox.
 */
int mailbox_delete(struct mailbox **mailboxptr)
{
    int r = 0;
    struct mailbox *mailbox = *mailboxptr;
    struct conversations_state *cstate = NULL;

    if (config_getswitch(IMAPOPT_CONVERSATIONS)) {
	cstate = conversations_get_mbox(mailbox->name);
	assert(cstate);
    }
    
    /* mark the mailbox deleted */
    mailbox_index_dirty(mailbox);
    mailbox->i.options |= OPT_MAILBOX_DELETED;

    /* mark the quota removed */
    mailbox_quota_dirty(mailbox);
    mailbox->i.quota_mailbox_used = 0;

    /* commit the changes */
    r = mailbox_commit(mailbox);
    if (r) return r;

    /* remove any seen */
    seen_delete_mailbox(NULL, mailbox);

    /* remove conversations records */
    if (config_getswitch(IMAPOPT_CONVERSATIONS)) 
	conversations_rename_folder(cstate, mailbox->name, NULL);

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

    mailbox_close(mailboxptr);

    return 0;
}

/* XXX - move this part of cleanup into mboxlist.  Really
 * needs to be done with mailboxes.db locked so nobody can
 * try to create a mailbox while the delete is underway.
 * VERY tight race condition exists right now... */
/* we need an exclusive namelock for this */
int mailbox_delete_cleanup(const char *part, const char *name)
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
	/* not the same partition, we can keep cleaning up */
	if (!r) {
	    if (strcmp(mbentry->partition, part))
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
    { 0, 0, 0 }
};

int mailbox_copy_files(struct mailbox *mailbox, const char *newpart,
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
int mailbox_rename_copy(struct mailbox *oldmailbox, 
			const char *newname,
			const char *newpartition,
			const char *userid, int ignorequota,
			struct mailbox **newmailboxptr)
{
    int r;
    struct mailbox *newmailbox = NULL;
    struct conversations_state *cstate = NULL;
    char *newquotaroot = NULL;

    assert(mailbox_index_islocked(oldmailbox, 1));

    /* NOTE: in the case of renaming a user to another user, we
     * update all the names in the SOURCE username.conversations,
     * then we rename the conversation file last */
    if (config_getswitch(IMAPOPT_CONVERSATIONS)) {
	cstate = conversations_get_mbox(oldmailbox->name);
	assert(cstate);
    }

    /* we can't rename back from a deleted mailbox, because the conversations
     * information will be wrong.  Ideally we might re-calculate, but for now
     * we just throw a big fat error */
    if (mboxname_isdeletedmailbox(oldmailbox->name, NULL)) {
	syslog(LOG_ERR, "can't rename a deleted mailbox %s", oldmailbox->name);
	return IMAP_MAILBOX_BADNAME;
    }

    /* Create new mailbox */
    r = mailbox_create(newname, newpartition,
		       oldmailbox->acl, (userid ? NULL : oldmailbox->uniqueid),
		       oldmailbox->specialuse, oldmailbox->i.options,
		       0, oldmailbox->i.highestmodseq, &newmailbox);

    if (r) return r;

    /* Check quota if necessary */
    if (!ignorequota && newmailbox->quotaroot && (!oldmailbox->quotaroot || 
	strcmp(oldmailbox->quotaroot, newmailbox->quotaroot))) {
	struct quota q;

	q.root = newmailbox->quotaroot;
	r = quota_read(&q, NULL, 1);

	/* check if the limit is exceeded */
	if (!r && q.limit >= 0 && q.used + oldmailbox->i.quota_mailbox_used >
	    (uquota_t) q.limit * QUOTA_UNITS) {
		r = IMAP_QUOTA_EXCEEDED;
	}

	/* then we abort - no space to rename */
	if (r && r != IMAP_QUOTAROOT_NONEXISTENT)
	    goto fail;
    }
    if (newmailbox->quotaroot) newquotaroot = xstrdup(newmailbox->quotaroot);

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

    /* update uidvalidity */
    newmailbox->i.uidvalidity = mboxname_nextuidvalidity(newname, time(0));

    /* INBOX rename - change uniqueid */
    if (!userid) mailbox_make_uniqueid(newmailbox);

    r = seen_copy(userid, oldmailbox, newmailbox);
    if (r) goto fail;

    /* mark the "used" back to zero, so it updates the new quota! */
    mailbox_set_quotaroot(newmailbox, newquotaroot);
    mailbox_quota_dirty(newmailbox);
    newmailbox->quota_previously_used = 0;

    /* commit the index changes */
    r = mailbox_commit(newmailbox);
    if (r) goto fail;

    /* if new name is deleted, don't keep the numbers */
    if (config_getswitch(IMAPOPT_CONVERSATIONS)) {
	if (mboxname_isdeletedmailbox(newname, NULL))
	    conversations_rename_folder(cstate, oldmailbox->name, NULL);
	else
	    conversations_rename_folder(cstate, oldmailbox->name, newname);
    }

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
     /* failure and back out */
    /* XXX - per file paths, need to clean up individual filenames */
    mailbox_delete_cleanup(newmailbox->part, newmailbox->name);
    mailbox_close(&newmailbox);
    free(newquotaroot);

    return r;
}

int mailbox_rename_cleanup(struct mailbox **mailboxptr, int isinbox) 
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
	r = mailbox_delete(mailboxptr);
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
static int mailbox_copyfile_core(const char *from, const char *to,
				 int nolink)
{
    int srcfd, destfd;
    struct stat sbuf;
    const char *src_base = 0;
    unsigned long src_size = 0;
    int n;

    if (!nolink) {
	if (link(from, to) == 0) return 0;
	if (errno == EEXIST) {
	    if (unlink(to) == -1) {
		syslog(LOG_ERR, "IOERROR: unlinking to recreate %s: %m", to);
		return IMAP_IOERROR;
	    }
	    if (link(from, to) == 0) return 0;
	}
    }

    destfd = open(to, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (destfd == -1) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", to);
	return IMAP_IOERROR;
    }

    srcfd = open(from, O_RDONLY, 0666);
    if (srcfd == -1) {
	syslog(LOG_ERR, "IOERROR: opening %s: %m", from);
	close(destfd);
	return IMAP_IOERROR;
    }


    if (fstat(srcfd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on %s: %m", from);
	close(srcfd);
	close(destfd);
	return IMAP_IOERROR;
    }
    map_refresh(srcfd, 1, &src_base, &src_size, sbuf.st_size, from, 0);

    n = retry_write(destfd, src_base, src_size);

    if (n == -1 || fsync(destfd)) {
	map_free(&src_base, &src_size);
	close(srcfd);
	close(destfd);
	syslog(LOG_ERR, "IOERROR: writing %s: %m", to);
	return IMAP_IOERROR;
    }
    map_free(&src_base, &src_size);
    close(srcfd);
    close(destfd);
    return 0;
}

int mailbox_copyfile(const char *from, const char *to, int nolink)
{
    /* try to make the target dir if initial copy fails */
    if (mailbox_copyfile_core(from, to, nolink)) {
	cyrus_mkdir(to, 0755);
	return mailbox_copyfile_core(from, to, nolink);
    }
    return 0;
}

/* ---------------------------------------------------------------------- */
/*                      RECONSTRUCT SUPPORT                               */
/* ---------------------------------------------------------------------- */

#define UIDGROW 300

struct found_files {
    unsigned long *uids;
    unsigned nalloc;
    unsigned nused;
};

static int sort_uid(const void *a, const void *b)
{
    return *(unsigned long *)a - *(unsigned long *)b;
}

static void init_files(struct found_files *ff)
{
    ff->uids = NULL;
    ff->nused = 0;
    ff->nalloc = 0;
}

static void add_files(struct found_files *ff, unsigned long uid)
{
    /* make sure there's space */
    if (ff->nused >= ff->nalloc) {
	ff->nalloc += UIDGROW;
	ff->uids = xrealloc(ff->uids, ff->nalloc * sizeof(unsigned long));
    }
    ff->uids[ff->nused++] = uid;
}

static void free_files(struct found_files *ff)
{
    if (ff->nalloc)
	free(ff->uids);
    init_files(ff);
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

static int find_files(struct mailbox *mailbox, struct found_files *files,
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

    init_files(files);

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
	    if (stat(buf, &sbuf) == -1) continue; /* ignore emepheral */
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
	    add_files(files, uid);
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
    unsigned long expunge_len = 0;   /* mapped size */
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
					      struct found_files *discovered)
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
		add_files(discovered, record->uid);
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

    return mailbox_append_index_record(mailbox, &record);
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


/*
 * Reconstruct the single mailbox named 'name'
 */
int mailbox_reconstruct(const char *name, int flags)
{
    /* settings */
    int make_changes = (flags & RECONSTRUCT_MAKE_CHANGES);

    int r = 0;
    uint32_t msg;
    int i, flag;
    struct index_record record;
    struct mailbox *mailbox = NULL;
    struct found_files files;
    struct found_files discovered;
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

    r = mailbox_open_cache(mailbox);
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

	/* ensure that next user will create the MMAPing */
	mailbox->need_cache_refresh = 1;
    }

    /* find cyrus.expunge file if present */
    cleanup_stale_expunged(mailbox);

    r = find_files(mailbox, &files, flags);
    if (r) goto close;
    init_files(&discovered);
    msg = 0;

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

	/* lower UID file exists */
	while (msg < files.nused && files.uids[msg] < record.uid) {
	    add_files(&discovered, files.uids[msg]);
	    msg++;
	}

	/* if they match, advance the pointer */
	have_file = 0;
	if (msg < files.nused && files.uids[msg] == record.uid) {
	    have_file = 1;
	    msg++;
	}

	r = mailbox_reconstruct_compare_update(mailbox, &record,
					       valid_user_flags,
					       flags, have_file,
					       &discovered);
	if (r) goto close;
    }

    /* add discovered messages before last_uid to the list in order */
    while (msg < files.nused && files.uids[msg] <= mailbox->i.last_uid) {
	add_files(&discovered, files.uids[msg]);
	msg++;
    }

    /* messages AFTER last_uid can keep the same UID (see also, restore
     * from list .index file) - so don't bother moving those */
    while (msg < files.nused) {
	r = mailbox_reconstruct_append(mailbox, files.uids[msg], flags);
	if (r) goto close;
	msg++;
    }
    
    /* handle new list */
    msg = 0;
    while (msg < discovered.nused) {
	r = mailbox_reconstruct_append(mailbox, discovered.uids[msg], flags);
	if (r) goto close;
	msg++;
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
    free_files(&files);
    free_files(&discovered);
    mailbox_close(&mailbox);
    return r;
}

/*
 * Atomically append an action record to the actions file for the named
 * mailbox.  Does not require the mailbox or index locks.  Does very
 * briefly lock the actions file using fcntl locks.  Handles the actions
 * file being renamed to actionsx (i.e. losing the race against a
 * process doing a mailbox open).
 * Returns: 0 on success or IMAP error code.
 */
static int mailbox_post_action(const char *name,
			       const struct buf *action)
{
    char *fname;
    int fd = -1;
    int r = 0;
    struct mboxlist_entry *mbentry = NULL;
    const char *failmode;
    int flags;

    /* Ensure the action contains a newline */
    if (action->len == 0 || action->s[action->len-1] != '\n')
	return IMAP_INVALID_IDENTIFIER;

    r = mboxlist_lookup(name, &mbentry, NULL);
    if (r)
	return r;

    fname = mboxname_metapath(mbentry->partition, name, META_ACTIONS, 0);
    if (!fname) {
	r = IMAP_MAILBOX_BADNAME;
	goto out;
    }

    for (;;) {
	fd = open(fname, O_RDWR|O_CREAT, 0600);
	if (fd < 0) {
	    r = IMAP_SYS_ERROR;
	    goto out;
	}

	failmode = NULL;
	r = lock_reopen(fd, fname, NULL, &failmode);
	if (r < 0 && (!failmode || strcmp(failmode, "opening"))) {
	    r = IMAP_IOERROR;
	    goto out;
	}
	if (r == 0)
	    break;

	/* lost the race against rename, retry opening */
	close(fd);
    }

    /* We might have a new fd from the one we started with, created by
     * lock_reopen(), whose flags won't include O_APPEND.  So add
     * O_APPEND as a 2nd step. */
    flags = fcntl(fd, F_GETFL, &flags);
    if (flags < 0) {
	r = IMAP_IOERROR;
	goto out_unlock;
    }
    r = fcntl(fd, F_SETFL, flags|O_APPEND);
    if (r < 0) {
	r = IMAP_IOERROR;
	goto out_unlock;
    }

    /* Finally, do the append */
    r = write(fd, action->s, action->len);
    if (r < 0 || r < (int)action->len) {
	r = IMAP_IOERROR;
	goto out_unlock;
    }

out_unlock:
    lock_unlock(fd);
out:
    close(fd);
    mboxlist_entry_free(&mbentry);
    return 0;
}

int mailbox_rename_cid(struct conversations_state *state,
		       conversation_id_t from_cid,
		       conversation_id_t to_cid)
{
    struct buf action = BUF_INITIALIZER;
    conversation_t *conv = NULL;
    conv_folder_t *folder;
    int r = 0;

    r = conversations_rename_cid(state, from_cid, to_cid);
    if (r)
	goto out;

    /* Use the B record to notify mailboxes of a CID rename.
     * We don't actually alter the values, because the EXPUNGE
     * events later will decrease the EXISTS back to zero, and
     * then it will delete itself */
    r = conversation_load(state, from_cid, &conv);
    if (!r && conv) {
	for (folder = conv->folders ; folder ; folder = folder->next) {
	    buf_reset(&action);
	    buf_printf(&action, "CIDRENAME " CONV_FMT " " CONV_FMT "\n",
		       from_cid, to_cid);

	    r = mailbox_post_action(folder->mboxname, &action);
	    if (r)
		syslog(LOG_ERR, "Failed to post CID rename for mailbox \"%s\": %s",
		       folder->mboxname, error_message(r));
	    r = 0;	/* ignore any error and keep going */
	}
	conversation_free(conv);
    }

out:
    buf_free(&action);
    return r;
}

int mailbox_post_nop_action(const char *name, unsigned int tag)
{
    struct buf action = BUF_INITIALIZER;
    int r;

    buf_printf(&action, "NOP %u\n", tag);
    r = mailbox_post_action(name, &action);
    buf_free(&action);
    return r;
}

static void mailbox_action_cid_rename(struct mailbox *mailbox,
				      const strarray_t *action,
				      const char *fname,
				      unsigned int lineno)
{
    conversation_id_t from_cid, to_cid;
    uint32_t recno, num_records;
    struct index_record record;
    struct index_record new_record;
    char msgfile[MAX_MAILBOX_PATH], newmsgfile[MAX_MAILBOX_PATH];
    int r;

    if (!config_getswitch(IMAPOPT_CONVERSATIONS))
	return;

    if (action->count != 3)
	goto bad_syntax;

    r = conversation_id_decode(&from_cid, action->data[1]);
    if (!r)
	goto bad_syntax;
    r = conversation_id_decode(&to_cid, action->data[2]);
    if (!r)
	goto bad_syntax;

    syslog(LOG_NOTICE, "Performing delayed CID rename: %s -> %s",
			action->data[1], action->data[2]);

    num_records = mailbox->i.num_records;
    for (recno = 1; recno <= num_records; recno++) {

	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) {
	    syslog(LOG_ERR, "mailbox_action_cid_rename: error "
			    "reading record %u, mailbox %s: %s",
			    recno, mailbox->name, error_message(r));
	    return;
	}

	if (record.system_flags & FLAG_EXPUNGED)
	    continue;
	if (record.cid != from_cid)
	    continue;

	/*
	 * [IRIS-293] handle CID renaming by re-inserting a new message
	 * and expunging the old one.  Thus the UID->CID mapping remains
	 * constant, i.e. the CID is an immutable property of a message.
	 * This is expected to aid caching in conversation-aware clients.
	 */

	/* clone the record */
	new_record = record;
	/* old record will be expunged */
	record.system_flags |= (FLAG_EXPUNGED|FLAG_UNLINKED);
	/* new record has new CID and UID */
	new_record.cid = to_cid;
	new_record.uid = mailbox->i.last_uid+1;

	/* hardlink the old message file to the new name */
	strncpy(msgfile, mailbox_message_fname(mailbox, record.uid),
		MAX_MAILBOX_PATH);
	strncpy(newmsgfile, mailbox_message_fname(mailbox, new_record.uid),
		MAX_MAILBOX_PATH);
	r = mailbox_copyfile(msgfile, newmsgfile, 0);

	/* append the new record */
	if (!r)
	    r = mailbox_append_index_record(mailbox, &new_record);

	/* rewrite the old record */
	if (!r)
	    r = mailbox_rewrite_index_record(mailbox, &record);

	/* finally, remove the old message file */
	if (!r && unlink(msgfile) < 0)
	    r = IMAP_IOERROR;

	if (r) {
	    syslog(LOG_ERR, "mailbox_action_cid_rename: error "
			    "reinserting record %u, mailbox %s: %s",
			    recno, mailbox->name, error_message(r));
	    return;
	}
    }

    return;

bad_syntax:
    syslog(LOG_ERR, "Bad syntax for CIDRENAME, line %u file %s",
		    lineno, fname);
}

/* This is for testing only */
unsigned int mailbox_nop_action_count = 0;
unsigned int mailbox_nop_action_tag = 0;

static void mailbox_action_nop(struct mailbox *mailbox __attribute__((unused)),
			       const strarray_t *action,
			       const char *fname __attribute__((unused)),
			       unsigned int lineno __attribute__((unused)))
{
    mailbox_nop_action_count++;
    mailbox_nop_action_tag = (action->count > 1 ?
			    strtoul(action->data[1], NULL, 0) : 0);
}

static void mailbox_execute_actions_file(struct mailbox *mailbox,
				         FILE *fp, const char *fname)
{
    char buf[1024];
    unsigned int lineno = 0;	/* used for error reporting */
    strarray_t *action;

    while (fgets(buf, sizeof(buf), fp)) {
	action = strarray_split(buf, NULL);
	lineno++;

	if (action->count < 1) {
	    syslog(LOG_ERR, "Unexpected empty line, line %u file %s",
			    lineno, fname);
	    strarray_free(action);
	    continue;
	}

	if (!strcmp(action->data[0], "NOP")) {
	    mailbox_action_nop(mailbox, action, fname, lineno);
	} else if (!strcmp(action->data[0], "CIDRENAME")) {
	    mailbox_action_cid_rename(mailbox, action, fname, lineno);
	} else {
	    syslog(LOG_ERR, "Unknown record type \"%s\", line %u file %s",
			    action->data[0], lineno, fname);
	}

	strarray_free(action);
    }
}

static int mailbox_execute_actions(struct mailbox *mailbox)
{
    char *actions_filename = NULL;
    char *actionsx_filename = NULL;
    int fd = -1;
    int r = 0;

    actionsx_filename = mailbox_meta_fname(mailbox, META_ACTIONSX);
    if (!actionsx_filename) {
	r = IMAP_MAILBOX_BADNAME;
	goto out;
    }
    actionsx_filename = xstrdup(actionsx_filename);

    actions_filename = mailbox_meta_fname(mailbox, META_ACTIONS);
    if (!actions_filename) {
	r = IMAP_MAILBOX_BADNAME;
	goto out;
    }
    actions_filename = xstrdup(actions_filename);

    for (;;) {
	fd = open(actionsx_filename, O_RDWR, 0);
	if (fd < 0) {
	    if (errno != ENOENT) {
		syslog(LOG_ERR, "Unable to open %s: %m", actionsx_filename);
		r = IMAP_SYS_ERROR;
		goto out;
	    }
	} else {
	    FILE *fp = fdopen(fd, "r");
	    if (!fp) {
		syslog(LOG_ERR, "Unable to open %s: %m", actionsx_filename);
		r = IMAP_SYS_ERROR;
		close(fd);
		goto out;
	    }
	    mailbox_execute_actions_file(mailbox, fp, actionsx_filename);
	    fclose(fp);
	    unlink(actionsx_filename);
	}

	fd = open(actions_filename, O_RDWR, 0);
	if (fd < 0) {
	    if (errno == ENOENT)
		break;
	    syslog(LOG_ERR, "Failed opening %s for locking: %m",
			    actions_filename);
	    r = IMAP_SYS_ERROR;
	    goto out;
	}

	r = lock_blocking(fd);
	if (r < 0) {
	    syslog(LOG_ERR, "Failed locking %s: %m",
			    actions_filename);
	    r = IMAP_SYS_ERROR;
	    goto out_unlock;
	}

	r = rename(actions_filename, actionsx_filename);
	if (r < 0) {
	    if (errno == ENOENT)
		break;
	    syslog(LOG_ERR, "Failed renaming %s to %s: %m",
			    actions_filename, actionsx_filename);
	    r = IMAP_SYS_ERROR;
	    goto out_unlock;
	}

	lock_unlock(fd);
	close(fd);
    }

out:
    free(actions_filename);
    free(actionsx_filename);
    return r;

out_unlock:
    lock_unlock(fd);
    if (fd >= 0)
	close(fd);
    goto out;
}
