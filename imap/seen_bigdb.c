/* seen_bigdb.c -- implementation of seen database using one big cyrusdb
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
 * $Id: seen_bigdb.c,v 1.11.2.2 2009/12/28 21:51:39 murch Exp $
 */

#include <config.h>

#include <stdlib.h>
#include <syslog.h>
#include <string.h>
#include <ctype.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <errno.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include "cyrusdb.h"

#include "assert.h"
#include "global.h"
#include "xmalloc.h"
#include "mailbox.h"
#include "imap_err.h"
#include "exitcodes.h"
#include "util.h"

#include "cyrusdb.h"
#include "seen.h"

#define FNAME_SEENDB "/seenstate.db"

/* choose "flat" or "berkeley" here --- berkeley highly recommended */
#define DB (&cyrusdb_berkeley)

enum {
    MAX_KEY = MAX_MAILBOX_PATH + MAX_MAILBOX_NAME + 30,
    SEEN_VERSION = 1,
    SEEN_DEBUG = 0
};

struct seen {
    const char *user;		/* what user is this for? */
    const char *uniqueid;	/* what mailbox? */
    struct txn *tid;		/* outstanding txn, if any */
};

static int seen_inited = 0;
static struct db *bigdb;

/* Stub */
char *seen_getpath(const char *userid) 
{
    return NULL;
}

static void seen_init(void)
{
    int r;
    char fname[1024];

    assert(!seen_inited);

    /* create db file name */
    strcpy(fname, config_dir);
    strcat(fname, FNAME_SEENDB);

    r = (DB->open)(fname, CYRUSDB_CREATE, &bigdb);
    if (r != 0) {
	syslog(LOG_ERR, "DBERROR: opening %s: %s", fname,
	       cyrusdb_strerror(r));
	fatal("can't read seenstate file", EC_TEMPFAIL);
    }

    seen_inited = 1;
}

/* get a database handle corresponding to (mailbox, user) pair */
int seen_open(struct mailbox *mailbox, 
	      const char *user,
	      int flags __attribute__((unused)),
	      struct seen **seendbptr)
{
    struct seen *ret;

    if (!seen_inited) {
	seen_init();
    }

    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_bigdb: seen_open(%s, %s)", 
	       mailbox->uniqueid, user);
    }

    ret = (struct seen *) xmalloc(sizeof(struct seen));
    ret->tid = NULL;
    ret->uniqueid = mailbox->uniqueid;
    ret->user = user;

    *seendbptr = ret;
    return 0;
}

/* construct the key for this uniqueid/user pair; ret must be at least
   MAX_KEY long */
static int getkey(const char *uniqueid, const char *user,
		  char *ret)
{
    assert(uniqueid && user);
    assert(ret);

    snprintf(ret, MAX_KEY, "%s//%s", uniqueid, user);
    
    return 0;
}

static int seen_readit(struct seen *seendb, 
		       time_t *lastreadptr, unsigned int *lastuidptr, 
		       time_t *lastchangeptr, char **seenuidsptr,
		       int rw)
{
    char key[MAX_KEY];
    const char *data, *dstart, *dend;
    char *p;
    int datalen;
    int version;
    int uidlen;
    int r;

    assert(seendb);
    getkey(seendb->uniqueid, seendb->user, key);
    
    if (rw) {
	r = DB->fetchlock(bigdb, key, strlen(key),
			  &data, &datalen, &seendb->tid);
    } else {
	r = DB->fetch(bigdb, key, strlen(key),
		      &data, &datalen, NULL);
    }
    switch (r) {
    case 0:
	break;
    case CYRUSDB_AGAIN:
	syslog(LOG_DEBUG, "deadlock in seen database for '%s/%s'",
	       seendb->user, seendb->uniqueid);
	return IMAP_AGAIN;
	break;
    case CYRUSDB_IOERROR:
	syslog(LOG_ERR, "DBERROR: error fetching txn", cyrusdb_strerror(r));
	return IMAP_IOERROR;
	break;
    case CYRUSDB_NOTFOUND:
	*lastreadptr = 0;
	*lastuidptr = 0;
	*lastchangeptr = 0;
	*seenuidsptr = xstrdup("");
	return 0;
	break;
    }

    /* remember that 'data' may not be null terminated ! */
    dstart = data;
    dend = data + datalen;

    version = strtol(data, &p, 10); data = p;
    assert(version == SEEN_VERSION);
    *lastreadptr = strtol(data, &p, 10); data = p;
    *lastuidptr = strtol(data, &p, 10); data = p;
    *lastchangeptr = strtol(data, &p, 10); data = p;
    while (Uisspace(*p) && p < dend) p++; data = p;
    uidlen = dend - data;
    *seenuidsptr = xmalloc(uidlen + 1);
    memcpy(*seenuidsptr, data, uidlen);
    (*seenuidsptr)[uidlen] = '\0';

    return 0;
}
/* read an entry from 'seendb' */
int seen_read(struct seen *seendb, 
	      time_t *lastreadptr, unsigned int *lastuidptr, 
	      time_t *lastchangeptr, char **seenuidsptr)
{
    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_bigdb: seen_read(%s, %s)", 
	       seendb->uniqueid, seendb->user);
    }

    return seen_readit(seendb, lastreadptr, lastuidptr, lastchangeptr,
		       seenuidsptr, 0);
}

/* read an entry from 'seendb' and leave that record (or some superset
   of it) locked for update */
int seen_lockread(struct seen *seendb, 
		  time_t *lastreadptr, unsigned int *lastuidptr, 
		  time_t *lastchangeptr, char **seenuidsptr)
{
    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_bigdb: seen_lockread(%s, %s)", 
	       seendb->uniqueid, seendb->user);
    }

    return seen_readit(seendb, lastreadptr, lastuidptr, lastchangeptr,
		       seenuidsptr, 1);
}

/* write an entry to 'seendb'; should have been already locked by
   seen_lockread() */
int seen_write(struct seen *seendb, time_t lastread, unsigned int lastuid, 
	       time_t lastchange, char *seenuids)
{
    char key[MAX_KEY];
    int sz = strlen(seenuids) + 50;
    char *data = xmalloc(sz);
    int datalen;
    int r;

    assert(seendb && seendb->tid);
    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_db: seen_write(%s, %s)", 
	       seendb->uniqueid, seendb->user);
    }

    getkey(seendb->uniqueid, seendb->user, key);
    sprintf(data, "%d %d %d %d %s", SEEN_VERSION, 
	    (int) lastread, lastuid, (int) lastchange, seenuids);
    datalen = strlen(data);

    r = DB->store(bigdb, key, strlen(key), data, datalen, &seendb->tid);
    switch (r) {
    case CYRUSDB_OK:
	break;
    case CYRUSDB_IOERROR:
	r = IMAP_AGAIN;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error updating database: %s", 
	       cyrusdb_strerror(r));
	r = IMAP_IOERROR;
	break;
    }

    free(data);
    return r;
}

/* close this handle */
int seen_close(struct seen *seendb)
{
    int r;

    assert(seendb);

    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_db: seen_close(%s, %s)", 
	       seendb->uniqueid, seendb->user);
    }

    if (seendb->tid) {
	r = DB->commit(bigdb, seendb->tid);
	if (r != CYRUSDB_OK) {
	    syslog(LOG_ERR, "DBERROR: error committing seen txn; "
		   "seen state lost: %s", cyrusdb_strerror(r));
	}
	seendb->tid = NULL;
    }
    free(seendb);

    return 0;
}

/* discard lock on handle; commit any pending txns */
int seen_unlock(struct seen *seendb)
{
    int r;

    assert(seendb);

    if (SEEN_DEBUG) {
	syslog(LOG_DEBUG, "seen_db: seen_unlock(%s, %s)",
	       seendb->uniqueid, seendb->user);

    }

    r = DB->commit(bigdb, seendb->tid);
    if (r != CYRUSDB_OK) {
	syslog(LOG_ERR, "DBERROR: error committing seen txn; "
	       "seen state lost: %s", cyrusdb_strerror(r));
    }
    seendb->tid = NULL;

    return 0;
}

/* called on mailbox operations */
int seen_create_mailbox(struct mailbox *mailbox)
{
    return 0;			/* noop */
}

int seen_delete_mailbox(struct mailbox *mailbox)
{
    return 0;			/* noop */
}

int seen_copy(struct mailbox *oldmailbox,struct mailbox *newmailbox)
{
    return 0;			/* noop */
}

/* called on user operations */
int seen_create_user(const char *user)
{
    return 0;			/* noop */
}

int seen_delete_user(const char *user)
{
    return 0;			/* noop */
}

int seen_rename_user(const char *olduser, const char *newuser)
{
    return 0;			/* noop */
}

int seen_reconstruct(struct mailbox *mailbox,
		     time_t report_time,
		     time_t prune_time,
		     int (*report_proc)(),
		     void *report_rock)
{
    return 0;			/* noop */
}

int seen_dump(void)
{
    /* need a way of dumping seen state */

    return -1;
}

/* done with all seen operations for this process */
int seen_done(void)
{
    int r;

    if (seen_inited) {
	r = (DB->close)(bigdb);
	if (r != 0) {
	    syslog(LOG_ERR, "DBERROR: closing seen database: %s",
		   cyrusdb_strerror(r));
	    fatal("can't read seenstate file", EC_TEMPFAIL);
	}
	
	seen_inited = 0;
    }

    return 0;
}

int seen_merge(const char *tmpfile, const char *tgtfile) 
{
    /* Not supported */
    return -1;
}
