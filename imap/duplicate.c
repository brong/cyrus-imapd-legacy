/*
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
 * $Id: duplicate.c,v 1.48 2010/01/06 17:01:31 murch Exp $
 */

#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <ctype.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#if HAVE_DIRENT_H
# include <dirent.h>
#else
# define dirent direct
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
#include <errno.h>

#include "assert.h"
#include "xmalloc.h"
#include "imap_err.h"
#include "global.h"
#include "exitcodes.h"
#include "util.h"
#include "cyrusdb.h"

#include "duplicate.h"

#define DB (config_duplicate_db)

static struct db *dupdb = NULL;
static int duplicate_dbopen = 0;

/* must be called after cyrus_init */
int duplicate_init(const char *fname, int myflags __attribute__((unused)))
{
    char buf[1024];
    int r = 0;

    if (r != 0)
	syslog(LOG_ERR, "DBERROR: init %s: %s", buf,
	       cyrusdb_strerror(r));
    else {
	char *tofree = NULL;

	if (!fname)
	    fname = config_getstring(IMAPOPT_DUPLICATE_DB_PATH);

	/* create db file name */
	if (!fname) {
	    tofree = strconcat(config_dir, FNAME_DELIVERDB, (char *)NULL);
	    fname = tofree;
	}

	r = (DB->open)(fname, CYRUSDB_CREATE, &dupdb);
	if (r != 0)
	    syslog(LOG_ERR, "DBERROR: opening %s: %s", fname,
		   cyrusdb_strerror(r));
	else
	    duplicate_dbopen = 1;

	free(tofree);
    }

    return r;
}

time_t duplicate_check(duplicate_key_t *dkey)
{
    char buf[1024];
    size_t idlen = strlen(dkey->id);
    size_t tolen = strlen(dkey->to);
    size_t datelen = strlen(dkey->date); 
    int r;
    const char *data = NULL;
    size_t len = 0;
    time_t mark = 0;

    if (!duplicate_dbopen) return 0;

    if (idlen + tolen + datelen > (int) sizeof(buf) - 30) return 0;
    memcpy(buf, dkey->id, idlen);
    buf[idlen] = '\0';
    memcpy(buf + idlen + 1, dkey->to, tolen);
    buf[idlen + tolen + 1] = '\0';
    assert(dkey->date != NULL);
    memcpy(buf + idlen + tolen + 2, dkey->date, datelen);
    buf[idlen + tolen + datelen + 2] = '\0';

    do {
	r = DB->fetch(dupdb, buf,
		      idlen + tolen + datelen + 3, /* We have three concatenated values now, all parts ending with '\0' */
		      &data, &len, NULL);
    } while (r == CYRUSDB_AGAIN);

    if (!r && data) {
	assert((len == sizeof(time_t)) ||
	       (len == sizeof(time_t) + sizeof(unsigned long)));

	/* found the record */
	memcpy(&mark, data, sizeof(time_t));
    } else if (r != CYRUSDB_OK) {
	if (r != CYRUSDB_NOTFOUND) {
	    syslog(LOG_ERR, "duplicate_check: error looking up %s/%s/%s: %s",
		   dkey->id, dkey->to, dkey->date, 
		   cyrusdb_strerror(r)); 
	}
	mark = 0;
    }

    syslog(LOG_DEBUG, "duplicate_check: %-40s %-20s %-40s %ld",
	   buf, buf+idlen+1, buf+idlen+tolen+2, mark); 

    return mark;
}

void duplicate_log(duplicate_key_t *dkey, char *action) 
{
    assert(dkey->date != NULL);
    syslog(LOG_INFO, "dupelim: eliminated duplicate message to %s id %s date %s (%s)",
      dkey->to, dkey->id, dkey->date, action);    
    if (config_auditlog)
	syslog(LOG_NOTICE, "auditlog: duplicate sessionid=<%s> action=<%s> message-id=%s user=<%s> date=<%s>",
	       session_id(), action, dkey->id, dkey->to, dkey->date); 
}

void duplicate_mark(duplicate_key_t *dkey, time_t mark, unsigned long uid)
{
    char buf[1024], data[100];
    int idlen = strlen(dkey->id);
    int tolen = strlen(dkey->to);
    int datelen = strlen(dkey->date); 
    int r;

    if (!duplicate_dbopen) return;

    if (idlen + tolen + datelen > (int) sizeof(buf) - 30) return; 
    memcpy(buf, dkey->id, idlen);
    buf[idlen] = '\0';
    memcpy(buf + idlen + 1, dkey->to, tolen);
    buf[idlen + tolen + 1] = '\0';
    assert(dkey->date != NULL);
    memcpy(buf + idlen + tolen + 2, dkey->date, datelen);
    buf[idlen + tolen + datelen + 2] = '\0';

    memcpy(data, &mark, sizeof(mark));
    memcpy(data + sizeof(mark), &uid, sizeof(uid));

    do {
	r = DB->store(dupdb, buf,
		      idlen + tolen + datelen + 3, /* We have three concatenated values now, all parts ending with '\0' */
		      data, sizeof(mark)+sizeof(uid), NULL);
    } while (r == CYRUSDB_AGAIN);

    syslog(LOG_DEBUG, "duplicate_mark: %-40s %-20s %-40s %ld %lu",
	   buf, buf+idlen+1, buf+idlen+tolen+2, mark, uid); 

    return;
}

struct findrock {
    duplicate_find_proc_t proc;
    void *rock;
};

static int find_p(void *rock __attribute__((unused)),
		  const char *id,
		  size_t idlen __attribute__((unused)),
		  const char *data __attribute__((unused)),
		  size_t datalen __attribute__((unused)))
{
    const char *rcpt;

    /* grab the rcpt and make sure its a mailbox */
    rcpt = id + strlen(id) + 1;
    return (rcpt[0] != '.');
}

static int find_cb(void *rock, const char *id,
		   size_t idlen __attribute__((unused)),
		   const char *data, size_t datalen)
{
    struct findrock *frock = (struct findrock *) rock;
    const char *rcpt;
    time_t mark;
    unsigned long uid = 0;
    int r;

    /* grab the rcpt */
    rcpt = id + strlen(id) + 1;

    /* grab the mark and uid */
    memcpy(&mark, data, sizeof(time_t));
    if (datalen > (int) sizeof(mark))
	memcpy(&uid, data + sizeof(mark), sizeof(unsigned long));

    r = (*frock->proc)(id, rcpt, mark, uid, frock->rock);

    return r;
}

int duplicate_find(const char *msgid,
		   duplicate_find_proc_t proc,
		   void *rock)
{
    struct findrock frock;

    if (!msgid) msgid = "";

    frock.proc = proc;
    frock.rock = rock;

    /* check each entry in our database */
    DB->foreach(dupdb, msgid, strlen(msgid), &find_p, &find_cb, &frock, NULL);

    return 0;
}

struct prunerock {
    struct db *db;
    time_t expmark; /* default expmark, if not overridden by table entry */
    struct hash_table *expire_table;
    int count;
    int deletions;
};

static int prune_p(void *rock,
		   const char *id, size_t idlen __attribute__((unused)),
		   const char *data, size_t datalen __attribute__((unused)))
{
    struct prunerock *prock = (struct prunerock *) rock;
    const char *rcpt;
    time_t mark, *expmark = NULL;

    prock->count++;

    /* grab the rcpt, make sure its a mailbox and lookup its expire time */
    rcpt = id + strlen(id) + 1;
    if (prock->expire_table && rcpt[0] && rcpt[0] != '.') {
	expmark = (time_t *) hash_lookup(rcpt, prock->expire_table);
    }

    /* grab the mark */
    memcpy(&mark, data, sizeof(time_t));

    /* check if we should prune this entry */
    return (mark < (expmark ? *expmark : prock->expmark));
}

static int prune_cb(void *rock, const char *id, size_t idlen,
		    const char *data __attribute__((unused)),
		    size_t datalen __attribute__((unused)))
{
    struct prunerock *prock = (struct prunerock *) rock;
    int r;

    prock->deletions++;

    do {
	r = DB->delete(prock->db, id, idlen, NULL, 0);
    } while (r == CYRUSDB_AGAIN);


    return 0;
}

int duplicate_prune(int seconds, struct hash_table *expire_table)
{
    struct prunerock prock;

    if (seconds < 0) fatal("must specify positive number of seconds", EC_USAGE);

    prock.count = prock.deletions = 0;
    prock.expmark = time(NULL) - seconds;
    prock.expire_table = expire_table;
    syslog(LOG_NOTICE, "duplicate_prune: pruning back %0.2f days",
	   ((double)seconds/86400));

    /* check each entry in our database */
    prock.db = dupdb;
    DB->foreach(dupdb, "", 0, &prune_p, &prune_cb, &prock, NULL);

    syslog(LOG_NOTICE, "duplicate_prune: purged %d out of %d entries",
	   prock.deletions, prock.count);

    return 0;
}

struct dumprock {
    FILE *f;
    int count;
};

static int dump_cb(void *rock,
		   const char *key, size_t keylen __attribute__((unused)),
		   const char *data, size_t datalen)
{
    struct dumprock *drock = (struct dumprock *) rock;
    time_t mark;
    char *id, *to, *freeme;
    int idlen, i;
    unsigned long uid = 0;

    assert((datalen == sizeof(time_t)) ||
	   (datalen == sizeof(time_t) + sizeof(unsigned long)));

    drock->count++;

    memcpy(&mark, data, sizeof(time_t));
    if (datalen > (int) sizeof(mark))
	memcpy(&uid, data + sizeof(mark), sizeof(unsigned long));
    to = (char*) key + strlen(key) + 1;
    id = (char *) key;
    idlen = strlen(id);

    for (i = 0; i < idlen; i++) {
	if (!isprint((unsigned char) id[i])) break;
    }

    if (i != idlen) {
	/* change to hexadecimal */
	freeme = xmalloc(idlen * 2 + 1);
	bin_to_hex(id, idlen, freeme, BH_UPPER);
	id = freeme;
    } else {
	freeme = NULL;
    }

    fprintf(drock->f, "id: %-40s\tto: %-20s\tat: %ld\tuid: %lu\n",
	    id, to, (long) mark, uid);

    if (freeme) free(freeme);

    return 0;
}

int duplicate_dump(FILE *f)
{
    struct dumprock drock;

    drock.f = f;
    drock.count = 0;

    /* check each entry in our database */
    DB->foreach(dupdb, "", 0, NULL, &dump_cb, &drock, NULL);

    return drock.count;
}

int duplicate_done(void)
{
    int r = 0;

    if (duplicate_dbopen) {
	r = (DB->close)(dupdb);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error closing deliverdb: %s",
		   cyrusdb_strerror(r));
	}
	duplicate_dbopen = 0;
    }

    return r;
}
