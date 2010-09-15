/* quota_db.c -- quota manipulation routines
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
 * $Id: quota_db.c,v 1.11 2010/01/06 17:01:39 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <syslog.h>

#include "assert.h"
#include "cyrusdb.h"
#include "exitcodes.h"
#include "global.h"
#include "imap_err.h"
#include "mailbox.h"
#include "quota.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

#define QDB config_quota_db

struct db *qdb;

static int quota_dbopen = 0;

/*
 * Read the quota entry 'quota'
 */
int quota_read(struct quota *quota, struct txn **tid, int wrlock)
{
    int r;
    int qrlen;
    const char *data;
    int datalen;

    if (!quota->root || !(qrlen = strlen(quota->root)))
	return IMAP_QUOTAROOT_NONEXISTENT;

    if (wrlock)
	r = QDB->fetchlock(qdb, quota->root, qrlen, &data, &datalen, tid);
    else
	r = QDB->fetch(qdb, quota->root, qrlen, &data, &datalen, tid);

    switch (r) {
    case CYRUSDB_OK:
	if (!*data || sscanf(data, UQUOTA_T_FMT " %d", 
			     &quota->used, &quota->limit) != 2) {
            char *buf = xstrndup(data, datalen);
            syslog(LOG_ERR, "DBERROR: parsed bogus quota data <%s> for %s",
               buf, quota->root);
            free(buf);
	    r = CYRUSDB_IOERROR;
	}
	break;

    case CYRUSDB_AGAIN:
	return IMAP_AGAIN;
	break;

    case CYRUSDB_NOTFOUND:
	return IMAP_QUOTAROOT_NONEXISTENT;
	break;
    }

    if (r) {
	syslog(LOG_ERR, "DBERROR: error fetching quota %s: %s",
	       quota->root, cyrusdb_strerror(r));
	return IMAP_IOERROR;
    }

    return 0;
}

/*
 * Commit the outstanding quota transaction
 */
void quota_commit(struct txn **tid)
{
    if (tid && *tid) {
	if (QDB->commit(qdb, *tid)) {
	    syslog(LOG_ERR, "IOERROR: committing quota: %m");
	}
	*tid = NULL;
    }
}

/*
 * Abort the outstanding quota transaction
 */
void quota_abort(struct txn **tid)
{
    if (tid && *tid) {
	if (QDB->abort(qdb, *tid)) {
	    syslog(LOG_ERR, "IOERROR: aborting quota: %m");
	}
	*tid = NULL;
    }
}

/*
 * Write out the quota entry 'quota'
 */
int quota_write(struct quota *quota, struct txn **tid)
{
    int r;
    int qrlen, len;
    char buf[1024];

    if (!quota->root) return 0;

    qrlen = strlen(quota->root);
    if (!qrlen) return IMAP_QUOTAROOT_NONEXISTENT;

    len = snprintf(buf, sizeof(buf) - 1,
		   UQUOTA_T_FMT " %d", quota->used, quota->limit);
    r = QDB->store(qdb, quota->root, qrlen, buf, len, tid);
    
    switch (r) {
    case CYRUSDB_OK:
	break;

    case CYRUSDB_AGAIN:
	return IMAP_AGAIN;
	break;

    default:
	syslog(LOG_ERR, "DBERROR: error storing %s: %s",
	       quota->root, cyrusdb_strerror(r));
	return IMAP_IOERROR;
	break;
    }

    return 0;
}

/*
 * Remove the quota root 'quota'
 */
int quota_deleteroot(const char *quotaroot)
{
    int qrlen;

    qrlen = strlen(quotaroot);
    if (!qrlen) return IMAP_QUOTAROOT_NONEXISTENT;

    return QDB->delete(qdb, quotaroot, qrlen, NULL, 0);
}

/*
 * Find the mailbox 'name' 's quotaroot, and return it in 'ret'.
 * 'ret' must be at least MAX_MAILBOX_NAME.
 *
 * returns true if a quotaroot is found, 0 otherwise. 
*/
int quota_findroot(char *ret, size_t retlen, const char *name)
{
    char *tail, *p, *mbox;

    strlcpy(ret, name, retlen);

    /* find the start of the unqualified mailbox name */
    mbox = (config_virtdomains && (p = strchr(ret, '!'))) ? p+1 : ret;
    tail = mbox + strlen(mbox);

    while (QDB->fetch(qdb, ret, strlen(ret), NULL, NULL, NULL)) {
	tail = strrchr(mbox, '.');
	if (!tail) break;
	*tail = '\0';
    }
    if (tail) return 1;
    if (mbox == ret) return 0;

    /* check for a domain quota */
    *mbox = '\0';
    return (QDB->fetch(qdb, ret, strlen(ret), NULL, NULL, NULL) == 0);
}


/* must be called after cyrus_init */
void quotadb_init(int myflags)
{
    int r;

    if (myflags & QUOTADB_SYNC) {
	r = QDB->sync();
    }
}

void quotadb_open(char *fname)
{
    int ret;
    char *tofree = NULL;

    /* create db file name */
    if (!fname) {
	size_t fname_len = strlen(config_dir)+strlen(FNAME_QUOTADB)+1;
	
	fname = xmalloc(fname_len);
	tofree = fname;

	strlcpy(fname, config_dir, fname_len);
	strlcat(fname, FNAME_QUOTADB, fname_len);
    }

    ret = (QDB->open)(fname, CYRUSDB_CREATE, &qdb);
    if (ret != 0) {
	syslog(LOG_ERR, "DBERROR: opening %s: %s", fname,
	       cyrusdb_strerror(ret));
	    /* Exiting TEMPFAIL because Sendmail thinks this
	       EC_OSFILE == permanent failure. */
	fatal("can't read quotas file", EC_TEMPFAIL);
    }

    if (tofree) free(tofree);

    quota_dbopen = 1;
}

void quotadb_close(void)
{
    int r;

    if (quota_dbopen) {
	r = (QDB->close)(qdb);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error closing quotas: %s",
		   cyrusdb_strerror(r));
	}
	quota_dbopen = 0;
    }
}

void quotadb_done(void)
{
    /* DB->done() handled by cyrus_done() */
}
