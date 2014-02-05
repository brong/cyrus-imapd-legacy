/* zoneinfo_db.c -- zoneinfo DB routines
 *
 * Copyright (c) 1994-2013 Carnegie Mellon University.  All rights reserved.
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

#include "assert.h"
#include "cyrusdb.h"
#include "exitcodes.h"
#include "global.h"
#include "tok.h"
#include "util.h"
#include "xmalloc.h"

#include "zoneinfo_db.h"

//#define FIND_CONTAINS

#define DB config_zoneinfo_db

struct db *zoneinfodb;
static int zoneinfo_dbopen = 0;
static struct buf databuf = BUF_INITIALIZER;

EXPORTED int zoneinfo_open(const char *fname)
{
    int ret;
    char *tofree = NULL;

    if (!fname) fname = config_getstring(IMAPOPT_ZONEINFO_DB_PATH);

    /* create db file name */
    if (!fname) {
	tofree = strconcat(config_dir, FNAME_ZONEINFODB, (char *)NULL);
	fname = tofree;
    }

    ret = DB->open(fname, CYRUSDB_CREATE, &zoneinfodb);
    if (ret != 0) {
	syslog(LOG_ERR, "DBERROR: opening %s: %s", fname,
	       cyrusdb_strerror(ret));
    }
    else zoneinfo_dbopen = 1;

    free(tofree);

    return ret;
}

void zoneinfo_close(struct txn *tid)
{
    if (zoneinfo_dbopen) {
	int r;

	if (tid) {
	    r = DB->commit(zoneinfodb, tid);
	    if (r) {
		syslog(LOG_ERR, "DBERROR: error committing zoneinfo: %s",
		       cyrusdb_strerror(r));
	    }
	}
	r = DB->close(zoneinfodb);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error closing zoneinfo: %s",
		   cyrusdb_strerror(r));
	}
	zoneinfo_dbopen = 0;

	buf_free(&databuf);
    }
}

void zoneinfo_done(void)
{
    /* DB->done() handled by cyrus_done() */
}

static int parse_zoneinfo(const char *data, int datalen,
			  struct zoneinfo *zi, int all)
{
    const char *dend = data + datalen;
    unsigned version;
    char *p;

    memset(zi, 0, sizeof(struct zoneinfo));

    /* version SP type SP dtstamp SP (string *(TAB string)) */

    version = strtoul(data, &p, 10);
    if (version != ZONEINFO_VERSION) return CYRUSDB_IOERROR;

    if (p < dend) zi->type = strtoul(p, &p, 10);
    if (p < dend) zi->dtstamp = strtol(p, &p, 10);

    if (all && p < dend) {
	size_t len = dend - ++p;
	char *str = xstrndup(p, len);
	tok_t tok;

	tok_initm(&tok, str, "\t", TOK_FREEBUFFER);
	while ((str = tok_next(&tok))) appendstrlist(&zi->data, str);
	tok_fini(&tok);
    }

    return 0;
}

EXPORTED int zoneinfo_lookup(const char *tzid, struct zoneinfo *zi)
{
    int r, datalen;
    const char *data = NULL;

    /* Don't access DB if it hasn't been opened */
    if (!zoneinfo_dbopen) return CYRUSDB_INTERNAL;

    assert(tzid);

    /* Check if there is an entry in the database */
    do {
	r = DB->fetch(zoneinfodb, tzid, strlen(tzid), &data, &datalen, NULL);
    } while (r == CYRUSDB_AGAIN);

    if (r || !data || (datalen < 6)) return r ? r : CYRUSDB_IOERROR;

    return parse_zoneinfo(data, datalen, zi, 1);
}

EXPORTED int zoneinfo_store(const char *tzid, struct zoneinfo *zi, struct txn **tid)
{
    struct strlist *sl;
    const char *sep;
    int r;

    /* Don't access DB if it hasn't been opened */
    if (!zoneinfo_dbopen) return CYRUSDB_INTERNAL;

    assert(tzid && zi);

    /* version SP type SP dtstamp SP (string *(TAB string)) */
    buf_reset(&databuf);
    buf_printf(&databuf, "%u %u %ld ", ZONEINFO_VERSION, zi->type, zi->dtstamp);
    for (sl = zi->data, sep = ""; sl; sl = sl->next, sep = "\t")
	buf_printf(&databuf, "%s%s", sep, sl->s);

    r = DB->store(zoneinfodb, tzid, strlen(tzid),
		  buf_cstring(&databuf), buf_len(&databuf), tid);

    if (r != CYRUSDB_OK) {
	syslog(LOG_ERR, "DBERROR: error updating zoneinfo: %s (%s)",
	       tzid, cyrusdb_strerror(r));
    }

    return r; 
}


#ifdef FIND_CONTAINS
/*
 * Find the first occurrence of find in s, where the search is limited to the
 * first slen characters of s.
 *
 * Copyright (c) 2001 Mike Barcroft <mike@FreeBSD.org>
 * Copyright (c) 1990, 1993
 *     The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Chris Torek.
 *
 * Fix for case-insensitive match of first char added by Ken Murchison
 */
static char *strncasestr(const char *s, const char *find, size_t slen)
{
    char c, sc;
    size_t len;

    if ((c = tolower(*find++)) != '\0') {
	len = strlen(find);
	do {
	    do {
		if ((sc = *s++) == '\0' || slen-- < 1) return (NULL);
	    } while (tolower(sc) != c);

	    if (len > slen) return (NULL);
	} while (strncasecmp(s, find, len) != 0);

	s--;
    }

    return ((char *)s);
}
#endif /* FIND_CONTAINS */

struct findrock {
    const char *find;
    int tzid_only;
    time_t changedsince;
    int (*proc)();
    void *rock;
};

static int find_p(void *rock,
		  const char *tzid __attribute__((unused)), int tzidlen,
		  const char *data, int datalen)
{
    struct findrock *frock = (struct findrock *) rock;
    struct zoneinfo zi;

    if (parse_zoneinfo(data, datalen, &zi, 0)) return 0;

    switch (zi.type) {
    case ZI_INFO: return 0;

    case ZI_LINK:
	if (frock->tzid_only) return 0;
	break;

    case ZI_ZONE:
	if (zi.dtstamp <= frock->changedsince) return 0;
	break;
    }

    if (!frock->find) return 1;
    else if (frock->tzid_only) return (tzidlen == (int) strlen(frock->find));
#ifdef FIND_CONTAINS
    else return (strncasestr(tzid, frock->find, tzidlen) != NULL);
#else
    else return 1;
#endif
}

static int find_cb(void *rock,
		   const char *tzid, int tzidlen,
		   const char *data, int datalen)
{
    struct findrock *frock = (struct findrock *) rock;
    struct zoneinfo zi;
    int r;

    r = parse_zoneinfo(data, datalen, &zi, 1);
    if (!r) {
	struct strlist *linkto = NULL;

	if (zi.type == ZI_LINK) {
	    linkto = zi.data;
	    zi.data = NULL;

	    tzid = linkto->s;
	    tzidlen = strlen(tzid);
	    r = zoneinfo_lookup(tzid, &zi);
	}
	if (!r) r = (*frock->proc)(tzid, tzidlen, &zi, frock->rock);
	freestrlist(zi.data);
	freestrlist(linkto);
    }

    return r;
}

EXPORTED int zoneinfo_find(const char *find, int tzid_only, time_t changedsince,
		  int (*proc)(), void *rock)
{
    struct findrock frock;

    /* Don't access DB if it hasn't been opened */
    if (!zoneinfo_dbopen) return CYRUSDB_INTERNAL;

    assert(proc);

    frock.find = find;
    frock.tzid_only = tzid_only;
    frock.changedsince = changedsince;
    frock.proc = proc;
    frock.rock = rock;

    if (!find
#ifdef FIND_CONTAINS
	|| !tzid_only
#endif
	) find = "";

    /* process each matching entry in our database */
    return DB->foreach(zoneinfodb, (char *) find, strlen(find),
		       &find_p, &find_cb, &frock, NULL);
}
