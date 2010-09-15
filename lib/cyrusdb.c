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
 * $Id: cyrusdb.c,v 1.14 2010/01/06 17:01:44 murch Exp $
 */

#include <config.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <errno.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include "cyrusdb.h"
#include "exitcodes.h"
#include "libcyr_cfg.h"
#include "retry.h"
#include "xmalloc.h"

struct cyrusdb_backend *cyrusdb_backends[] = {
#ifdef HAVE_BDB
    &cyrusdb_berkeley,
    &cyrusdb_berkeley_nosync,
    &cyrusdb_berkeley_hash,
    &cyrusdb_berkeley_hash_nosync,
#endif
    &cyrusdb_flat,
    &cyrusdb_skiplist,
    &cyrusdb_quotalegacy,
#if defined HAVE_MYSQL || defined HAVE_PGSQL || defined HAVE_SQLITE
    &cyrusdb_sql,
#endif
    NULL };

void cyrusdb_init() 
{
    int i, r;
    char dbdir[1024];
    const char *confdir = libcyrus_config_getstring(CYRUSOPT_CONFIG_DIR);
    int initflags = libcyrus_config_getint(CYRUSOPT_DB_INIT_FLAGS);
    
    strcpy(dbdir, confdir);
    strcat(dbdir, FNAME_DBDIR);

    for(i=0; cyrusdb_backends[i]; i++) {
	r = (cyrusdb_backends[i])->init(dbdir, initflags);
	if(r) {
	    syslog(LOG_ERR, "DBERROR: init() on %s",
		   cyrusdb_backends[i]->name);
	}
    }
}

void cyrusdb_done() 
{
    int i;
    
    for(i=0; cyrusdb_backends[i]; i++) {
	(cyrusdb_backends[i])->done();
    }
}

int cyrusdb_copyfile(const char *srcname, const char *dstname)
{
    int srcfd, dstfd;
    struct stat sbuf;
    char buf[4096];
    int n;

    if ((srcfd = open(srcname, O_RDONLY)) < 0) {
	syslog(LOG_DEBUG, "error opening %s for reading", srcname);
	return -1;
    }

    if (fstat(srcfd, &sbuf) < 0) {
	syslog(LOG_DEBUG, "error fstating %s", srcname);
	close(srcfd);
	return -1;
    }

    if ((dstfd = open(dstname, O_WRONLY | O_CREAT, sbuf.st_mode)) < 0) {
	syslog(LOG_DEBUG, "error opening %s for writing (%d)",
	       dstname, sbuf.st_mode);
	close(srcfd);
	return -1;
    }

    for (;;) {
	n = read(srcfd, buf, 4096);

	if (n < 0) {
	    if (errno == EINTR)
		continue;

	    syslog(LOG_DEBUG, "error reading buf");
	    close(srcfd);
	    close(dstfd);
	    unlink(dstname);
	    return -1;
	}

	if (n == 0)
	    break;

	if (retry_write(dstfd, buf, n) != n) {
	    syslog(LOG_DEBUG, "error writing buf (%d)", n);
	    close(srcfd);
	    close(dstfd);
	    unlink(dstname);
	    return -1;
	}
    }

    close(srcfd);
    close(dstfd);
    return 0;
}

struct convert_rock {
    struct cyrusdb_backend *backend;
    struct db *db;
    struct txn *tid;
};

static int converter_cb(void *rock,
			const char *key, int keylen,
			const char *data, int datalen) 
{
    struct convert_rock *cr = (struct convert_rock *)rock;
    return (cr->backend->store)(cr->db, key, keylen, data, datalen, &cr->tid);
}

/* convert (just copy every record) from one database to another in possibly
   a different format.  It's up to the surrounding code to copy the
   new database over the original if it wants to */
void cyrusdb_convert(const char *fromfname, const char *tofname,
		     struct cyrusdb_backend *frombackend,
		     struct cyrusdb_backend *tobackend)
{
    struct db *fromdb, *todb;
    struct convert_rock cr;
    struct txn *fromtid = NULL;
    int r;

    /* open both databases (create todb) */
    r = (frombackend->open)(fromfname, 0, &fromdb);
    if (r != CYRUSDB_OK)
	fatal("can't open old database", EC_TEMPFAIL);
    r = (tobackend->open)(tofname, CYRUSDB_CREATE, &todb);
    if (r != CYRUSDB_OK)
	fatal("can't open new database", EC_TEMPFAIL);

    /* set up the copy rock */
    cr.backend = tobackend;
    cr.db = todb;
    cr.tid = NULL;

    /* copy each record to the destination DB (transactional for speed) */
    (frombackend->foreach)(fromdb, "", 0, NULL, converter_cb, &cr, &fromtid);

    /* commit both transactions */
    if (fromtid) (frombackend->commit)(fromdb, fromtid);
    if (cr.tid) (tobackend->commit)(todb, cr.tid);

    /* and close the DBs */
    (frombackend->close)(fromdb);
    (tobackend->close)(todb);
}

const char *cyrusdb_detect(const char *fname)
{
    FILE *f;
    char buf[16];
    int n;
    uint32_t bdb_magic;

    f = fopen(fname, "r");
    if (!f) return NULL;

    /* empty file? */
    n = fread(buf, 16, 1, f);
    fclose(f);

    if (n != 1) return NULL;

    /* only compare first 16 bytes, that's OK */
    if (!strncmp(buf, "\241\002\213\015skiplist file\0\0\0", 16))
	return "skiplist";

    bdb_magic = *(uint32_t *)(buf+12);

    if (bdb_magic == 0x053162) /* BDB BTREE MAGIC */
	return "berkeley";

    if (bdb_magic == 0x061561) /* BDB HASH MAGIC */
	return "berkeley-hash";

    /* unable to detect SQLite databases or flat files explicitly here */
    return NULL;
}

struct cyrusdb_backend *cyrusdb_fromname(const char *name)
{
    int i;
    struct cyrusdb_backend *db = NULL;

    for (i = 0; cyrusdb_backends[i]; i++) {
	if (!strcmp(cyrusdb_backends[i]->name, name)) {
	    db = cyrusdb_backends[i]; break;
	}
    }
    if (!db) {
	char errbuf[1024];
	snprintf(errbuf, sizeof(errbuf),
		 "cyrusdb backend %s not supported", name);
	fatal(errbuf, EC_CONFIG);
    }

    return db;
}
