/*  cyrusdb_berkeley: berkeley db backends
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
 * $Id: cyrusdb_berkeley.c,v 1.24 2010/01/06 17:01:45 murch Exp $
 */

#include <config.h>

#include <db.h>
#include <syslog.h>
#include <string.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>

#include "assert.h"
#include "bsearch.h"
#include "cyrusdb.h"
#include "exitcodes.h"
#include "libcyr_cfg.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

extern void fatal(const char *, int);

/* --- cut here --- */
/*
 * what berkeley db algorithm should we use for deadlock detection?
 * 
 * DB_LOCK_DEFAULT
 *    Use the default policy as specified by db_deadlock. 
 * DB_LOCK_OLDEST
 *    Abort the oldest transaction. 
 * DB_LOCK_RANDOM
 *    Abort a random transaction involved in the deadlock. 
 * DB_LOCK_YOUNGEST
 *    Abort the youngest transaction. 
 */

#define CONFIG_DEADLOCK_DETECTION DB_LOCK_YOUNGEST
#define MIN_CACHESIZE 20	/* 20KB per Sleepycat docs */
#define MAX_CACHESIZE 4194303	/* UINT32_MAX / 1024 */

/* --- cut here --- */

#if DB_VERSION_MAJOR >= 4
#define txn_checkpoint(xx1,xx2,xx3,xx4) (xx1)->txn_checkpoint(xx1,xx2,xx3,xx4)
#define txn_id(xx1) (xx1)->id(xx1)
#define log_archive(xx1,xx2,xx3,xx4) (xx1)->log_archive(xx1,xx2,xx3)
#define txn_begin(xx1,xx2,xx3,xx4) (xx1)->txn_begin(xx1,xx2,xx3,xx4)
#define txn_commit(xx1,xx2) (xx1)->commit(xx1,xx2)
#define txn_abort(xx1) (xx1)->abort(xx1)
#elif DB_VERSION_MINOR == 3
#define log_archive(xx1,xx2,xx3,xx4) log_archive(xx1,xx2,xx3)
#endif

static int dbinit = 0;
static DB_ENV *dbenv;

/* other routines call this one when they fail */
static int commit_txn(struct db *db, struct txn *tid);
static int abort_txn(struct db *db, struct txn *tid);

static void db_panic(DB_ENV *dbenv __attribute__((unused)),
		     int errno __attribute__((unused)))
{
    syslog(LOG_CRIT, "DBERROR: critical database situation");
    /* but don't bounce mail */
    exit(EC_TEMPFAIL);
}

#if (DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 3)
static void db_err(const DB_ENV *dbenv __attribute__((unused)),
		   const char *db_prfx, const char *buffer)
#else
static void db_err(const char *db_prfx, char *buffer)
#endif
{
    syslog(LOG_WARNING, "DBERROR %s: %s", db_prfx, buffer);
}

static void db_msg(const DB_ENV *dbenv __attribute__((unused)),
		   const char *msg)
{
    syslog(LOG_INFO, "DBMSG: %s", msg);
}

static int init(const char *dbdir, int myflags)
{
    int r, do_retry = 1;
    int flags = 0;
    int maj, min, patch;
    static char errpfx[10]; /* needs to be static; bdb doesn't copy */
    int opt;

    if (dbinit++) return 0;

    db_version(&maj, &min, &patch);
    if (maj != DB_VERSION_MAJOR || min != DB_VERSION_MINOR ||
	DB_VERSION_PATCH > patch) {
	syslog(LOG_CRIT, "incorrect version of Berkeley db: "
	       "compiled against %d.%d.%d, linked against %d.%d.%d",
	       DB_VERSION_MAJOR, DB_VERSION_MINOR, DB_VERSION_PATCH,
	       maj, min, patch);
	fatal("wrong db version", EC_SOFTWARE);
    }

    if (myflags & CYRUSDB_RECOVER) {
      flags |= DB_RECOVER | DB_CREATE;
    }

    if ((r = db_env_create(&dbenv, 0)) != 0) {
	syslog(LOG_ERR, "DBERROR: db_appinit failed: %s", db_strerror(r));
	return CYRUSDB_IOERROR;
    }
    dbenv->set_paniccall(dbenv, (void (*)(DB_ENV *, int)) &db_panic);
    if (CONFIG_DB_VERBOSE) {
	dbenv->set_verbose(dbenv, DB_VERB_DEADLOCK, 1);
	dbenv->set_verbose(dbenv, DB_VERB_WAITSFOR, 1);
    }
    if (CONFIG_DB_VERBOSE > 1) {
#ifdef DB_VERB_CHKPOINT
	dbenv->set_verbose(dbenv, DB_VERB_CHKPOINT, 1);
#endif
    }

#if (DB_VERSION_MAJOR == 4) && (DB_VERSION_MINOR >= 3)
    dbenv->set_msgcall(dbenv, db_msg);
#endif
    dbenv->set_errcall(dbenv, db_err);
    snprintf(errpfx, sizeof(errpfx), "db%d", DB_VERSION_MAJOR);
    dbenv->set_errpfx(dbenv, errpfx);

    dbenv->set_lk_detect(dbenv, CONFIG_DEADLOCK_DETECTION);

    if ((opt = libcyrus_config_getint(CYRUSOPT_BERKELEY_LOCKS_MAX)) < 0) {
	syslog(LOG_WARNING,
	       "DBERROR: invalid berkeley_locks_max value, using internal default");
    } else {
#if DB_VERSION_MAJOR >= 4
	r = dbenv->set_lk_max_locks(dbenv, opt);
	if (!r)
	    r = dbenv->set_lk_max_lockers(dbenv, opt);
	if (!r)
	    r = dbenv->set_lk_max_objects(dbenv, opt);
#else
	r = dbenv->set_lk_max(dbenv, opt);
#endif
	if (r) {
	    dbenv->err(dbenv, r, "set_lk_max");
	    syslog(LOG_ERR, "DBERROR: set_lk_max(): %s", db_strerror(r));
	    abort();
	}
    }

    if ((opt = libcyrus_config_getint(CYRUSOPT_BERKELEY_TXNS_MAX)) < 0) {
	syslog(LOG_WARNING,
	       "DBERROR: invalid berkeley_txns_max value, using internal default");
    } else {
	r = dbenv->set_tx_max(dbenv, opt);
	if (r) {
	    dbenv->err(dbenv, r, "set_tx_max");
	    syslog(LOG_ERR, "DBERROR: set_tx_max(): %s", db_strerror(r));
	    abort();
	}
    }

    opt = libcyrus_config_getint(CYRUSOPT_BERKELEY_CACHESIZE);
    if (opt < MIN_CACHESIZE || opt > MAX_CACHESIZE) {
	syslog(LOG_WARNING,
	       "DBERROR: invalid berkeley_cachesize value, using internal default");
    } else {
	r = dbenv->set_cachesize(dbenv, 0, opt * 1024, 0);
	if (r) {
	    dbenv->err(dbenv, r, "set_cachesize");
	    (dbenv->close)(dbenv, 0);
	    syslog(LOG_ERR, "DBERROR: set_cachesize(): %s", db_strerror(r));
	    return CYRUSDB_IOERROR;
	}
    }

    /* what directory are we in? */
 retry:
    flags |= DB_INIT_LOCK | DB_INIT_MPOOL | 
	     DB_INIT_LOG | DB_INIT_TXN;
#if (DB_VERSION_MAJOR > 3) || ((DB_VERSION_MAJOR == 3) && (DB_VERSION_MINOR > 0))
    r = (dbenv->open)(dbenv, dbdir, flags, 0644); 
#else
    r = (dbenv->open)(dbenv, dbdir, NULL, flags, 0644); 
#endif
    if (r) {
        if (do_retry && (r == ENOENT)) {
	  /* Per sleepycat Support Request #3838 reporting a performance problem: 

	        Berkeley DB only transactionally protects the open if you're
	        doing a DB_CREATE.  Even if the Cyrus application is opening
  	        the file read/write, we don't need a transaction.  I see
	        from their source that they are always specifying DB_CREATE.
	        I bet if they changed it to not specifying CREATE and only
	        creating if necessary, the problem would probably go away.

	     Given that in general the file should exist, we optimize the most 
	     often case: the file exists.  So, we add DB_CREATE only if we fail 
	     to open the file and thereby avoid doing a stat(2) needlessly. Sure, it 
	     should be cached by why waste the cycles anyway?
	  */
	  flags |= DB_CREATE;
	  do_retry = 0;
	  goto retry;
        }
	
	syslog(LOG_ERR, "DBERROR: dbenv->open '%s' failed: %s", dbdir,
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }

    dbinit = 1;

    return 0;
}

static int done(void)
{
    int r;

    if (--dbinit) return 0;

    r = (dbenv->close)(dbenv, 0);
    dbinit = 0;
    if (r) {
	syslog(LOG_ERR, "DBERROR: error exiting application: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }

    return 0;
}

static int mysync(void)
{
    int r;

    assert(dbinit);

#if !(DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR >= 1)
    do {
#endif
#if (DB_VERSION_MAJOR > 3) || ((DB_VERSION_MAJOR == 3) && (DB_VERSION_MINOR > 0))
	r = txn_checkpoint(dbenv, 0, 0, 0);
#else
	r = txn_checkpoint(dbenv, 0, 0);
#endif
#if !(DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR >= 1)
    } while (r == DB_INCOMPLETE);  /* Never returned by BDB 4.1 */
#endif
    if (r) {
	syslog(LOG_ERR, "DBERROR: couldn't checkpoint: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }

    return 0;
}

static int myarchive(const char **fnames, const char *dirname)
{
    int r;
    char **begin, **list;
    const char **fname;
    char dstname[1024], *dp;
    int length, rest;

    strlcpy(dstname, dirname, sizeof(dstname));
    length = strlen(dstname);
    dp = dstname + length;
    rest = sizeof(dstname) - length;

    /* Get the list of log files to remove. */
    r = log_archive(dbenv, &list, DB_ARCH_ABS, NULL);
    if (r) {
	syslog(LOG_ERR, "DBERROR: error listing log files: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }
    if (list != NULL) {
	for (begin = list; *list != NULL; ++list) {
	    syslog(LOG_DEBUG, "removing log file: %s", *list);
	    r = unlink(*list);
	    if (r) {
		syslog(LOG_ERR, "DBERROR: error removing log file: %s",
		       *list);
		return CYRUSDB_IOERROR;
	    }
	}
	free (begin);
    }

    /* Get the list of database files to archive. */
    /* XXX  Should we do this, or just use the list given to us? */
    r = log_archive(dbenv, &list, DB_ARCH_ABS | DB_ARCH_DATA, NULL);
    if (r) {
	syslog(LOG_ERR, "DBERROR: error listing database files: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }
    if (list != NULL) {
	for (begin = list; *list != NULL; ++list) {
	    /* only archive those files specified by the app */
	    for (fname = fnames; *fname != NULL; ++fname) {
		if (!strcmp(*list, *fname)) break;
	    }
	    if (*fname) {
		syslog(LOG_DEBUG, "archiving database file: %s", *fname);
		strlcpy(dp, strrchr(*fname, '/'), rest);
		r = cyrusdb_copyfile(*fname, dstname);
		if (r) {
		    syslog(LOG_ERR,
			   "DBERROR: error archiving database file: %s",
			   *fname);
		    return CYRUSDB_IOERROR;
		}
	    }
	}
	free (begin);
    }

    /* Get the list of log files to archive. */
    r = log_archive(dbenv, &list, DB_ARCH_ABS | DB_ARCH_LOG, NULL);
    if (r) {
	syslog(LOG_ERR, "DBERROR: error listing log files: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }
    if (list != NULL) {
	for (begin = list; *list != NULL; ++list) {
	    syslog(LOG_DEBUG, "archiving log file: %s", *list);
	    strcpy(dp, strrchr(*list, '/'));
	    r = cyrusdb_copyfile(*list, dstname);
	    if (r) {
		syslog(LOG_ERR, "DBERROR: error archiving log file: %s",
		       *list);
		return CYRUSDB_IOERROR;
	    }
	}
	free (begin);
    }

    return 0;
}

static int mbox_compar(DB *db __attribute__((unused)),
		       const DBT *a, const DBT *b)
{
    return bsearch_ncompare((const char *) a->data, a->size,
			    (const char *) b->data, b->size);
}

static int myopen(const char *fname, DBTYPE type, int flags, struct db **ret)
{
    DB *db = NULL;
    int r;
    int dbflags = (flags & CYRUSDB_CREATE) ? DB_CREATE : 0;

    assert(dbinit && fname && ret);

    *ret = NULL;

    r = db_create(&db, dbenv, 0);
    if (r != 0) {
	syslog(LOG_ERR, "DBERROR: opening %s (creating database handle): %s", fname, db_strerror(r));
	return CYRUSDB_IOERROR;
    }
    /* xxx set comparator! */
    if (flags & CYRUSDB_MBOXSORT) db->set_bt_compare(db, mbox_compar);

#if DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR >= 1
    r = (db->open)(db, NULL, fname, NULL, type, dbflags | DB_AUTO_COMMIT, 0664);
#else
    r = (db->open)(db, fname, NULL, type, dbflags, 0664);
#endif

    if (r != 0) {
	int level = (flags & CYRUSDB_CREATE) ? LOG_ERR : LOG_DEBUG;
	syslog(level, "DBERROR: opening %s: %s", fname, db_strerror(r));
	r = (db->close)(db, DB_NOSYNC);
        if (r != 0) {
            syslog(level, "DBERROR: closing %s: %s", fname, db_strerror(r));
        }
	return CYRUSDB_IOERROR;
    }

    *ret = (struct db *) db;

    return r;
}

static int open_btree(const char *fname, int flags, struct db **ret)
{
    return myopen(fname, DB_BTREE, flags, ret);
}

static int open_hash(const char *fname, int flags, struct db **ret)
{
    return myopen(fname, DB_HASH, flags, ret);
}

static int myclose(struct db *db)
{
    int r;
    DB *a = (DB *) db;

    assert(dbinit && db);

    /* since we're using txns, we can supply DB_NOSYNC */
    r = (a->close)(a, DB_NOSYNC);
    if (r != 0) {
	syslog(LOG_ERR, "DBERROR: error closing: %s", db_strerror(r));
	r = CYRUSDB_IOERROR;
    }

    return r;
}

static int gettid(struct txn **mytid, DB_TXN **tid, char *where)
{
    int r;

    if (mytid) {
	if (*mytid) {
  	    assert((txn_id((DB_TXN *)*mytid) != 0));
	    *tid = (DB_TXN *) *mytid;
	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "%s: reusing txn %lu", where,
		       (unsigned long) txn_id(*tid));
	} else {
	    r = txn_begin(dbenv, NULL, tid, 0);
	    if (r != 0) {
		syslog(LOG_ERR, "DBERROR: error beginning txn (%s): %s", where,
		       db_strerror(r));
		return CYRUSDB_IOERROR;
	    }
	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "%s: starting txn %lu", where,
		       (unsigned long) txn_id(*tid));
	}
	*mytid = (struct txn *) *tid;
    }

    return 0;
}

static int myfetch(struct db *mydb, 
		   const char *key, int keylen,
		   const char **data, int *datalen,
		   struct txn **mytid, int flags)
{
    int r = 0;
    DBT k, d;
    DB *db = (DB *) mydb;
    DB_TXN *tid = NULL;
	
    assert(dbinit && db);

    if (data) *data = NULL;
    if (datalen) *datalen = 0;

    r = gettid(mytid, &tid, "myfetch");
    if (r) return r;

    memset(&k, 0, sizeof(k));
    memset(&d, 0, sizeof(d));

    k.data = (char *) key;
    k.size = keylen;

    r = db->get(db, tid, &k, &d, flags);
    switch (r) {
    case 0:
	if (data) *data = d.data;
	if (datalen) *datalen = d.size;
	break;
    case DB_NOTFOUND:
	r = CYRUSDB_NOTFOUND;
	break;
    case DB_LOCK_DEADLOCK:
	if (mytid) {
	    abort_txn(mydb, *mytid);
	    *mytid = NULL;
	}
	r = CYRUSDB_AGAIN;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error fetching %s: %s", key,
	       db_strerror(r));
	r = CYRUSDB_IOERROR;
	break;
    }

    return r;
}

static int fetch(struct db *mydb, 
		 const char *key, int keylen,
		 const char **data, int *datalen,
		 struct txn **mytid)
{
    return myfetch(mydb, key, keylen, data, datalen, mytid, 0);
}

static int fetchlock(struct db *mydb, 
		     const char *key, int keylen,
		     const char **data, int *datalen,
		     struct txn **mytid)
{
    return myfetch(mydb, key, keylen, data, datalen, mytid, DB_RMW);
}

#define OPENCURSOR() do { \
    r = db->cursor(db, tid, &cursor, 0); \
    if (r != 0) { \
	syslog(LOG_ERR, "DBERROR: unable to create cursor: %s", \
	       db_strerror(r)); \
	cursor = NULL; \
	goto done; \
    } \
 } while (0)

#define CLOSECURSOR() do { \
    int r = cursor->c_close(cursor); \
    if (r) { \
	syslog(LOG_ERR, "DBERROR: error closing cursor: %s", \
	       db_strerror(r)); \
	cursor = NULL; \
	goto done; \
    } \
 } while (0)


/* instead of "DB_DBT_REALLOC", we might want DB_DBT_USERMEM and allocate
   this to the maximum length at the beginning. */
static int foreach(struct db *mydb,
		   char *prefix, int prefixlen,
		   foreach_p *goodp,
		   foreach_cb *cb, void *rock, 
		   struct txn **mytid)
{
    int r = 0;
    DBT k, d;
    DBC *cursor = NULL;
    DB *db = (DB *) mydb;
    DB_TXN *tid = NULL;

    assert(dbinit && db);
    assert(cb);

    memset(&k, 0, sizeof(k));
    memset(&d, 0, sizeof(d));

    /* k.flags |= DB_DBT_REALLOC;
       d.flags |= DB_DBT_REALLOC;*/

    r = gettid(mytid, &tid, "foreach");
    if (r) return r;

    if (0) {
    restart:
	CLOSECURSOR();
    }

    /* create cursor */
    OPENCURSOR();

    /* find first record */
    if (prefix && *prefix) {
	/* if (k.data) free(k.data); */
	k.data = prefix;
	k.size = prefixlen;

	r = cursor->c_get(cursor, &k, &d, DB_SET_RANGE);
    } else {
	r = cursor->c_get(cursor, &k, &d, DB_FIRST);
    }
    if (!tid && r == DB_LOCK_DEADLOCK) goto restart;
	
    /* iterate over all mailboxes matching prefix */
    while (!r) {
	/* does this match our prefix? */
	if (prefixlen && memcmp(k.data, prefix, prefixlen)) break;

	if (!goodp || goodp(rock, k.data, k.size, d.data, d.size)) {
	    /* we have a winner! */

	    /* close the cursor, so we're not holding locks 
	       during a callback */
	    CLOSECURSOR(); cursor = NULL;

	    r = cb(rock, k.data, k.size, d.data, d.size);
            if (r != 0) {
                if (r < 0) {
                    syslog(LOG_ERR, "DBERROR: foreach cb() failed");
                }
                /* don't mistake this for a db error */
                r = 0;

                break;
            }

	    /* restore the current location & advance */
	    OPENCURSOR();
	    
	    r = cursor->c_get(cursor, &k, &d, DB_SET);
	    switch (r) {
	    case 0:
		r = cursor->c_get(cursor, &k, &d, DB_NEXT);
		break;

	    case DB_NOTFOUND:
		/* deleted during callback? */
		r = cursor->c_get(cursor, &k, &d, DB_SET_RANGE);
		break;

	    default:
		/* handle other cases below */
		break;
	    }
	} else {
	    /* advance the cursor */
	    r = cursor->c_get(cursor, &k, &d, DB_NEXT);
	}

	while (r == DB_LOCK_DEADLOCK) {
	    if (tid) {
		break;		/* don't autoretry txn-protected */
	    }

	    /* if we deadlock, close and reopen the cursor, and
	       reposition it */
	    CLOSECURSOR();
	    OPENCURSOR();

	    r = cursor->c_get(cursor, &k, &d, DB_SET);
	    switch (r) {
	    case 0:
		r = cursor->c_get(cursor, &k, &d, DB_NEXT);
		break;
	    case DB_LOCK_DEADLOCK:
		continue;
	    case DB_NOTFOUND: /* deleted? */
		r = cursor->c_get(cursor, &k, &d, DB_SET_RANGE);
		break;
	    }
	}
    }

 done:
    if (cursor) {
	CLOSECURSOR();
    }

    switch (r) {
    case 0:			/* ok */
	break;
    case DB_NOTFOUND:		/* also ok */
	r = 0;
	break;
    case DB_LOCK_DEADLOCK:	/* erg, we're in a txn! */
	if (mytid) {
	    abort_txn(mydb, *mytid);
	    *mytid = NULL;
	}
	r = CYRUSDB_AGAIN;
	break;
    default:
	if (mytid) {
	    abort_txn(mydb, *mytid); 
	    *mytid = NULL;
	}
	syslog(LOG_ERR, "DBERROR: error advancing: %s",  db_strerror(r));
	r = CYRUSDB_IOERROR;
	break;
    }

/*     if (k.data) free(k.data);
       if (d.data) free(d.data);*/

    return r;
}

static int mystore(struct db *mydb, 
		   const char *key, int keylen,
		   const char *data, int datalen,
		   struct txn **mytid, int putflags, int txnflags)
{
    int r = 0;
    DBT k, d;
    DB_TXN *tid;
    DB *db = (DB *) mydb;

    assert(dbinit && db);
    assert(key && keylen);

    r = gettid(mytid, &tid, "mystore");
    if (r) return r;

    memset(&k, 0, sizeof(k));
    memset(&d, 0, sizeof(d));

    k.data = (char *) key;
    k.size = keylen;
    d.data = (char *) data;
    d.size = datalen;

    if (!mytid) {
	/* start a transaction for the write */
    restart:
	r = txn_begin(dbenv, NULL, &tid, 0);
	if (r != 0) {
	    syslog(LOG_ERR, "DBERROR: mystore: error beginning txn: %s", 
		   db_strerror(r));
	    return CYRUSDB_IOERROR;
	}
	if (CONFIG_DB_VERBOSE)
	    syslog(LOG_DEBUG, "mystore: starting txn %lu",
		   (unsigned long) txn_id(tid));
    }
    r = db->put(db, tid, &k, &d, putflags);
    if (!mytid) {
	/* finish once-off txn */
	if (r) {
	    int r2;

	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "mystore: aborting txn %lu",
		       (unsigned long) txn_id(tid));
	    r2 = txn_abort(tid);
	    if (r2) {
		syslog(LOG_ERR, "DBERROR: mystore: error aborting txn: %s", 
		       db_strerror(r));
		return CYRUSDB_IOERROR;
	    }

	    if (r == DB_LOCK_DEADLOCK) {
		goto restart;
	    }
	} else {
	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "mystore: committing txn %lu",
		       (unsigned long) txn_id(tid));
	    r = txn_commit(tid, txnflags);
	}
    }

    if ( r != 0) {
	if (mytid) {
	    abort_txn(mydb, *mytid);
	    *mytid = NULL;
	}
	if (r == DB_LOCK_DEADLOCK) {
	    r = CYRUSDB_AGAIN;
	} else {
	    syslog(LOG_ERR, "DBERROR: mystore: error storing %s: %s",
		   key, db_strerror(r));
	    r = CYRUSDB_IOERROR;
	}
    }

    return r;
}

static int create(struct db *db, 
		  const char *key, int keylen,
		  const char *data, int datalen,
		  struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, DB_NOOVERWRITE, 0);
}

static int store(struct db *db, 
		 const char *key, int keylen,
		 const char *data, int datalen,
		 struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, 0, 0);
}

static int create_nosync(struct db *db, 
			 const char *key, int keylen,
			 const char *data, int datalen,
			 struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, DB_NOOVERWRITE,
		   DB_TXN_NOSYNC);
}

static int store_nosync(struct db *db, 
			const char *key, int keylen,
			const char *data, int datalen,
			struct txn **tid)
{
    return mystore(db, key, keylen, data, datalen, tid, 0, DB_TXN_NOSYNC);
}

static int mydelete(struct db *mydb, 
		    const char *key, int keylen,
		    struct txn **mytid, int txnflags, int force)
{
    int r = 0;
    DBT k;
    DB_TXN *tid;
    DB *db = (DB *) mydb;

    assert(dbinit && db);
    assert(key && keylen);

    r = gettid(mytid, &tid, "delete");
    if (r) return r;

    memset(&k, 0, sizeof(k));

    k.data = (char *) key;
    k.size = keylen;

    if (!mytid) {
    restart:
	/* start txn for the write */
	r = txn_begin(dbenv, NULL, &tid, 0);
	if (r != 0) {
	    syslog(LOG_ERR, "DBERROR: mydelete: error beginning txn: %s", 
		   db_strerror(r));
	    return CYRUSDB_IOERROR;
	}
	if (CONFIG_DB_VERBOSE)
	    syslog(LOG_DEBUG, "mydelete: starting txn %lu",
		   (unsigned long) txn_id(tid));
    }
    r = db->del(db, tid, &k, 0);
    if (force && r == DB_NOTFOUND) 
	r = CYRUSDB_OK;  /* ignore not found errors */
    if (!mytid) {
	/* finish txn for the write */
	if (r) {
	    int r2;
	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "mydelete: aborting txn %lu",
		       (unsigned long) txn_id(tid));
	    r2 = txn_abort(tid);
	    if (r2) {
		syslog(LOG_ERR, "DBERROR: mydelete: error aborting txn: %s", 
		       db_strerror(r));
		return CYRUSDB_IOERROR;
	    }

	    if (r == DB_LOCK_DEADLOCK) {
		goto restart;
	    }
	} else {
	    if (CONFIG_DB_VERBOSE)
		syslog(LOG_DEBUG, "mydelete: committing txn %lu",
		       (unsigned long) txn_id(tid));
	    r = txn_commit(tid, txnflags);
	}
    }

    if (r != 0) {
	if (mytid) {
	    abort_txn(mydb, *mytid);
	    *mytid = NULL;
	}
	if (r == DB_LOCK_DEADLOCK) {
	    r = CYRUSDB_AGAIN;
	} else {
	    syslog(LOG_ERR, "DBERROR: mydelete: error deleting %s: %s",
		   key, db_strerror(r));
	    r = CYRUSDB_IOERROR;
	}
    }

    return r;
}

static int delete(struct db *db, 
		  const char *key, int keylen,
		  struct txn **tid, int force)
{
    return mydelete(db, key, keylen, tid, 0, force);
}

static int delete_nosync(struct db *db, 
			 const char *key, int keylen,
			 struct txn **tid, int force)
{
    return mydelete(db, key, keylen, tid, DB_TXN_NOSYNC, force);
}

static int mycommit(struct db *db __attribute__((unused)),
		    struct txn *tid, int txnflags)
{
    int r;
    DB_TXN *t = (DB_TXN *) tid;

    assert(dbinit && tid);

    if (CONFIG_DB_VERBOSE)
	syslog(LOG_DEBUG, "mycommit: committing txn %lu",
	       (unsigned long) txn_id(t));
    r = txn_commit(t, txnflags);
    switch (r) {
    case 0:
	break;
    case EINVAL:
	syslog(LOG_WARNING, "mycommit: tried to commit an already aborted transaction");
	r = CYRUSDB_IOERROR;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: mycommit  failed on commit: %s",
	       db_strerror(r));
	r = CYRUSDB_IOERROR;
	break;
    }

    return r;
}

static int commit_txn(struct db *db, struct txn *tid)
{
    return mycommit(db, tid, 0);
}

static int commit_nosync(struct db *db, struct txn *tid)
{
    return mycommit(db, tid, DB_TXN_NOSYNC);
}

static int abort_txn(struct db *db __attribute__((unused)),
		     struct txn *tid)
{
    int r;
    DB_TXN *t = (DB_TXN *) tid;

    assert(dbinit && tid);

    if (CONFIG_DB_VERBOSE)
	syslog(LOG_DEBUG, "abort_txn: aborting txn %lu",
	       (unsigned long) txn_id(t));
    r = txn_abort(t);
    if (r != 0) {
	syslog(LOG_ERR, "DBERROR: abort_txn: error aborting txn: %s",
	       db_strerror(r));
	return CYRUSDB_IOERROR;
    }

    return 0;
}

struct cyrusdb_backend cyrusdb_berkeley = 
{
    "berkeley",			/* name */

    &init,
    &done,
    &mysync,
    &myarchive,

    &open_btree,
    &myclose,

    &fetch,
    &fetchlock,
    &foreach,
    &create,
    &store,
    &delete,

    &commit_txn,
    &abort_txn,
    
    NULL,
    NULL
};

struct cyrusdb_backend cyrusdb_berkeley_nosync = 
{
    "berkeley-nosync",		/* name */

    &init,
    &done,
    &mysync,
    &myarchive,

    &open_btree,
    &myclose,

    &fetch,
    &fetchlock,
    &foreach,
    &create_nosync,
    &store_nosync,
    &delete_nosync,

    &commit_nosync,
    &abort_txn,

    NULL,
    NULL
};

struct cyrusdb_backend cyrusdb_berkeley_hash = 
{
    "berkeley-hash",		/* name */

    &init,
    &done,
    &mysync,
    &myarchive,

    &open_hash,
    &myclose,

    &fetch,
    &fetchlock,
    &foreach,
    &create,
    &store,
    &delete,

    &commit_txn,
    &abort_txn,
    
    NULL,
    NULL
};

struct cyrusdb_backend cyrusdb_berkeley_hash_nosync = 
{
    "berkeley-hash-nosync",	/* name */

    &init,
    &done,
    &mysync,
    &myarchive,

    &open_hash,
    &myclose,

    &fetch,
    &fetchlock,
    &foreach,
    &create_nosync,
    &store_nosync,
    &delete_nosync,

    &commit_nosync,
    &abort_txn,

    NULL,
    NULL
};
