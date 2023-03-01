/* cyrusdb_zeroskip.c - Support for Zeroskip
 *
 * Copyright (c) 1994-2018 Carnegie Mellon University.  All rights reserved.
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
#include "cyrusdb.h"
#include "util.h"
#include "xmalloc.h"

#include <libzeroskip/zeroskip.h>
#include <libzeroskip/memtree.h>

struct txn {
    struct zsdb_txn *t;
};


struct dbengine {
    struct zsdb *db;
    struct zsdb_txn *current_txn;
    unsigned uncommitted : 1;
};


struct dblist {
    struct dbengine *db;
    struct dblist *next;
    char *fname;
    int refcount;
};

static struct dblist *open_zeroskip;

/****** INTERNAL FUNCTIONS ******/
static int create_or_reuse_txn(struct dbengine *db,
                               struct txn **tidptr)
{
    if (!tidptr) return 0;

    int r;

    // existing transaction?  Keep it
    if (*tidptr) return CYRUSDB_OK;

    struct txn *tid = xzmalloc(sizeof(struct txn));

    /* Acquire write lock */
    r = zsdb_write_lock_acquire(db->db, 0);
    if (r != ZS_OK) {
         free(tid);
         return CYRUSDB_INTERNAL;
    }

    r = zsdb_transaction_begin(db->db, &tid->t);
    if (r != ZS_OK) {
        zsdb_write_lock_release(db->db);
        free(tid);
        return CYRUSDB_INTERNAL;
    }

    *tidptr = tid;
    db->current_txn = tid->t;

    return CYRUSDB_OK;
}

static int close_txn(struct dbengine *db, struct txn **tidptr)
{
    assert(tidptr);
    struct txn *tid = *tidptr;

    if (!tid) return 0;
    assert (tid->t == db->current_txn);

    if (db->uncommitted) {
        syslog(LOG_ERR, "ZSERROR: UNCOMMITTED CHANGES ON CLOSE");
        zsdb_abort(db->db, &tid->t);
        db->current_txn = tid->t;
    }

    if (tid->t) {
        zsdb_transaction_end(&tid->t);
        db->current_txn = tid->t;
    }
    free(tid);

    zsdb_write_lock_release(db->db);

    *tidptr = NULL;

    return 0;
}

memtree_memcmp_fn(
  mbox,
  ,
  bsearch_memtree_mbox(k, keylen, b, blen)
)
/****** CYRUS DB API ******/

HIDDEN int cyrusdb_zeroskip_init(const char *dbdir __attribute__((unused)),
                                 int myflags __attribute__((unused)))
{
    return CYRUSDB_OK;
}

HIDDEN int cyrusdb_zeroskip_done(void)
{
    return CYRUSDB_OK;
}

HIDDEN int cyrusdb_zeroskip_sync(void)
{
    return CYRUSDB_OK;
}

HIDDEN int cyrusdb_zeroskip_archive(const strarray_t *fnames __attribute__((unused)),
                                    const char *dirname __attribute__((unused)))
{
    return CYRUSDB_OK;
}


HIDDEN int cyrusdb_zeroskip_unlink(const char *fname __attribute__((unused)),
                                   int flags __attribute__((unused)))
{
    return CYRUSDB_OK;
}


static int cyrusdb_zeroskip_commit(struct dbengine *db, struct txn *tid)
{
    assert(db);
    if (!tid) return 0;
    int r = 0;

    if (db->uncommitted) {
        assert(db->current_txn == tid->t);
        r = zsdb_commit(db->db, &tid->t);
        if (r)
            zsdb_abort(db->db, &tid->t);
        db->current_txn = tid->t;
        db->uncommitted = 0;
    }

    int r2 = close_txn(db, &tid);

    return r ? r : r2;
}

static int cyrusdb_zeroskip_abort(struct dbengine *db, struct txn *tid)
{
    assert(db);
    if (!tid) return 0;
    int r = 0;

    if (db->uncommitted) {
        r = zsdb_abort(db->db, &tid->t);
        db->current_txn = tid->t;
        db->uncommitted = 0;
    }
    int r2 = close_txn(db, &tid);

    return r ? r : r2;
}

static int cyrusdb_zeroskip_open(const char *fname,
                                 int flags,
                                 struct dbengine **ret,
                                 struct txn **mytid)
{
    struct dbengine *dbe;
    int r = CYRUSDB_OK;
    int zsdbflags = MODE_RDWR;
    zsdb_cmp_fn dbcmpfn = NULL;
    memtree_search_cb_t btcmpfn = NULL;
    struct dblist *ent = NULL;

    dbe = (struct dbengine *) xzmalloc(sizeof(struct dbengine));

    /* do we already have this DB open? */
    for (ent = open_zeroskip; ent; ent = ent->next) {
        if (strcmp(ent->fname, fname)) continue;
        // XXX - we need to look and see if the the DB is already in a transaction
        r = create_or_reuse_txn(ent->db, mytid);
        if (r != ZS_OK)
            return CYRUSDB_INTERNAL;
        ent->refcount++;
        *ret = ent->db;
        return 0;
    }

    if (flags & CYRUSDB_CREATE)
        zsdbflags = MODE_CREATE;

    if (flags & CYRUSDB_MBOXSORT) {
        zsdbflags |= MODE_CUSTOMSEARCH;
        dbcmpfn = bsearch_uncompare_mbox;
        btcmpfn = memtree_memcmp_mbox;
    }

    if (zsdb_init(&dbe->db, dbcmpfn, btcmpfn) != ZS_OK) {
        r = CYRUSDB_IOERROR;
        goto done;
    }

    r = zsdb_open(dbe->db, fname, zsdbflags);
    if (r) {
        if (r == ZS_NOTFOUND) r = CYRUSDB_NOTFOUND;
        else r = CYRUSDB_IOERROR;
        goto finalise_db;
    }

    r = create_or_reuse_txn(dbe, mytid);
    if (r != ZS_OK) {
        r = CYRUSDB_INTERNAL;
        goto close_db;
    }

    *ret = dbe;

    /* track this database in the open list */
    ent = (struct dblist *) xzmalloc(sizeof(struct dblist));
    ent->db = dbe;
    ent->refcount = 1;
    ent->next = open_zeroskip;
    ent->fname = xstrdup(fname);
    open_zeroskip = ent;

    r = CYRUSDB_OK;
    goto done;

 close_db:
    zsdb_close(dbe->db);
 finalise_db:
    zsdb_final(&dbe->db);
    free(dbe);

 done:
    return r;
}

static int cyrusdb_zeroskip_close(struct dbengine *dbe)
{
    int r = CYRUSDB_OK;

    assert(dbe);
    assert(dbe->db);
    assert(!dbe->uncommitted);

    /* remove this DB from the open list */
    struct dblist *ent = open_zeroskip;
    struct dblist *prev = NULL;
    while (ent && ent->db != dbe) {
        prev = ent;
        ent = ent->next;
    }
    assert(ent);

    if (--ent->refcount > 0) 
        return 0;

    if (prev) prev->next = ent->next;
    else open_zeroskip = ent->next;

    r = zsdb_close(dbe->db);
    if (r) {
        r = CYRUSDB_INTERNAL;
        goto done;
    }

    zsdb_final(&dbe->db);

    free(dbe);

    free(ent->fname);
    free(ent);

 done:
    return r;
}

static int cyrusdb_zeroskip_fetch(struct dbengine *db,
                                  const char *key, size_t keylen,
                                  const char **data, size_t *datalen,
                                  struct txn **tidptr)
{
    int r = CYRUSDB_OK;

    assert(db);
    assert(key);
    assert(keylen);

    if (datalen) assert(data);

    if (data) *data = NULL;
    if (datalen) *datalen = 0;

    r = create_or_reuse_txn(db, tidptr);
    if (r) goto done;

    r = zsdb_fetch(db->db, (const unsigned char *)key, keylen,
                   (const unsigned char **)data, datalen);

    if (r == ZS_NOTFOUND) {
        r = CYRUSDB_NOTFOUND;
        if (data) *data = NULL;
        if (datalen) *datalen = 0;
        goto done;
    }

    if (r) {
        r = CYRUSDB_IOERROR;
        goto done;
    }

 done:
    return r;
}

static int cyrusdb_zeroskip_fetchlock(struct dbengine *db,
                                      const char *key, size_t keylen,
                                      const char **data, size_t *datalen,
                                      struct txn **tidptr)
{
    /* TODO: LOCK??? */
    return cyrusdb_zeroskip_fetch(db, key, keylen,
                                  data, datalen,
                                  tidptr);
}

static int cyrusdb_zeroskip_fetchnext(struct dbengine *db,
                                      const char *key, size_t keylen,
                                      const char **foundkey, size_t *fklen,
                                      const char **data, size_t *datalen,
                                      struct txn **tidptr)
{
    int r = CYRUSDB_OK;

    assert(db);

    if (data) *data = NULL;
    if (datalen) *datalen = 0;

    r = create_or_reuse_txn(db, tidptr);
    if (r) goto done;

    r = zsdb_fetchnext(db->db, (const unsigned char *)key, keylen,
                       (const unsigned char **)foundkey, fklen,
                       (const unsigned char **)data, datalen);

    if (r == ZS_NOTFOUND) {
        r = CYRUSDB_NOTFOUND;
        if (data) *data = NULL;
        if (datalen) *datalen = 0;
        goto done;
    }

    if (r) {
        r = CYRUSDB_IOERROR;
        goto done;
    }

 done:
    return r;
}

static int cyrusdb_zeroskip_foreach(struct dbengine *db,
                                    const char *prefix, size_t prefixlen,
                                    foreach_p *goodp,
                                    foreach_cb *cb, void *rock,
                                    struct txn **tidptr)
{
    int r = CYRUSDB_OK;

    assert(db);
    assert(cb);

    if (prefixlen) assert(prefix);

    r = create_or_reuse_txn(db, tidptr);
    if (r) goto done;

    /* FIXME: The *ugly* typecasts  be removed as soon as we * update the
     * CyrusDB interfaces to support `unsigned char *` instead of * `char *`.
     */
    r = zsdb_foreach(db->db, (unsigned char *)prefix, prefixlen,
                     (int (*)(void*, const unsigned char *, size_t , const unsigned char *, size_t))goodp,
                     (int (*)(void*, const unsigned char *, size_t , const unsigned char *, size_t))cb,
                     rock);

 done:
    return r;
}

static int cyrusdb_zeroskip_store(struct dbengine *db,
                                  const char *key, size_t keylen,
                                  const char *data, size_t datalen,
                                  struct txn **tidptr)
{
    struct txn *tid = NULL;
    int r = 0;

    if (datalen) assert(data);

    assert(db);
    assert(key && keylen);

    // always get a writelock
    r = create_or_reuse_txn(db, tidptr ? tidptr : &tid);
    if (r) goto done;

    db->uncommitted = 1;

    r = zsdb_add(db->db, (const unsigned char *)key, keylen,
                 (const unsigned char *)data, datalen);
    if (r == ZS_NOTFOUND) {
        r = CYRUSDB_NOTFOUND;
        goto done;
    }
    if (r) {
        r = CYRUSDB_INTERNAL;
        goto done;
    }

 done:
    if (tid) {
        if (r) close_txn(db, &tid);
        else r = cyrusdb_zeroskip_commit(db, tid);
    }

    return r;
}

static int cyrusdb_zeroskip_delete(struct dbengine *db,
                                   const char *key, size_t keylen,
                                   struct txn **tidptr,
                                   int force __attribute__((unused)))
{
    struct txn *tid = NULL;
    int r = 0;

    if (keylen) assert(key);

    assert(db);

    // always get a writelock
    r = create_or_reuse_txn(db, tidptr ? tidptr : &tid);
    if (r) goto done;

    db->uncommitted = 1;

    r = zsdb_remove(db->db, (const unsigned char *)key, keylen);
    if (r == ZS_NOTFOUND) {
        r = CYRUSDB_NOTFOUND;
        goto done;
    }
    if (r) {
        r = CYRUSDB_INTERNAL;
        goto done;
    }

 done:
    if (tid) {
        if (r) close_txn(db, &tid);
        else r = cyrusdb_zeroskip_commit(db, tid);
    }

    return r;
}

/* cyrusdb_zeroskip_dump:
   if detail == 1, dump all records.
   if detail == 2, dump active records only
*/
static int cyrusdb_zeroskip_dump(struct dbengine *db,
                                 int detail)
{
    int r = 0;

    assert(db);

    r = zsdb_dump(db->db, (detail == 1) ? DB_DUMP_ALL : DB_DUMP_ACTIVE);
    if (r)
        r = CYRUSDB_IOERROR;
    else
        r = CYRUSDB_OK;

    return r;
}

static int cyrusdb_zeroskip_consistent(struct dbengine *db __attribute__((unused)))
{
    return 0;
}

static int cyrusdb_zeroskip_checkpoint(struct dbengine *db)
{
    int r = 0;

    assert(db);

    if (zsdb_pack_lock_acquire(db->db, 0) != ZS_OK) {
        r = CYRUSDB_IOERROR;
        goto done;
    }

    r = zsdb_repack(db->db);
    if (r)
        r = CYRUSDB_IOERROR;
    else
        r = CYRUSDB_OK;

    if (zsdb_pack_lock_release(db->db) != ZS_OK) {
        r = CYRUSDB_IOERROR;
    }

done:
    return r;
}

static int cyrusdb_zeroskip_compar(struct dbengine *db __attribute__((unused)),
                                   const char *a __attribute__((unused)),
                                   int alen __attribute__((unused)),
                                   const char *b __attribute__((unused)),
                                   int blen __attribute__((unused)))
{
    /* return db->compar(a, alen, b, blen); */
    return 0;
}


HIDDEN struct cyrusdb_backend cyrusdb_zeroskip =
{
    "zeroskip",                  /* name */

    &cyrusdb_zeroskip_init,
    &cyrusdb_zeroskip_done,
    &cyrusdb_zeroskip_sync,
    &cyrusdb_zeroskip_archive,
    &cyrusdb_zeroskip_unlink,

    &cyrusdb_zeroskip_open,
    &cyrusdb_zeroskip_close,

    &cyrusdb_zeroskip_fetch,
    &cyrusdb_zeroskip_fetchlock,
    &cyrusdb_zeroskip_fetchnext,

    &cyrusdb_zeroskip_foreach,
    &cyrusdb_zeroskip_store,
    &cyrusdb_zeroskip_store,
    &cyrusdb_zeroskip_delete,

    &cyrusdb_zeroskip_commit,
    &cyrusdb_zeroskip_abort,

    &cyrusdb_zeroskip_dump,
    &cyrusdb_zeroskip_consistent,
    &cyrusdb_zeroskip_checkpoint,
    &cyrusdb_zeroskip_compar
};

