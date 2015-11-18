/* cyrusdb_jmapsocket - simple DB that talks JMAP style methods over
 *                      a unix socket
 *
 * Copyright (c) 2015 FastMail Pty Ltd
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
 *    prior written permission. For permission or any other legal
 *    details, please contact
 *      Office of Technology Transfer
 *      Carnegie Mellon University
 *      5000 Forbes Avenue
 *      Pittsburgh, PA  15213-3890
 *      (412) 268-4387, fax: (412) 268-7395
 *      tech-transfer@andrew.cmu.edu
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

#include <syslog.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include "assert.h"
#include "bsearch.h"
#include "cyrusdb.h"
#include "exitcodes.h"
#include "libcyr_cfg.h"
#include "xmalloc.h"
#include "util.h"

extern void fatal(const char *, int);

struct dbengine {
    char *fname;
    int flags;
    int fd;
};

static int dbinit = 0;
static const sql_engine_t *dbengine = NULL;

static int init(const char *dbdir __attribute__((unused)),
                int flags __attribute__((unused)))
{
    int r = 0;

    if (dbinit++) return 0;

    dbinit = 1;

    return r;
}

static int done(void)
{
    --dbinit;
    return 0;
}

static int myopen(const char *fname, int flags, struct dbengine **ret, struct txn **mytid)
{
    const char *database, *hostnames, *user, *passwd;
    char *host_ptr, *host, *cur_host, *cur_port;
    int usessl;
    void *conn = NULL;
    char *p, *table, cmd[1024];

    if (mytid) return CYRUSDB_NOTIMPLEMENTED;

    assert(fname);
    assert(ret);

    *ret = (struct dbengine *) xzmalloc(sizeof(struct dbengine));
    (*ret)->fname = xstrdup(fname);
    (*ret)->flags = flags;
    (*ret)->fd = 0;

    return 0;
}

static int myfetch(struct dbengine *db,
                   const char *key, size_t keylen,
                   const char **data, size_t *datalen,
                   struct txn **mytid)
{
	if (mytid)
		return CYRUSDB_NOTIMPLEMENTED;

	
}

static int myclose(struct dbengine *db)
{
    assert(db);

    if (db->fd >= 0)
        fclose(db->fd);
    free(db->fname);

    free(db);

    return 0;
}

HIDDEN struct cyrusdb_backend cyrusdb_jmapsocket =
{
    "jmapsocket",                      /* name */

    &init,
    &done,
    &cyrusdb_generic_sync,
    &cyrusdb_generic_noarchive,
    NULL,

    &myopen,
    &myclose,

    &myfetch,
    &myfetch,
    NULL,

    NULL,
    NULL,
    NULL,
    NULL,

    NULL,
    NULL,

    NULL,
    NULL,
    NULL,
    NULL,
};
