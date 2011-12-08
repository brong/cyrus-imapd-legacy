/* hammer_skiplist.c - tool to harass a skiplist file
 * 
 * Copyright (c) 1998-2003 Carnegie Mellon University.  All rights reserved.
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
 *
 */
/*
 * $Id: hammer_skiplist.c,v 1.4 2007/09/28 02:27:46 murch Exp $
 */

#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <fcntl.h>
#include <ctype.h>
#include <syslog.h>

#include <sys/ipc.h>
#include <sys/msg.h>

#include "acl.h"
#include "assert.h"
#include "auth.h"
#include "cyrusdb.h"
#include "exitcodes.h"
#include "glob.h"
#include "imap_err.h"
#include "global.h"
#include "mailbox.h"
#include "util.h"
#include "xmalloc.h"

const int config_need_data = 0;
struct cyrusdb_backend *DB_OLD = NULL;

void hammer(struct db *db)
{
    int c;
    for (c = 0;c < 10000; c++) { /* should be enough! */
        struct txn *tid = NULL;
        struct txn **tp;
        char key[100];
        char value[100];
        int klen, vlen, i, r = 0;
        int rop;

        /* protect against silly things */

        tp = (rand() % 2) ? &tid : NULL;
        klen = 1 + (rand() % 6);
        for (i = 0; i < klen; i++) {
          key[i] = 'A' + (rand() % 26);
        }
        key[klen] = '\0';
        vlen = rand() % 20;
        for (i = 0; i < vlen; i++) {
          value[i] = 'a' + (rand() % 26);
        }
        value[vlen] = '\0';
        rop = rand() % 1000;
        if (rop >= 999) {
          if (!r) r = DB_OLD->store(db, key, klen, value, vlen, tp);
          /* forget to commit */
        }
        else if (rop >= 800) {
          if (!r) r = DB_OLD->store(db, key, klen, value, vlen, tp);
          if (!r) r = DB_OLD->delete(db, key, klen, tp, 0);
          if (!r) r = DB_OLD->store(db, key, klen, value, vlen, tp);
          if (!r && tp) DB_OLD->commit(db, *tp);
        }
        else if (rop >= 700) {
          if (!r) r =  DB_OLD->delete(db, key, klen, tp, 0);
          if (!r && tp) DB_OLD->commit(db, *tp);
        }
        else if (rop >= 600) { /* will fail */
          if (!r) r = DB_OLD->store(db, key, klen, value, vlen, tp);
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
        }
        else if (rop > 200) {
          if (!r) r = DB_OLD->store(db, key, klen, value, vlen, tp);
          key[klen-1] = 'a';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'b';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'd';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'c';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          if (!r && tp) DB_OLD->commit(db, *tp);
        }
        else {
          if (!r) r =  DB_OLD->store(db, key, klen, value, vlen, tp);
          key[klen-1] = 'a';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'b';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'd';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          key[klen-1] = 'c';
          if (!r) r = DB_OLD->create(db, key, klen, value, vlen, tp);
          if (!r && tp) DB_OLD->abort(db, *tp);
        }

    }


}

int main(int argc, char *argv[])
{
    struct db *odb;
    const char *old_db;
    int opt, i, r;
    char *alt_config = NULL;
    int db_flags = 0;

    while ((opt = getopt(argc, argv, "C:n")) != EOF) {
	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;
	case 'n': /* create new */
	    db_flags |= CYRUSDB_CREATE;
	    break;
	}
    }
	
    if((argc - optind) < 1) {
	fprintf(stderr, "Usage: %s [-C altconfig] <dbfile>\n", argv[0]);

	exit(-1);
    }

    old_db = argv[optind];

    if(old_db[0] != '/') {
	printf("\nSorry, you cannot use this tool with relative path names.\n"
	       "This is because some database backends (mainly berkeley) do not\n"
	       "always do what you would expect with them.\n"
	       "\nPlease use absolute pathnames instead.\n\n");
	exit(EC_OSERR);
    }

    for(i=0; cyrusdb_backends[i]; i++) {
	if(!strcmp(cyrusdb_backends[i]->name, "twoskip")) {
	    DB_OLD = cyrusdb_backends[i]; break;
	}
    }
    if(!cyrusdb_backends[i]) {
	fatal("unknown backend", EC_TEMPFAIL);
    }   

    cyrus_init(alt_config, "hammer_skiplist", 0);


    r = (DB_OLD->open)(old_db, db_flags, &odb);
    if(r != CYRUSDB_OK)
	fatal("can't open database", EC_TEMPFAIL);

    hammer(odb);
    
    cyrus_done();

    return 0;
}

