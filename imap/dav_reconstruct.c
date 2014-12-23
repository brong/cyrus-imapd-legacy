/* dav_reconstruct.c - (re)build DAV DB for a user
 *
 * Copyright (c) 1994-2012 Carnegie Mellon University.  All rights reserved.
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
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <syslog.h>
#include <time.h>

#include <libical/ical.h>

#include "annotate.h"
#include "caldav_db.h"
#include "carddav_db.h"
#include "exitcodes.h"
#include "global.h"
#include "http_dav.h"
#include "imap_err.h"
#include "mailbox.h"
#include "message.h"
#include "message_guid.h"
#include "mboxname.h"
#include "mboxlist.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcat.h"

extern int optind;
extern char *optarg;

/* current namespace */
static struct namespace recon_namespace;

/* config.c stuff */
const int config_need_data = 0;

/* forward declarations */
void usage(void);
void shut_down(int code);

static int code = 0;

static int do_user(const char *userid, void *rock __attribute__((unused)))
{
    printf("Reconstructing DAV DB for %s...\n", userid);

    return dav_reconstruct_user(userid);
}

int main(int argc, char **argv)
{
    int opt, r;
    char *alt_config = NULL;
    int allusers = 0;

    if ((geteuid()) == 0 && (become_cyrus(/*is_master*/0) != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    while ((opt = getopt(argc, argv, "C:a")) != EOF) {
	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;

	case 'a':
	    allusers = 1;
	    break;

	default:
	    usage();
	}
    }

    cyrus_init(alt_config, "dav_reconstruct", 0, 0);

    /* Set namespace -- force standard (internal) */
    if ((r = mboxname_init_namespace(&recon_namespace, 1)) != 0) {
	syslog(LOG_ERR, "%s", error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

    mboxlist_init(0);
    mboxlist_open(NULL);

    signals_set_shutdown(&shut_down);
    signals_add_handlers(0);

    caldav_init();
    carddav_init();

    if (allusers) {
	mboxlist_alluser(do_user, NULL);
    }
    else if (optind == argc) {
	 usage();
    }
    else {
	int i;
	for (i = optind; i < argc; i++)
	    do_user(argv[i], NULL);
    }

    carddav_done();
    caldav_done();

    mboxlist_close();
    mboxlist_done();

    exit(code);
}


void usage(void)
{
    fprintf(stderr,
	    "usage: dav_reconstruct [-C <alt_config>] userid\n");
    exit(EC_USAGE);
}

/*
 * Cleanly shut down and exit
 */
void shut_down(int code) __attribute__((noreturn));
void shut_down(int code)
{
    in_shutdown = 1;

    mboxlist_close();
    mboxlist_done();
    caldav_done();
    exit(code);
}
