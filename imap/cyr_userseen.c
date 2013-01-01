/* ctl_userseen.c - tool to remove seen records for owners.
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
 * $Id: ctl_cyrusdb.c,v 1.33 2010/01/06 17:01:30 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <syslog.h>
#include <errno.h>

#include "cyrusdb.h"
#include "global.h"
#include "exitcodes.h"
#include "libcyr_cfg.h"
#include "mailbox.h"
#include "mboxlist.h"
#include "seen.h"
#include "util.h"
#include "xmalloc.h"

/* config.c stuff */
static int do_remove = 0;

static void usage(void)
{
    fprintf(stderr, "cyr_userseen [-C <altconfig>] -d\n");
    exit(-1);
}

/* Callback for use by delete_seen */
static int deluserseen(void *rock __attribute__((unused)),
		       const char *key,
		       size_t keylen,
		       const char *val __attribute__((unused)),
		       size_t vallen  __attribute__((unused)))
{
    char *name = xstrndup(key, keylen);
    struct mailbox *mailbox = NULL;
    const char *userid;
    int r = 0;

    r = mailbox_open_irl(name, &mailbox);
    if (r) goto done;

    userid = mboxname_to_userid(name);
    if (userid) {
	printf("removing seen for %s on %s\n", userid, mailbox->name);
	if (do_remove) seen_delete_mailbox(userid, mailbox);
    }

    mailbox_close(&mailbox);

done:
    free(name);
    return r;
}

int main(int argc, char *argv[])
{
    extern char *optarg;
    int opt;
    char *alt_config = NULL;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    while ((opt = getopt(argc, argv, "C:d")) != EOF) {
	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;

	case 'd':
	    do_remove = 1;
	    break;

	default:
	    usage();
	    break;
	}
    }

    cyrus_init(alt_config, "cyr_userseen", 0, 0);

    mboxlist_init(0);
    mboxlist_open(NULL);

    /* build a list of mailboxes - we're using internal names here */
    mboxlist_allmbox(NULL, deluserseen, NULL);

    mboxlist_close();
    mboxlist_done();

    return 0;
}
