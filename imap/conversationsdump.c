/*
 * Copyright (c) 1994-2010 Carnegie Mellon University.  All rights reserved.
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

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <syslog.h>
#include <string.h>
#include <sys/stat.h>

/* cyrus includes */
#include "assert.h"
#include "exitcodes.h"
#include "global.h"
#include "index.h"
#include "conversations.h"
#include "sysexits.h"
#include "util.h"
#include "xmalloc.h"

#if !HAVE___ATTRIBUTE__
#define __attribute__(x)
#endif

/* config.c stuff */
const int config_need_data = CONFIG_NEED_PARTITION_DATA;

int verbose = 0;

static int usage(const char *name)
    __attribute__((noreturn));

/* current namespace */
static struct namespace dump_namespace;

int main(int argc, char **argv)
{
    int c;
    const char *alt_config = NULL;
    const char *mboxname = NULL;
    char *fname;
    struct conversations_state state;
    struct stat sb;
    int r;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    while ((c = getopt(argc, argv, "vC:")) != EOF) {
	switch (c) {
	case 'v':
	    verbose++;
	    break;

	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;

	default:
	    usage(argv[0]);
	    break;
	}
    }

    if (optind == argc-1)
	mboxname = argv[optind];
    else
	usage(argv[0]);

    cyrus_init(alt_config, "conversationsdump", 0);

    fname = conversations_getpath(mboxname);
    if (fname == NULL) {
	fprintf(stderr, "Unable to get conversations database "
			"filename for mboxname \"%s\"\n",
			mboxname);
	exit(EC_NOINPUT);
    }

    /* What we really want here is read-only database access without
     * the create-if-nonexistant semantics.  However, the cyrusdb
     * interface makes it difficult to do that properly.  In the
     * meantime, we can just check if the file exists here. */
    r = stat(fname, &sb);
    if (r < 0) {
	perror(fname);
	exit(EC_NOINPUT);
    }

    r = conversations_open(&state, fname);
    if (r) {
	/* TODO: wouldn't it be nice if we could translate this
	 * error code into somethine useful for humans? */
	fprintf(stderr, "Failed to open conversations database %s: %d\n",
		fname, r);
	exit(EC_NOINPUT);
    }

    conversations_dump(&state, stdout);

    conversations_close(&state);

    cyrus_done();
    free(fname);
    fname = NULL;

    return 0;
}

static int usage(const char *name)
{
    fprintf(stderr, "usage: %s [-v] [-C altconfig] mboxname\n", name);

    exit(EC_USAGE);
}

void fatal(const char* s, int code)
{
    fprintf(stderr, "conversationsdump: %s\n", s);
    cyrus_done();
    exit(code);
}

