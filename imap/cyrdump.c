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
 * $Id: cyrdump.c,v 1.23 2010/01/06 17:01:31 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <syslog.h>
#include <string.h>

/* cyrus includes */
#include "assert.h"
#include "exitcodes.h"
#include "global.h"
#include "index.h"
#include "imap_err.h"
#include "imapurl.h"
#include "mailbox.h"
#include "mboxlist.h"
#include "sysexits.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"


/* config.c stuff */
const int config_need_data = CONFIG_NEED_PARTITION_DATA;

int verbose = 0;

static int dump_me(char *name, int matchlen, int maycreate, void *rock);
static void print_seq(const char *tag, const char *attrib, 
		      unsigned *seq, int n);
int usage(const char *name);

/* current namespace */
static struct namespace dump_namespace;

struct incremental_record {
    unsigned incruid;
};

int main(int argc, char *argv[])
{
    int option;
    char buf[MAX_MAILBOX_PATH+1];
    int i, r;
    char *alt_config = NULL;
    struct incremental_record irec;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    while ((option = getopt(argc, argv, "v")) != EOF) {
	switch (option) {
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

    if (optind == argc) {
	usage(argv[0]);
    }

    cyrus_init(alt_config, "dump", 0);
    mboxlist_init(0);
    mboxlist_open(NULL);

    /* Set namespace -- force standard (internal) */
    if ((r = mboxname_init_namespace(&dump_namespace, 1)) != 0) {
	syslog(LOG_ERR, "%s", error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

    irec.incruid = 0;
    for (i = optind; i < argc; i++) {
	strlcpy(buf, argv[i], sizeof(buf));
	/* Translate any separators in mailboxname */
	mboxname_hiersep_tointernal(&dump_namespace, buf,
				    config_virtdomains ?
				    strcspn(buf, "@") : 0);
	(*dump_namespace.mboxlist_findall)(&dump_namespace, buf, 1, 0, 0,
					   dump_me, &irec);
    }

    mboxlist_close();
    mboxlist_done();

    cyrus_done();
    
    return 0;
}

int usage(const char *name)
{
    fprintf(stderr, "usage: %s [-v] [mboxpattern ...]\n", name);

    exit(EC_USAGE);
}

static void generate_boundary(char *boundary, size_t size)
{
    assert(size >= 100);
    
    snprintf(boundary, size, "dump-%ld-%ld-%ld", 
	     (long) getpid(), (long) time(NULL), (long) rand());
}

static int dump_me(char *name, int matchlen __attribute__((unused)),
		   int maycreate __attribute__((unused)), void *rock)
{
    int r;
    char boundary[128];
    struct imapurl url;
    char imapurl[MAX_MAILBOX_PATH+1];
    struct incremental_record *irec = (struct incremental_record *) rock;
    struct searchargs searchargs;
    struct index_state *state;
    unsigned *uids;
    unsigned *uidseq;
    int i, n, numuids;

    r = index_open(name, NULL, &state);
    if (r) {
	if (verbose) {
	    printf("error opening %s: %s\n", name, error_message(r));
	}
	return 0;
    }

    generate_boundary(boundary, sizeof(boundary));

    printf("Content-Type: multipart/related; boundary=\"%s\"\n\n", boundary);

    printf("--%s\n", boundary);
    printf("Content-Type: text/xml\n");
    printf("IMAP-Dump-Version: 0\n");
    printf("\n");

    printf("<imapdump uniqueid=\"%s\">\n", state->mailbox->uniqueid);
    memset(&url, 0, sizeof(struct imapurl));
    url.server = config_servername;
    url.mailbox = name;
    imapurl_toURL(imapurl, &url);
    printf("  <mailbox-url>%s</mailbox-url>\n", imapurl);
    printf("  <incremental-uid>%d</incremental-uid>\n", irec->incruid);
    printf("  <nextuid>%ld</nextuid>\n", state->mailbox->i.last_uid + 1);
    printf("\n");

    memset(&searchargs, 0, sizeof(struct searchargs));
    numuids = index_getuidsequence(state, &searchargs, &uids);
    print_seq("uidlist", NULL, uids, numuids);
    printf("\n");

    printf("  <flags>\n");

    searchargs.system_flags_set = FLAG_ANSWERED;
    n = index_getuidsequence(state, &searchargs, &uidseq);
    print_seq("flag", "name=\"\\Answered\" user=\"*\"", uidseq, n);
    if (uidseq) free(uidseq);

    searchargs.system_flags_set = FLAG_DELETED;
    n = index_getuidsequence(state, &searchargs, &uidseq);
    print_seq("flag", "name=\"\\Deleted\" user=\"*\"", uidseq, n);
    if (uidseq) free(uidseq);

    searchargs.system_flags_set = FLAG_DRAFT;
    n = index_getuidsequence(state, &searchargs, &uidseq);
    print_seq("flag", "name=\"\\Draft\" user=\"*\"", uidseq, n);
    if (uidseq) free(uidseq);

    searchargs.system_flags_set = FLAG_FLAGGED;
    n = index_getuidsequence(state, &searchargs, &uidseq);
    print_seq("flag", "name=\"\\Flagged\" user=\"*\"", uidseq, n);
    if (uidseq) free(uidseq);

    printf("  </flags>\n");

    printf("</imapdump>\n");

    for (i = 0; i < numuids; i++) {
	const char *base;
	unsigned long len;

	if (uids[i] < irec->incruid) {
	    /* already dumped this message */
	    /* xxx could do binary search to get to the first
	       undumped uid */
	    continue;
	}

	printf("\n--%s\n", boundary);
	printf("Content-Type: message/rfc822\n");
	printf("Content-ID: %d\n", uids[i]);
	printf("\n");
	r = mailbox_map_message(state->mailbox, uids[i], &base, &len);
	if (r) {
	    if (verbose) {
		printf("error mapping message %d: %s\n", uids[i], 
		       error_message(r));
	    }
	    break;
	}
	fwrite(base, 1, len, stdout);
	mailbox_unmap_message(state->mailbox, uids[i], &base, &len);
    }

    printf("\n--%s--\n", boundary);

    index_close(&state);

    return 0;
}

static void print_seq(const char *tag, const char *attrib,
		      unsigned *seq, int n)
{
    int i;

    printf("  <%s%s%s>", tag, attrib ? " " : "", attrib ? attrib : "");
    for (i = 0; i < n; i++) {
	printf("%u ", seq[i]);
    }
    printf("</%s>\n", tag);
}
