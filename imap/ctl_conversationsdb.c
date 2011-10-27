/*
 * Copyright (c) 1994-2011 Carnegie Mellon University.  All rights reserved.
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
#include "imap_err.h"
#include "index.h"
#include "conversations.h"
#include "mailbox.h"
#include "mboxlist.h"
#include "message.h"
#include "sync_log.h"
#include "sysexits.h"
#include "util.h"
#include "xmalloc.h"

#if !HAVE___ATTRIBUTE__
#define __attribute__(x)
#endif

/* config.c stuff */
const int config_need_data = CONFIG_NEED_PARTITION_DATA;
static struct namespace conv_namespace;

enum { UNKNOWN, DUMP, UNDUMP, ZERO, BUILD, RECALC };

int verbose = 0;

char *prev_userid;
int mode = UNKNOWN;

static int do_dump(const char *fname)
{
    struct conversations_state *state = NULL;
    struct stat sb;
    int r;

    /* What we really want here is read-only database access without
     * the create-if-nonexistant semantics.  However, the cyrusdb
     * interface makes it difficult to do that properly.  In the
     * meantime, we can just check if the file exists here. */
    r = stat(fname, &sb);
    if (r < 0) {
	perror(fname);
	return -1;
    }

    r = conversations_open_path(fname, &state);
    if (r) {
	/* TODO: wouldn't it be nice if we could translate this
	 * error code into somethine useful for humans? */
	fprintf(stderr, "Failed to open conversations database %s: %d\n",
		fname, r);
	return -1;
    }

    conversations_dump(state, stdout);

    conversations_abort(&state);
    return 0;
}

static int do_undump(const char *fname)
{
    struct conversations_state *state;
    int r;

    r = conversations_open_path(fname, &state);
    if (r) {
	/* TODO: wouldn't it be nice if we could translate this
	 * error code into somethine useful for humans? */
	fprintf(stderr, "Failed to open conversations database %s: %s\n",
		fname, error_message(r));
	return -1;
    }

    r = conversations_truncate(state);
    if (r) {
	fprintf(stderr, "Failed to truncate conversations database %s: %s\n",
		fname, error_message(r));
	goto out;
    }

    r = conversations_undump(state, stdin);
    if (r) {
	fprintf(stderr, "Failed to undump to conversations database %s: %s\n",
		fname, error_message(r));
	goto out;
    }

    r = conversations_commit(&state);
    if (r)
	fprintf(stderr, "Failed to commit conversations database %s: %s\n",
		fname, error_message(r));

out:
    conversations_abort(&state);
    return r;
}

static int zero_cid_cb(const char *mboxname,
		       int matchlen __attribute__((unused)),
		       int maycreate __attribute__((unused)),
		       void *rock __attribute__((unused)))
{
    struct mailbox *mailbox = NULL;
    struct index_record record;
    int r;
    uint32_t recno;

    r = mailbox_open_iwl(mboxname, &mailbox);
    if (r) return r;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) goto done;

	/* already zero, fine */
	if (record.cid == NULLCONVERSATION)
	    continue;
    
	record.cid = NULLCONVERSATION;
	r = mailbox_rewrite_index_record(mailbox, &record);
	if (r) goto done;
    }

 done:
    mailbox_close(&mailbox);
    return r;
}

static int do_zero(const char *inboxname)
{
    char buf[MAX_MAILBOX_NAME];
    int r;
    struct conversations_state *state = NULL;

    r = conversations_open_mbox(inboxname, &state);

    conversations_truncate(state);

    r = zero_cid_cb(inboxname, 0, 0, NULL);
    if (r) return r;

    snprintf(buf, sizeof(buf), "%s.*", inboxname);
    r = mboxlist_findall(NULL, buf, 1, NULL,
			 NULL, zero_cid_cb, NULL);

    conversations_commit(&state);

    return r;
}

static int build_cid_cb(const char *mboxname,
		        int matchlen __attribute__((unused)),
		        int maycreate __attribute__((unused)),
		        void *rock __attribute__((unused)))
{
    struct mailbox *mailbox = NULL;
    struct index_record record;
    uint32_t recno;
    int r;
    struct conversations_state *cstate = conversations_get_mbox(mboxname);

    if (!cstate) return IMAP_CONVERSATIONS_NOT_OPEN;

    r = mailbox_open_iwl(mboxname, &mailbox);
    if (r) return r;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) goto done;

	/* already assigned, fine */
	if (record.cid != NULLCONVERSATION)
	    continue;

	/* we don't care about expunged messages */
	if (record.system_flags & FLAG_EXPUNGED)
	    continue;

	r = mailbox_cacherecord(mailbox, &record);
	if (r) goto done;

	r = message_update_conversations(cstate, &record, NULL, /*isreplica*/0);
	if (r) goto done;

	r = mailbox_rewrite_index_record(mailbox, &record);
	if (r) goto done;
    }

 done:
    mailbox_close(&mailbox);
    return r;
}

static int do_build(const char *inboxname)
{
    char buf[MAX_MAILBOX_NAME];
    int r;
    struct conversations_state *state = NULL;

    r = conversations_open_mbox(inboxname, &state);

    r = build_cid_cb(inboxname, 0, 0, NULL);
    if (r) return r;

    snprintf(buf, sizeof(buf), "%s.*", inboxname);
    r = mboxlist_findall(NULL, buf, 1, NULL,
			 NULL, build_cid_cb, NULL);

    conversations_commit(&state);
    return r;
}

static int recalc_counts_cb(const char *mboxname,
			    int matchlen __attribute__((unused)),
			    int maycreate __attribute__((unused)),
			    void *rock __attribute__((unused)))
{
    struct mailbox *mailbox = NULL;
    struct index_record record;
    uint32_t recno;
    int r;

    r = mailbox_open_irl(mboxname, &mailbox);
    if (r) return r;

    if (verbose)
	printf("%s\n", mboxname);

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &record);
	if (r) goto done;

	/* not assigned, skip */
	if (!record.cid)
	    continue;

	r = mailbox_update_conversations(mailbox, NULL, &record);
	if (r) goto done;
    }

 done:
    mailbox_close(&mailbox);
    return r;
}

static int do_recalc(const char *inboxname)
{
    char buf[MAX_MAILBOX_NAME];
    int r;
    struct conversations_state *state = NULL;

    r = conversations_open_mbox(inboxname, &state);

    conversations_wipe_counts(state);

    r = recalc_counts_cb(inboxname, 0, 0, NULL);
    if (r) return r;

    snprintf(buf, sizeof(buf), "%s.*", inboxname);
    r = mboxlist_findall(NULL, buf, 1, NULL,
			 NULL, recalc_counts_cb, NULL);

    conversations_commit(&state);
    return r;
}

static int usage(const char *name)
    __attribute__((noreturn));

static int do_user(const char *userid)
{
    const char *inboxname;
    char *fname;
    int r;

    fname = conversations_getuserpath(userid);
    if (fname == NULL) {
	fprintf(stderr, "Unable to get conversations database "
			"filename for userid \"%s\"\n",
			userid);
	return EC_USAGE;
    }

    inboxname = mboxname_user_inbox(userid);
    if (inboxname == NULL) {
	fprintf(stderr, "Invalid userid %s", userid);
	return EC_USAGE;
    }

    switch (mode)
    {
    case DUMP:
	if (do_dump(fname))
	    r = EC_NOINPUT;
	break;

    case UNDUMP:
	if (do_undump(fname))
	    r = EC_NOINPUT;
	break;

    case ZERO:
	if (do_zero(inboxname))
	    r = EC_NOINPUT;
	break;

    case BUILD:
	if (do_build(inboxname))
	    r = EC_NOINPUT;
	break;

    case RECALC:
	if (do_recalc(inboxname))
	    r = EC_NOINPUT;
	break;

    case UNKNOWN:
	fatal("UNKNOWN MODE", EC_SOFTWARE);
    }

    free(fname);

    return r;
}

static int do_mailbox(char *name,
		      int namelen,
		      int maycreate __attribute__((unused)),
		      void *rock __attribute__((unused)))
{
    char *mboxname = xstrndup(name, namelen);
    const char *userid = mboxname_to_userid(mboxname);

    if (mboxname_isdeletedmailbox(mboxname, NULL))
	goto done;

    if (userid && strcmp(userid, prev_userid)) {
	printf("%s\n", userid);
	do_user(userid);
	free(prev_userid);
	prev_userid = xstrdup(userid);
    }

done:
    free(mboxname);

    return 0;
}

int main(int argc, char **argv)
{
    int c;
    const char *alt_config = NULL;
    const char *userid = NULL;
    int r = 0;
    int recursive = 0;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    while ((c = getopt(argc, argv, "durzbvRC:")) != EOF) {
	switch (c) {
	case 'd':
	    if (mode != UNKNOWN)
		usage(argv[0]);
	    mode = DUMP;
	    break;

	case 'r':
	    recursive = 1;
	    break;

	case 'u':
	    if (mode != UNKNOWN)
		usage(argv[0]);
	    mode = UNDUMP;
	    break;

	case 'z':
	    if (mode != UNKNOWN)
		usage(argv[0]);
	    mode = ZERO;
	    break;

	case 'b':
	    if (mode != UNKNOWN)
		usage(argv[0]);
	    mode = BUILD;
	    break;

	case 'R':
	    if (mode != UNKNOWN)
		usage(argv[0]);
	    mode = RECALC;
	    break;

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

    if (mode == UNKNOWN)
	usage(argv[0]);

    if (optind == argc-1)
	userid = argv[optind];
    else if (recursive)
	userid = "";
    else
	usage(argv[0]);

    cyrus_init(alt_config, "ctl_conversationsdb", 0);

    mboxlist_init(0);
    mboxlist_open(NULL);

    sync_log_init();

    if (recursive) {
	char *buf = xmalloc(strlen(userid) + 2);
	prev_userid = xstrdup("");
	strcpy(buf, userid);
	strcat(buf, "*");

	if ((r = mboxname_init_namespace(&conv_namespace, 1)) != 0) {
	    syslog(LOG_ERR, "%s", error_message(r));
	    fatal(error_message(r), EC_CONFIG);
	}

	(*conv_namespace.mboxlist_findall)(&conv_namespace, buf, 1, 0, 0,
					   do_mailbox, NULL);

	free(prev_userid);
	free(buf);
    }
    else
	do_user(userid);

    sync_log_done();

    mboxlist_close();
    mboxlist_done();

    cyrus_done();

    return r;
}

static int usage(const char *name)
{
    fprintf(stderr, "usage: %s [options] [-u|-d|-z|-f] [-r] username\n", name);
    fprintf(stderr, "\n");
    fprintf(stderr, "options are:\n");
    fprintf(stderr, "    -v             be more verbose\n");
    fprintf(stderr, "    -C altconfig   use altconfig instead of imapd.conf\n");
    fprintf(stderr, "    -u             undump the conversations database from stdin\n");
    fprintf(stderr, "    -d             dump the conversations database to stdout\n");
    fprintf(stderr, "    -z             zero the conversations DB (make all NULLs)\n");
    fprintf(stderr, "    -b             build conversations entries for any NULL records\n");
    fprintf(stderr, "    -R             recalculate all counts\n");
    fprintf(stderr, "\n");
    fprintf(stderr, "    -r             recursive mode: username is a prefix\n");

    exit(EC_USAGE);
}

void fatal(const char* s, int code)
{
    fprintf(stderr, "ctl_conversationsdb: %s\n", s);
    cyrus_done();
    exit(code);
}

