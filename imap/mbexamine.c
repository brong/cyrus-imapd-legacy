/* mbexamine.c -- examine the contents of a mailbox index and cache
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
 */

/* $Id: mbexamine.c,v 1.12.2.1 2007/11/01 14:39:33 murch Exp $ */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <fcntl.h>
#include <ctype.h>
#include <syslog.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <sys/stat.h>
#include <stdlib.h>

#if HAVE_DIRENT_H
# include <dirent.h>
# define NAMLEN(dirent) strlen((dirent)->d_name)
#else
# define dirent direct
# define NAMLEN(dirent) (dirent)->d_namlen
# if HAVE_SYS_NDIR_H
#  include <sys/ndir.h>
# endif
# if HAVE_SYS_DIR_H
#  include <sys/dir.h>
# endif
# if HAVE_NDIR_H
#  include <ndir.h>
# endif
#endif

#include "acl.h"
#include "assert.h"
#include "bsearch.h"
#include "convert_code.h"
#include "exitcodes.h"
#include "index.h"
#include "global.h"
#include "imap_err.h"
#include "imparse.h"
#include "mailbox.h"
#include "message.h"
#include "message_guid.h"
#include "mboxname.h"
#include "mboxlist.h"
#include "seen.h"
#include "retry.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

extern int optind;
extern char *optarg;

/* current namespace */
static struct namespace recon_namespace;

/* config.c stuff */
const int config_need_data = 0;

/* forward declarations */
int do_examine(char *name, int matchlen, int maycreate, void *rock);
void usage(void);
void shut_down(int code);

int code = 0;

unsigned wantuid = 0;
unsigned wantvalue = 0;

int main(int argc, char **argv)
{
    int opt, i, r;
    char buf[MAX_MAILBOX_PATH+1];
    char *alt_config = NULL;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    /* Ensure we're up-to-date on the index file format */
    assert(INDEX_HEADER_SIZE == (OFFSET_SPARE4+4));
    assert(INDEX_RECORD_SIZE == (OFFSET_MODSEQ+4));

    while ((opt = getopt(argc, argv, "C:u:s:")) != EOF) {
	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;

	case 'u':
	    if(wantvalue) usage();
	    wantuid = 1;
	    wantvalue = atoi(optarg);
	    break;
	    
	case 's':
	    if(wantvalue) usage();
	    wantvalue = atoi(optarg);
	    break;
	    
	default:
	    usage();
	}
    }

    cyrus_init(alt_config, "mbexamine", 0);

    /* Set namespace -- force standard (internal) */
    if ((r = mboxname_init_namespace(&recon_namespace, 1)) != 0) {
	syslog(LOG_ERR, error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

    mboxlist_init(0);
    mboxlist_open(NULL);

    signals_set_shutdown(&shut_down);
    signals_add_handlers(0);

    if (optind == argc) {
	strlcpy(buf, "*", sizeof(buf));
	(*recon_namespace.mboxlist_findall)(&recon_namespace, buf, 1, 0, 0,
					    do_examine, NULL);
    }

    for (i = optind; i < argc; i++) {
	/* Handle virtdomains and separators in mailboxname */
	(*recon_namespace.mboxname_tointernal)(&recon_namespace, argv[i],
					       NULL, buf);
	(*recon_namespace.mboxlist_findall)(&recon_namespace, buf, 1, 0,
					    0, do_examine, NULL);
    }

    mboxlist_close();
    mboxlist_done();

    exit(code);
}

void usage(void)
{
    fprintf(stderr,
	    "usage: mbexamine [-C <alt_config>] [-s seqnum] mailbox...\n"
	    "       mbexamine [-C <alt_config>] [-u uid] mailbox...\n");
    exit(EC_USAGE);
}    

/*
 * mboxlist_findall() callback function to examine a mailbox
 */
int do_examine(char *name,
	       int matchlen __attribute__((unused)),
	       int maycreate __attribute__((unused)),
	       void *rock __attribute__((unused)))
{
    unsigned i;
    int r = 0;
    int flag = 0;
    char ext_name_buf[MAX_MAILBOX_PATH+1];
    struct mailbox mailbox;
    const char *index_base;
    long int start_offset, record_size;
    
    signals_poll();

    /* Convert internal name to external */
    (*recon_namespace.mboxname_toexternal)(&recon_namespace, name,
					   "cyrus", ext_name_buf);
    printf("Examining %s...\n", ext_name_buf);

    /* Open/lock header */
    r = mailbox_open_header(name, 0, &mailbox);
    if (r) {
	return r;
    }
    if (mailbox.header_fd != -1) {
	(void) mailbox_lock_header(&mailbox);
    }
    mailbox.header_lock_count = 1;

    if (chdir(mailbox.path) == -1) {
	r = IMAP_IOERROR;
	goto done;
    }

    /* Attempt to open/lock index */
    r = mailbox_open_index(&mailbox);
    if (r) {
	goto done;
    } else {
	(void) mailbox_lock_index(&mailbox);
    }
    mailbox.index_lock_count = 1;

    printf(" Mailbox Header Info:\n");
    printf("  Path to mailbox: %s\n", mailbox.path);
    printf("  Mailbox ACL: %s\n", mailbox.acl); /* xxx parse */
    printf("  Unique ID: %s\n", mailbox.uniqueid);
    printf("  User Flags: ");

    for(i=0;i<MAX_USER_FLAGS;i++) {
	if(!mailbox.flagname[i]) break;
	printf("%s ", mailbox.flagname[i]);
    }

    if(i==0) printf("[none]");

    printf("\n");

    printf("\n Index Header Info:\n");
    printf("  Generation Number: %d\n", mailbox.generation_no);
    printf("  Format: ");
    switch(mailbox.format) {
	case MAILBOX_FORMAT_NORMAL:
	    printf("NORMAL");
	    break;
        case MAILBOX_FORMAT_NETNEWS:
	    printf("NET NEWS");
	    break;
        default:
	    printf("UNKNOWN");
    }
    printf("\n");
    printf("  Minor Version: %d\n", mailbox.minor_version);
    printf("  Header Size: %ld bytes  Record Size: %ld bytes\n",
	   mailbox.start_offset, mailbox.record_size);
    printf("  Number of Messages: %lu  Mailbox Size: " UQUOTA_T_FMT " bytes\n",
	   mailbox.exists, mailbox.quota_mailbox_used);
    printf("  Last Append Date: (%ld) %s", mailbox.last_appenddate,
	   ctime(&mailbox.last_appenddate));
    printf("  UIDValidity: %ld  Last UID: %ld\n", mailbox.uidvalidity,
	   mailbox.last_uid);
    printf("  Deleted: %ld  Answered: %ld  Flagged: %ld\n",
	   mailbox.deleted, mailbox.answered, mailbox.flagged);
    if (mailbox.minor_version >= 4) {
	printf("  Mailbox Options:");
	if (!mailbox.options) {
	    printf(" NONE");
	} else {
	    if (mailbox.options & OPT_POP3_NEW_UIDL) {
		printf(" POP3_NEW_UIDL");
	    }
	    if (mailbox.options & OPT_IMAP_CONDSTORE) {
		printf(" IMAP_CONDSTORE");
	    }
	    if (mailbox.options & OPT_IMAP_SHAREDSEEN) {
		printf(" IMAP_SHAREDSEEN");
	    }
	    if (mailbox.options & OPT_IMAP_DUPDELIVER) {
		printf(" IMAP_DUPDELIVER");
	    }
	}
	printf("\n");
    }
    printf("  Last POP3 Login: (%ld) %s", mailbox.pop3_last_login,
	   ctime((const long *) &mailbox.pop3_last_login));
    if (mailbox.minor_version >= 8) {
	printf("  Highest Mod Sequence: " MODSEQ_FMT "\n",
	       mailbox.highestmodseq);
    }

    printf("\n Message Info:\n");

    index_base = mailbox.index_base;
    start_offset = mailbox.start_offset;
    record_size = mailbox.record_size;
    
    for(i=1; i<=mailbox.exists; i++) {
	const char *cacheitem;
	int j;

	if(wantvalue) {
	    if(!wantuid) {
		if(i != wantvalue) continue;
	    } else {
		if(UID(i) != wantvalue) continue;
	    }
	    flag = 1;
	}

	printf("%06d> UID:%08d   INT_DATE:%d SENTDATE:%d SIZE:%-6d\n",
	       i, UID(i), INTERNALDATE(i), SENTDATE(i),
	       SIZE(i));
	printf("      > HDRSIZE:%-6d LASTUPD :%ld SYSFLAGS:%08X",
	       HEADER_SIZE(i), LAST_UPDATED(i), SYSTEM_FLAGS(i));
	if (mailbox.minor_version >= 5)
	    printf("   LINES:%-6d\n", CONTENT_LINES(i));

	if (mailbox.minor_version >= 6)
	    printf("      > CACHEVER:%-2d", CACHE_VERSION(i));

	if (mailbox.minor_version >= 7) {
	    printf(" GUID: %s", message_guid_encode(GUID(i)));
	}

	if (mailbox.minor_version >= 8) {
	    printf(" MODSEQ:" MODSEQ_FMT, MODSEQ(i));
	}

	printf("\n");

	printf("      > USERFLAGS:");
	for(j=(MAX_USER_FLAGS/32)-1; j>=0; j--) {
	    printf(" %08X", USER_FLAGS(i,j));
	}
	printf("\n");

	cacheitem = mailbox.cache_base + CACHE_OFFSET(i);
	
	printf(" Envel>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("BdyStr>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("  Body>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);

#if 0
	/* xxx print out machine-readable bodystructure? */
	printf(" Sects>\n");
#endif

	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("CacHdr>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("  From>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("    To>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("    Cc>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("   Bcc>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);
	cacheitem = CACHE_ITEM_NEXT(cacheitem);
	printf("Subjct>{%d}%s\n", CACHE_ITEM_LEN(cacheitem),
	       cacheitem + CACHE_ITEM_SIZE_SKIP);

	if(flag) break;
    }

    if(wantvalue && !flag) {
	printf("Desired message not found\n");
    }

 done:
    mailbox_close(&mailbox);

    return r;
}

/*
 * Cleanly shut down and exit
 */
void shut_down(int code) __attribute__((noreturn));
void shut_down(int code)
{
    mboxlist_close();
    mboxlist_done();
    exit(code);
}
