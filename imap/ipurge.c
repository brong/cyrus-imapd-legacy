/* ipurge.c - delete mail from cyrus imap mailbox or partition
 *            based on date (or size?)
 *
 * includes support for ISPN virtual host extensions
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
 * $Id: ipurge.c,v 1.26.2.3 2009/12/28 21:51:34 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <syslog.h>
#include <string.h>
#include <netinet/in.h>

/* cyrus includes */
#include "global.h"
#include "sysexits.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "mailbox.h"
#include "xmalloc.h"
#include "mboxlist.h"
#include "util.h"
#include "sync_log.h"

/* config.c stuff */
const int config_need_data = CONFIG_NEED_PARTITION_DATA;

/* globals for getopt routines */
extern char *optarg;
extern int  optind;
extern int  opterr;
extern int  optopt;

/* globals for callback functions */
int days = -1;
int size = -1;
int exact = -1;
int pattern = -1;
int skipflagged = 0;
int datemode = OFFSET_SENTDATE;
int invertmatch = 0;

/* for statistical purposes */
typedef struct mbox_stats_s {

    int total;         /* total including those deleted */
    int total_bytes;
    int deleted;       
    int deleted_bytes;

} mbox_stats_t;

/* current namespace */
static struct namespace purge_namespace;

int verbose = 1;
int forceall = 0;

int purge_me(char *, int, int);
unsigned purge_check(struct mailbox *, void *, unsigned char *, int);
int usage(char *name);
void print_stats(mbox_stats_t *stats);

int main (int argc, char *argv[]) {
  int option;		/* getopt() returns an int */
  char buf[MAX_MAILBOX_PATH+1];
  char *alt_config = NULL;
  int r;

  if ((geteuid()) == 0 && (become_cyrus() != 0)) {
      fatal("must run as the Cyrus user", EC_USAGE);
  }

  while ((option = getopt(argc, argv, "C:hxd:b:k:m:fsXi")) != EOF) {
    switch (option) {
    case 'C': /* alt config file */
      alt_config = optarg;
      break;
    case 'd': {
      if (optarg == 0) {
	usage(argv[0]);
      }
      days = atoi(optarg) * 86400 /* nominal # of seconds in a 'day' */;
    } break;
    case 'b': {
      if (optarg == 0) {
	usage(argv[0]);
      }
      size = atoi(optarg);
    } break;
    case 'k': {
      if (optarg == 0) {
	usage(argv[0]);
      }
      size = atoi(optarg) * 1024; /* make it bytes */
    } break;
    case 'm': {
      if (optarg == 0) {
	usage(argv[0]);
      }
      size = atoi(optarg) * 1048576; /* 1024 * 1024 */
    } break;
    case 'x' : {
      exact = 1;
    } break;
    case 'f' : {
      forceall = 1;
    } break;
    case 's' : {
      skipflagged = 1;
    } break;
    case 'X' : {
      datemode = OFFSET_INTERNALDATE;
    } break;
    case 'i' : {
      invertmatch = 1;
    } break;
    case 'h':
    default: usage(argv[0]);
    }
  }
  if ((days == -1 ) && (size == -1)) {
    printf("One of these must be specified -d, -b -k, -m\n");
    usage(argv[0]);
  }

  cyrus_init(alt_config, "ipurge", 0);

  /* Set namespace -- force standard (internal) */
  if ((r = mboxname_init_namespace(&purge_namespace, 1)) != 0) {
      syslog(LOG_ERR, error_message(r));
      fatal(error_message(r), EC_CONFIG);
  }

  mboxlist_init(0);
  mboxlist_open(NULL);

  /* open the quota db, we'll need it for expunge */
  quotadb_init(0);
  quotadb_open(NULL);

  sync_log_init();

  if (optind == argc) { /* do the whole partition */
    strcpy(buf, "*");
    (*purge_namespace.mboxlist_findall)(&purge_namespace, buf, 1, 0, 0,
					purge_me, NULL);
  } else {
    for (; optind < argc; optind++) {
      strncpy(buf, argv[optind], MAX_MAILBOX_BUFFER);
      /* Translate any separators in mailboxname */
      mboxname_hiersep_tointernal(&purge_namespace, buf,
				  config_virtdomains ?
				  strcspn(buf, "@") : 0);
      (*purge_namespace.mboxlist_findall)(&purge_namespace, buf, 1, 0, 0,
					  purge_me, NULL);
    }
  }

  sync_log_done();

  quotadb_close();
  quotadb_done();

  mboxlist_close();
  mboxlist_done();

  cyrus_done();
  
  return 0;
}

int
usage(char *name) {
  printf("usage: %s [-f] [-s] [-C <alt_config>] [-x] [-X] [-i] {-d days | -b bytes|-k Kbytes|-m Mbytes}\n\t[mboxpattern1 ... [mboxpatternN]]\n", name);
  printf("\tthere are no defaults and at least one of -d, -b, -k, -m\n\tmust be specified\n");
  printf("\tif no mboxpattern is given %s works on all mailboxes\n", name);
  printf("\t -x specifies an exact match for days or size\n");
  printf("\t -f force also to delete mail below user.* and INBOX.*\n");
  printf("\t -s skip over messages that are flagged.\n");
  printf("\t -X use delivery time instead of date header for date matches.\n");
  printf("\t -i invert match logic: -x means not equal, date is for newer, size is for smaller.\n");
  exit(0);
}

/* we don't check what comes in on matchlen and maycreate, should we? */
int purge_me(char *name, int matchlen __attribute__((unused)),
	     int maycreate __attribute__((unused))) {
  struct mailbox the_box;
  int            error;
  mbox_stats_t   stats;

  if( ! forceall ) {
      /* DON'T purge INBOX* and user.* */
      if (!strncasecmp(name,"INBOX",5) || mboxname_isusermailbox(name, 0))
	  return 0;
  }

  memset(&stats, '\0', sizeof(mbox_stats_t));

  if (verbose) {
      char mboxname[MAX_MAILBOX_BUFFER];

      /* Convert internal name to external */
      (*purge_namespace.mboxname_toexternal)(&purge_namespace, name,
					     "cyrus", mboxname);
      printf("Working on %s...\n", mboxname);
  }

  error = mailbox_open_header(name, 0, &the_box);
  if (error != 0) { /* did we find it? */
    syslog(LOG_ERR, "Couldn't find %s, check spelling", name);
    return error;
  }
  if (the_box.header_fd != -1) {
    (void) mailbox_lock_header(&the_box);
  }
  the_box.header_lock_count = 1;

  error = mailbox_open_index(&the_box);
  if (error != 0) {
    mailbox_close(&the_box);
    syslog(LOG_ERR, "Couldn't open mailbox index for %s", name);
    return error;
  }
  (void) mailbox_lock_index(&the_box);
  the_box.index_lock_count = 1;

  mailbox_expunge(&the_box, purge_check, &stats, 0, NULL);

  sync_log_mailbox(the_box.name);
  mailbox_close(&the_box);

  print_stats(&stats);

  return 0;
}

void deleteit(bit32 msgsize, mbox_stats_t *stats)
{
    stats->deleted++;
    stats->deleted_bytes += msgsize;
}

/* thumbs up routine, checks date & size and returns yes or no for deletion */
/* 0 = no, 1 = yes */
unsigned purge_check(struct mailbox *mailbox __attribute__((unused)),
		     void *deciderock,
		     unsigned char *buf,
		     int expunge_flags __attribute__((unused)))
{
  time_t my_time;
  mbox_stats_t *stats = (mbox_stats_t *) deciderock;
  bit32 senttime;
  bit32 msgsize;
  bit32 flagged;

  senttime = ntohl(*((bit32 *)(buf + datemode)));
  msgsize = ntohl(*((bit32 *)(buf + OFFSET_SIZE)));
  flagged = ntohl(*((bit32 *)(buf + OFFSET_SYSTEM_FLAGS))) & FLAG_FLAGGED;

  stats->total++;
  stats->total_bytes += msgsize;

  if (skipflagged && flagged)
    return 0;

  if (exact == 1) {
    if (days >= 0) {
      my_time = time(0);
      /*    printf("comparing %ld :: %ld\n", my_time, the_record->sentdate); */
      if (((my_time - (time_t) senttime)/86400) == (days/86400)) {
	  if (invertmatch) return 0;
	  deleteit(msgsize, stats);
	  return 1;
      } else {
	  if (!invertmatch) return 0;
	  deleteit(msgsize, stats);
	  return 1;
      }
    }
    if (size >= 0) {
      /* check size */
	if ((int) msgsize == size) {
	  if (invertmatch) return 0;
	  deleteit(msgsize, stats);
	  return 1;
      } else {
	  if (!invertmatch) return 0;
	  deleteit(msgsize, stats);
	  return 1;
      }
    }
    return 0;
  } else {
    if (days >= 0) {
      my_time = time(0);
      /*    printf("comparing %ld :: %ld\n", my_time, the_record->sentdate); */
      if (!invertmatch && ((my_time - (time_t) senttime) > days)) {
	  deleteit(msgsize, stats);
	  return 1;
      }
      if (invertmatch && ((my_time - (time_t) senttime) < days)) {
	  deleteit(msgsize, stats);
	  return 1;
      }
    }
    if (size >= 0) {
      /* check size */
	if (!invertmatch && ((int) msgsize > size)) {
	  deleteit(msgsize, stats);
	  return 1;
      }
	if (invertmatch && ((int) msgsize < size)) {
	  deleteit(msgsize, stats);
	  return 1;
      }
    }
    return 0;
  }
}

void print_stats(mbox_stats_t *stats)
{
    printf("total messages    \t\t %d\n",stats->total);
    printf("total bytes       \t\t %d\n",stats->total_bytes);
    printf("Deleted messages  \t\t %d\n",stats->deleted);
    printf("Deleted bytes     \t\t %d\n",stats->deleted_bytes);
    printf("Remaining messages\t\t %d\n",stats->total - stats->deleted);
    printf("Remaining bytes   \t\t %d\n",
	   stats->total_bytes - stats->deleted_bytes);
}
