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
#include "exitcodes.h"
#include "mailbox.h"
#include "xmalloc.h"
#include "mboxlist.h"
#include "util.h"
#include "sync_log.h"

/* generated headers are not necessarily in current directory */
#include "imap/imap_err.h"

/* globals for getopt routines */
extern char *optarg;
extern int  optind;
extern int  opterr;
extern int  optopt;

/* globals for callback functions */
static int days = -1;
static int size = -1;
static int exact = -1;
static int skipflagged = 0;
static int onlydeleted = 0;
static int use_sentdate = 1;
static int invertmatch = 0;

/* for statistical purposes */
typedef struct mbox_stats_s {

    int total;         /* total including those deleted */
    int total_bytes;
    int deleted;
    int deleted_bytes;

} mbox_stats_t;

static int verbose = 1;
static int forceall = 0;

static int purge_me(const char *, int, int, void *);
static unsigned purge_check(struct mailbox *mailbox,
                            const struct index_record *record,
                            void *rock);
static int usage(const char *name);
static void print_stats(mbox_stats_t *stats);

int main (int argc, char *argv[]) {
  int option;           /* getopt() returns an int */
  char *alt_config = NULL;

  if ((geteuid()) == 0 && (become_cyrus(/*is_master*/0) != 0)) {
      fatal("must run as the Cyrus user", EC_USAGE);
  }

  while ((option = getopt(argc, argv, "C:hxd:b:k:m:fsXio")) != EOF) {
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
      use_sentdate = 0;
    } break;
    case 'i' : {
      invertmatch = 1;
    } break;
    case 'o' : {
      onlydeleted = 1;
    } break;
    case 'h':
    default: usage(argv[0]);
    }
  }
  if ((days == -1 ) && (size == -1)) {
    printf("One of these must be specified -d, -b -k, -m\n");
    usage(argv[0]);
  }

  cyrus_init(alt_config, "ipurge", 0, CONFIG_NEED_PARTITION_DATA);

  /* setup for mailbox event notifications */
  mboxevent_init();

  mboxlist_init(0);
  mboxlist_open(NULL);

  /* open the quota db, we'll need it for expunge */
  quotadb_init(0);
  quotadb_open(NULL);

  sync_log_init();

  if (optind == argc) { /* do the whole partition */
    mboxlist_findall(NULL, "*", 1, 0, 0, purge_me, NULL);
  } else {
    /* do all matching mailboxes in one pass */
    strarray_t *array = strarray_new();
    for (; optind < argc; optind++) {
      strarray_append(array, argv[optind]);
    }
    if (array->count)
      mboxlist_findallmulti(NULL, array, 1, 0, 0, purge_me, NULL);
    strarray_free(array);
  }

  sync_log_done();

  quotadb_close();
  quotadb_done();

  mboxlist_close();
  mboxlist_done();

  cyrus_done();

  return 0;
}

static int usage(const char *name)
{
  printf("usage: %s [-f] [-s] [-C <alt_config>] [-x] [-X] [-i] [-o] {-d days | -b bytes|-k Kbytes|-m Mbytes}\n\t[mboxpattern1 ... [mboxpatternN]]\n", name);
  printf("\tthere are no defaults and at least one of -d, -b, -k, -m\n\tmust be specified\n");
  printf("\tif no mboxpattern is given %s works on all mailboxes\n", name);
  printf("\t -x specifies an exact match for days or size\n");
  printf("\t -f force also to delete mail below user.* and INBOX.*\n");
  printf("\t -s skip over messages that are flagged.\n");
  printf("\t -X use delivery time instead of date header for date matches.\n");
  printf("\t -i invert match logic: -x means not equal, date is for newer, size is for smaller.\n");
  printf("\t -o only purge messages that are deleted.\n");
  exit(0);
}

/* we don't check what comes in on matchlen and category, should we? */
static int purge_me(const char *name, int matchlen __attribute__((unused)),
                    int category __attribute__((unused)),
                    void *rock __attribute__((unused)))
{
  struct mailbox *mailbox = NULL;
  int r;
  mbox_stats_t stats;

  if (!forceall) {
      /* DON'T purge INBOX* and user.* */
      if (!strncasecmp(name,"INBOX",5) || mboxname_isusermailbox(name, 0))
          return 0;
  }

  memset(&stats, '\0', sizeof(mbox_stats_t));

  if (verbose) {
      printf("Working on %s...\n", name);
  }

  r = mailbox_open_iwl(name, &mailbox);
  if (r) { /* did we find it? */
    syslog(LOG_ERR, "Couldn't find %s, check spelling", name);
    return r;
  }

  mailbox_expunge(mailbox, purge_check, &stats, NULL, EVENT_MESSAGE_EXPUNGE);

  mailbox_close(&mailbox);

  print_stats(&stats);

  return 0;
}

static void deleteit(bit32 msgsize, mbox_stats_t *stats)
{
    stats->deleted++;
    stats->deleted_bytes += msgsize;
}

/* thumbs up routine, checks date & size and returns yes or no for deletion */
/* 0 = no, 1 = yes */
static unsigned purge_check(struct mailbox *mailbox __attribute__((unused)),
                     const struct index_record *record,
                     void *deciderock)
{
  time_t my_time;
  time_t senttime;
  mbox_stats_t *stats = (mbox_stats_t *) deciderock;

  my_time = time(0);
  senttime = use_sentdate ? record->sentdate : record->internaldate;

  stats->total++;
  stats->total_bytes += record->size;

  if (skipflagged && record->system_flags & FLAG_FLAGGED)
    return 0;

  if (onlydeleted && !(record->system_flags & FLAG_DELETED))
    return 0;

  if (exact == 1) {
    if (days >= 0) {
      /*    printf("comparing %ld :: %ld\n", my_time, the_record->sentdate); */
      if (((my_time - (time_t) senttime)/86400) == (days/86400)) {
          if (invertmatch) return 0;
          deleteit(record->size, stats);
          return 1;
      } else {
          if (!invertmatch) return 0;
          deleteit(record->size, stats);
          return 1;
      }
    }
    if (size >= 0) {
      /* check size */
        if (record->size == (unsigned)size) {
          if (invertmatch) return 0;
          deleteit(record->size, stats);
          return 1;
      } else {
          if (!invertmatch) return 0;
          deleteit(record->size, stats);
          return 1;
      }
    }
    return 0;
  } else {
    if (days >= 0) {
      /*    printf("comparing %ld :: %ld\n", my_time, the_record->sentdate); */
      if (!invertmatch && ((my_time - (time_t) senttime) > days)) {
          deleteit(record->size, stats);
          return 1;
      }
      if (invertmatch && ((my_time - (time_t) senttime) < days)) {
          deleteit(record->size, stats);
          return 1;
      }
    }
    if (size >= 0) {
      /* check size */
        if (!invertmatch && ((int) record->size > size)) {
          deleteit(record->size, stats);
          return 1;
      }
        if (invertmatch && ((int) record->size < size)) {
          deleteit(record->size, stats);
          return 1;
      }
    }
    return 0;
  }
}

static void print_stats(mbox_stats_t *stats)
{
    printf("total messages    \t\t %d\n",stats->total);
    printf("total bytes       \t\t %d\n",stats->total_bytes);
    printf("Deleted messages  \t\t %d\n",stats->deleted);
    printf("Deleted bytes     \t\t %d\n",stats->deleted_bytes);
    printf("Remaining messages\t\t %d\n",stats->total - stats->deleted);
    printf("Remaining bytes   \t\t %d\n",
           stats->total_bytes - stats->deleted_bytes);
}
