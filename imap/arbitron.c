/* arbitron.c -- program to report readership statistics
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
 * $Id: arbitron.c,v 1.48 2010/01/06 17:01:30 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <syslog.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <sys/stat.h>

#include "assert.h"
#include "global.h"
#include "exitcodes.h"
#include "hash.h"
#include "imap_err.h"
#include "mailbox.h"
#include "mpool.h"
#include "mboxlist.h"
#include "convert_code.h"
#include "seen.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

/* config.c stuff */
const int config_need_data = 0;

#define DB (config_seenstate_db)
#define SUBDB (config_subscription_db)

extern int optind;
extern char *optarg;

/* Maintain the mailbox list */
/* xxx it'd be nice to generate a subscriber list too */
struct user_list {
    const char *user;
    struct user_list *next;
};

struct arb_mailbox_data {
    int nreaders;
    struct user_list *readers;
    int nsubscribers;
    struct user_list *subscribers;
};

struct mpool *arb_pool;
hash_table mailbox_table, mboxname_table;

time_t report_start_time = -1, report_end_time, prune_time = 0;
int code = 0;
int dosubs = 1;
int dousers = 0;
int long_report = 0;

/* current namespace */
static struct namespace arb_namespace;

/* forward declarations */
static void usage(void);
static void run_users(void);
static void make_report(const char *key, void *data, void *rock);
static void process_seen(const char *path, const char *user);
static void process_subs(const char *path, const char *user);
static int do_mailbox(const char *name, int matchlen, int maycreate, void *rock);

int main(int argc,char **argv)
{
    int opt, r;
    int report_days = 30;
    int prune_months = 0;
    char pattern[MAX_MAILBOX_BUFFER];
    char *alt_config = NULL;
    time_t now = time(0);

    strcpy(pattern, "*");

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    report_end_time = now;

    while ((opt = getopt(argc, argv, "C:oud:D:p:l")) != EOF) {
	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;

	case 'd':
	    if (report_start_time != -1) usage();
	    report_days = atoi(optarg);
	    if (report_days <= 0) usage();
	    break;

	case 'D': {
	    unsigned  month, day, year;
	    struct tm date;

	    if (strlen(optarg) < 8 ||
		sscanf(optarg, "%02u%02u%04u", &month, &day, &year) < 3) {
		usage();
	    }
	    memset(&date, 0, sizeof(struct tm));
	    date.tm_mon = month - 1;
	    date.tm_mday = day;
	    date.tm_year = year - 1900;
	    report_start_time = mktime(&date);

	    if (optarg[8] == ':' && strlen(optarg+9) == 8) {
		if (sscanf(optarg+9, "%02u%02u%04u", &month, &day, &year) < 3) {
		    usage();
		}
		memset(&date, 0, sizeof(struct tm));
		date.tm_mon = month - 1;
		date.tm_mday = day;
		date.tm_year = year - 1900;
		report_end_time = mktime(&date);
	    }

	    break;
	}

	case 'o':
	    dosubs = 0;
	    break;

	case 'u':
	    dousers = 1;
	    break;

	case 'p':
	    prune_months = atoi(optarg);
	    if (prune_months <= 0) usage();
	    break;

	case 'l':
	    long_report = dousers = 1;
	    break;

	default:
	    usage();
	}
    }

    /* Init Cyrus Backend Foo */
    cyrus_init(alt_config, "arbitron", 0);

    mboxlist_init(0);
    mboxlist_open(NULL);
    
    /* Set namespace -- force standard (internal) */
    if ((r = mboxname_init_namespace(&arb_namespace, 1)) != 0) {
	syslog(LOG_ERR, "%s", error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

    if (optind != argc) strlcpy(pattern, argv[optind], sizeof(pattern));

    if (report_start_time == -1) {
	report_start_time = now - (report_days*60*60*24);
    }
    if (prune_months) {
	prune_time = now - (prune_months*60*60*24*31);
    }

    /* Allocate our shared memory pools */
    arb_pool = new_mpool(0);
    construct_hash_table(&mailbox_table, 2047, 1);
    construct_hash_table(&mboxname_table, 2047, 1);

    /* Translate any separators in mailboxname */
    mboxname_hiersep_tointernal(&arb_namespace, pattern, 0);
    
    /* Get the mailbox list */
    fprintf(stderr, "Loading Mailboxes...");
    (*arb_namespace.mboxlist_findall)(&arb_namespace, pattern, 1, 0, 0,
				      do_mailbox, NULL);

    fprintf(stderr, "Done\nLoading Users");
    
    /* Now do all the users */
    run_users();

    fprintf(stderr, "Done\n");    

    /* And print the report */
    hash_enumerate(&mboxname_table, make_report, NULL);    

    /* Free Resources */
    free_hash_table(&mailbox_table, NULL);    
    free_hash_table(&mboxname_table, NULL);
    free_mpool(arb_pool);    
    mboxlist_close();
    mboxlist_done();    

    cyrus_done();

    return code;
}

static void usage(void)
{
    fprintf(stderr,
	    "usage: arbitron [-o] [-u] [-l] [-C alt_config] "
	    "[-d days | -D mmddyyy[:mmddyyyy]]\n"
            "                [-p months] [mboxpattern]\n");
    exit(EC_USAGE);
}    

static int do_mailbox(const char *name, int matchlen __attribute__((unused)),
		      int maycreate __attribute__((unused)),
		      void *rock __attribute__((unused)))
{
    int r;
    struct mailbox *mailbox = NULL;

    r = mailbox_open_irl(name, &mailbox);
    if (r) return 0;

    struct arb_mailbox_data *d = mpool_malloc(arb_pool,
					      sizeof(struct arb_mailbox_data));
    
    d->nreaders = 0;
    d->nsubscribers = 0;
    d->readers = NULL;
    d->subscribers = NULL;

    hash_insert(mailbox->uniqueid, d, &mailbox_table);
    hash_insert(name, d, &mboxname_table);

    mailbox_close(&mailbox);

    return 0;
}

static void run_users(void)
{
    char prefix[MAX_MAILBOX_PATH+1],path[MAX_MAILBOX_PATH+1],
	file[MAX_MAILBOX_PATH+1];    
    DIR *dirp, *dirq;
    struct dirent *dirent1, *dirent2;
    
    snprintf(prefix, sizeof(prefix), "%s%s", config_dir, FNAME_USERDIR);
    
    dirp = opendir(prefix);
    if(!dirp) {
	fatal("can't open user directory", EC_SOFTWARE);
    }

    while((dirent1 = readdir(dirp)) != NULL) {
	if(!strcmp(dirent1->d_name, ".") || !strcmp(dirent1->d_name,"..")) {
	    continue;	    
	}
	
	snprintf(path, sizeof(path), "%s%s", prefix, dirent1->d_name);
/*	printf("trying %s\n",path); */
	
	dirq = opendir(path);
	if(dirq) {	    
	    fprintf(stderr, ".");	    
	    while(dirq && ((dirent2 = readdir(dirq)) != NULL)) {
		size_t len;
		
		if(!strcmp(dirent2->d_name, ".") ||
		   !strcmp(dirent2->d_name,"..")) {
		    continue;	    
		}

		len = strlen(dirent2->d_name);

	        /* 5 is magic number for strlen(".seen") and
		   4 is the magic number for strlen(".sub") */
		if(len > 4) {
		    char *user = NULL;

		    snprintf(file, sizeof(file),
			     "%s/%s", path, dirent2->d_name);
/*		    printf("got file %s\n",file); */
		    if(len > 5 &&
		       !strcmp(dirent2->d_name + len - 5, ".seen")) {
			if (dousers) {
			    user = mpool_strndup(arb_pool, dirent2->d_name,
						 len-5);
			}
			process_seen(file, user);
		    } else if (dosubs &&
			       !strcmp(dirent2->d_name + len - 4, ".sub")) {
			if (dousers) {
			    user = mpool_strndup(arb_pool, dirent2->d_name,
						 len-4);
			}
			process_subs(file, user);
		    }
		}
	    }
	    closedir(dirq);
	}
	    
    }    
    closedir(dirp);

}

static int process_user_cb(void *rockp,
			   const char *key, size_t keylen,
			   const char *tmpdata __attribute__((unused)),
			   size_t tmpdatalen __attribute__((unused))) 
{
    /* Only called to do deletes */
/*    printf("pruning entry\n"); */
    
    DB->delete((struct db *)rockp, key, keylen, NULL, 0);    

    return 0;    
}

/* We can cheat and do all we need to in this function */
static int process_user_p(void *rockp,
			  const char *key,
			  size_t keylen,
			  const char *data,
			  size_t datalen __attribute__((unused))) 
{
    int ret = 0;    
    long version, lastread;
    char *p;    
    char buf[64];
    struct arb_mailbox_data *mbox;
    const char *user = (const char *) rockp;

    /* remember that 'data' may not be null terminated ! */
    version = strtol(data, &p, 10); data = p;
    if (version < 0) abort();
    /* xxx not checking version */
    lastread = strtol(data, &p, 10); data = p;
    
    memcpy(buf, key, keylen);
    buf[keylen] = '\0';

    mbox = hash_lookup(buf, &mailbox_table);

    if(mbox && lastread >= report_start_time &&
       lastread <= report_end_time) {
/*	printf("got %s\n", mbox->name);	     */
	mbox->nreaders++;
	if (user) {
	    struct user_list *u = mpool_malloc(arb_pool,
					       sizeof(struct user_list));

	    u->user = user;
	    u->next = mbox->readers;
	    mbox->readers = u;
	}
    }

    /* Check for pruning even if mailbox isn't valid */
    if(lastread < prune_time) {
	ret = 1;
    }	

    /* Only return true if we need to prune this guy */
    return ret;    
}

static void process_seen(const char *path, const char *user)
{
    int r;    
    struct db *tmp = NULL;

    r = (DB->open)(path, 0, &tmp);
    if(r) goto done;
    
    DB->foreach(tmp, "", 0, process_user_p, process_user_cb,
		(void *) user, NULL);

 done:
    if(tmp) (DB->close)(tmp);
}

static int process_subs_cb(void *rockp __attribute__((unused)),
			   const char *key __attribute__((unused)),
			   size_t keylen __attribute__((unused)),
			   const char *tmpdata __attribute__((unused)),
			   size_t tmpdatalen __attribute__((unused))) 
{
    return 0;
}

static int process_subs_p(void *rockp,
			  const char *key, size_t keylen,
			  const char *tmpdata __attribute__((unused)),
			  size_t tmpdatalen __attribute__((unused))) 
{
    struct arb_mailbox_data *mbox;
    char buf[MAX_MAILBOX_BUFFER];
    const char *user = (const char *) rockp;

    memcpy(buf, key, keylen);
    buf[keylen] = '\0';

/*    printf("lookup %s\n", buf); */

    mbox = hash_lookup(buf, &mboxname_table);

    if(mbox) {
/*	printf("got sub %s\n", buf); */
	mbox->nsubscribers++;
	if (user) {
	    struct user_list *u = mpool_malloc(arb_pool,
					       sizeof(struct user_list));

	    u->user = user;
	    u->next = mbox->subscribers;
	    mbox->subscribers = u;
	}
    }

    return 0; /* never do callback */
}

static void process_subs(const char *path, const char *user)
{
    int r;    
    struct db *tmp = NULL;

    r = (SUBDB->open)(path, 0, &tmp);
    if(r) goto done;
    
    SUBDB->foreach(tmp, "", 0, process_subs_p, process_subs_cb,
		   (void *) user, NULL);

 done:
    if(tmp) (SUBDB->close)(tmp);
}

void report_users(struct user_list *u)
{
    char sep = ':';

    while (u) {
	printf("%c%s", sep, u->user);
	sep = ',';
	u = u->next;
    }
}

void long_report_users(struct user_list *u, const char *mbox, char type)
{
    char buf[100];
    struct tm *tm;

    while (u) {
	printf("%s,%s,%c,", mbox, u->user, type);
	tm = localtime(&report_start_time);
	strftime(buf, sizeof(buf), "%m-%d-%Y %H:%M:%S", tm);
	printf("%s,", buf);

	tm = localtime(&report_end_time);
	strftime(buf, sizeof(buf), "%m-%d-%Y %H:%M:%S", tm);
	printf("%s\n", buf);
	u = u->next;
    }
}

static void make_report(const char *key, void *data, void *rock __attribute__((unused)))
{
    struct arb_mailbox_data *mbox = (struct arb_mailbox_data *)data;
    char *extkey;

    /* Skip underread user mailboxes */
    if(!strncasecmp(key, "user.", 5) && mbox->nreaders <= 1)
	return;    

    extkey = xstrdup(key);
    mboxname_hiersep_toexternal(&arb_namespace, extkey, 0);
    key = extkey;

    if (long_report) {
	long_report_users(mbox->readers, key, 'r');
	long_report_users(mbox->subscribers, key, 's');
    }
    else {
	printf("%s %d", key, mbox->nreaders);
	if (dousers) report_users(mbox->readers);
	if (dosubs) {
	    printf(" %d", mbox->nsubscribers);
	if (dousers) report_users(mbox->subscribers);
	}
	printf("\n");
    }
    free(extkey);
}
