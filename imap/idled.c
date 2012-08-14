/* idled.c - daemon for handling IMAP IDLE notifications
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
 * $Id: idled.c,v 1.28 2010/01/06 17:01:32 murch Exp $
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <sys/types.h>
#include <syslog.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <errno.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <signal.h>
#include <fcntl.h>

#include "idlemsg.h"
#include "global.h"
#include "mboxlist.h"
#include "xmalloc.h"
#include "hash.h"
#include "exitcodes.h"

extern int optind;
extern char *optarg;

static int verbose = 0;
static int debugmode = 0;
static time_t idle_timeout;
static volatile sig_atomic_t sigquit = 0;

struct ientry {
    struct sockaddr_un remote;
    time_t itime;
    struct ientry *next;
};
static struct hash_table itable;

EXPORTED void fatal(const char *msg, int err)
{
    if (debugmode) fprintf(stderr, "dying with %s %d\n",msg,err);
    syslog(LOG_CRIT, "%s", msg);
    syslog(LOG_NOTICE, "exiting");

    cyrus_done();

    exit(err);
}

static int mbox_count_cb(void *rockp,
			 const char *key __attribute__((unused)),
			 size_t keylen __attribute__((unused)),
			 const char *data __attribute__((unused)),
			 size_t datalen __attribute__((unused)))
{
    int *ip = (int *) rockp;
    (*ip)++;

    return 0;
}

/* remove an ientry from list of those idling on mboxname */
static void remove_ientry(const char *mboxname,
			  const struct sockaddr_un *remote)
{
    struct ientry *t, *p = NULL;

    t = (struct ientry *) hash_lookup(mboxname, &itable);
    while (t && memcmp(&t->remote, remote, sizeof(*remote))) {
	p = t;
	t = t->next;
    }
    if (t) {
	if (!p) {
	    /* first ientry in the linked list */

	    p = t->next; /* remove node */

	    /* we just removed the data that the hash entry
	       was pointing to, so insert the new data */
	    hash_insert(mboxname, p, &itable);
	}
	else {
	    /* not the first ientry in the linked list */

	    p->next = t->next; /* remove node */
	}
	free(t);
    }
}



static void process_message(struct sockaddr_un *remote, idle_message_t *msg)
{
    struct ientry *t, *n;
    int r;

    switch (msg->which) {
    case IDLE_MSG_INIT:
	if (verbose || debugmode)
	    syslog(LOG_DEBUG, "imapd[%s]: IDLE_MSG_INIT '%s'\n",
		   idle_id_from_addr(remote), msg->mboxname);

	/* add an ientry to list of those idling on mboxname */
	t = (struct ientry *) hash_lookup(msg->mboxname, &itable);
	n = (struct ientry *) xzmalloc(sizeof(struct ientry));
	n->remote = *remote;
	n->itime = time(NULL);
	n->next = t;
	hash_insert(msg->mboxname, n, &itable);
	break;

    case IDLE_MSG_NOTIFY:
	if (verbose || debugmode)
	    syslog(LOG_DEBUG, "IDLE_MSG_NOTIFY '%s'\n", msg->mboxname);

	/* send a message to all clients idling on mboxname */
	t = (struct ientry *) hash_lookup(msg->mboxname, &itable);
	for ( ; t ; t = n) {
	    n = t->next;
	    if ((t->itime + idle_timeout) < time(NULL)) {
		/* This process has been idling for longer than the timeout
		 * period, so it probably died.  Remove it from the list.
		 */
		if (verbose || debugmode)
		    syslog(LOG_DEBUG, "    TIMEOUT %s\n", idle_id_from_addr(&t->remote));

		remove_ientry(msg->mboxname, &t->remote);
	    }
	    else { /* signal process to update */
		if (verbose || debugmode)
		    syslog(LOG_DEBUG, "    fwd NOTIFY %s\n", idle_id_from_addr(&t->remote));

		/* forward the received msg onto our clients */
		r = idle_send(&t->remote, msg);
		if (r) {
		    /* ENOENT can happen as result of a race between delivering
		     * messages and shutting down imapd.  It indicates that the
		     * imapd's socket was unlinked, which means that imapd went
		     * through it's graceful shutdown path, so don't syslog. */
		    if (r != ENOENT)
			syslog(LOG_ERR, "IDLE: error sending message "
					"NOTIFY to imapd %s for mailbox %s: %s, ",
					"forgetting.",
					idle_id_from_addr(&t->remote),
					msg->mboxname, error_message(r));
		    if (verbose || debugmode)
			syslog(LOG_DEBUG, "    forgetting %s\n", idle_id_from_addr(&t->remote));
		    remove_ientry(msg->mboxname, &t->remote);
		}
	    }
	}
	break;

    case IDLE_MSG_DONE:
	if (verbose || debugmode)
	    syslog(LOG_DEBUG, "imapd[%s]: IDLE_MSG_DONE '%s'\n",
		   idle_id_from_addr(remote), msg->mboxname);

	/* remove client from list of those idling on mboxname */
	remove_ientry(msg->mboxname, remote);
	break;

    case IDLE_MSG_NOOP:
	break;

    default:
	syslog(LOG_ERR, "unrecognized message: %lx", msg->which);
	break;
    }
}


static void send_alert(const char *key,
		       void *data,
		       void *rock __attribute__((unused)))
{
    struct ientry *t = (struct ientry *) data;
    struct ientry *n;
    idle_message_t msg;
    int r;

    msg.which = IDLE_MSG_ALERT;
    strncpy(msg.mboxname, ".", sizeof(msg.mboxname));


    for ( ; t ; t = n) {
	n = t->next;

	/* signal process to check ALERTs */
	if (verbose || debugmode)
	    syslog(LOG_DEBUG, "    ALERT %s\n", idle_id_from_addr(&t->remote));

	r = idle_send(&t->remote, &msg);
	if (r) {
	    /* ENOENT can happen as result of a race between shutting
	     * down idled and shutting down imapd.  It indicates that the
	     * imapd's socket was unlinked, which means that imapd went
	     * through it's graceful shutdown path, so don't syslog. */
	    if (r != ENOENT)
		syslog(LOG_ERR, "IDLE: error sending message "
				"ALERT to imapd %s: %s, ",
				"forgetting.",
				idle_id_from_addr(&t->remote),
				msg.mboxname, error_message(r));
	    if (verbose || debugmode)
		syslog(LOG_DEBUG, "    forgetting %s\n", idle_id_from_addr(&t->remote));
	    remove_ientry(key, &t->remote);
	}
    }
}

static void sighandler(int sig __attribute__((unused)))
{
    sigquit = 1;
    return;
}

int main(int argc, char **argv)
{
    char *p = NULL;
    int opt;
    int nmbox = 0;
    int s;
    struct sockaddr_un local;
    fd_set read_set, rset;
    int nfds;
    struct timeval timeout;
    pid_t pid;
    char *alt_config = NULL;
    struct sigaction action;

    p = getenv("CYRUS_VERBOSE");
    if (p) verbose = atoi(p) + 1;

    while ((opt = getopt(argc, argv, "C:d")) != EOF) {
	switch (opt) {
        case 'C': /* alt config file */
            alt_config = optarg;
            break;
	case 'd': /* don't fork. debugging mode */
	    debugmode = 1;
	    break;
	default:
	    fprintf(stderr, "invalid argument\n");
	    exit(EC_USAGE);
	    break;
	}
    }

    cyrus_init(alt_config, "idled", 0, 0);

    /* Set inactivity timer (convert from minutes to seconds) */
    idle_timeout = config_getint(IMAPOPT_TIMEOUT);
    if (idle_timeout < 30) idle_timeout = 30;
    idle_timeout *= 60;

    /* count the number of mailboxes */
    mboxlist_init(0);
    mboxlist_open(NULL);
    cyrusdb_foreach(mbdb, "", 0, NULL, &mbox_count_cb,
				&nmbox, NULL);
    mboxlist_close();
    mboxlist_done();

    sigemptyset(&action.sa_mask);

    action.sa_flags = 0;
    action.sa_handler = sighandler;
    if (sigaction(SIGQUIT, &action, NULL) < 0)
	fatal("unable to install signal handler for SIGQUIT", 1);
    if (sigaction(SIGINT, &action, NULL) < 0)
	fatal("unable to install signal handler for SIGINT", 1);
    if (sigaction(SIGTERM, &action, NULL) < 0)
	fatal("unable to install signal handler for SIGTERM", 1);

    /* create idle table -- +1 to avoid a zero value */
    construct_hash_table(&itable, nmbox + 1, 1);

    if (!idle_make_server_address(&local) ||
	!idle_init_sock(&local)) {
	cyrus_done();
	exit(1);
    }
    s = idle_get_sock();

    /* fork unless we were given the -d option */
    if (debugmode == 0) {

	pid = fork();

	if (pid == -1) {
	    perror("fork");
	    exit(1);
	}

	if (pid != 0) { /* parent */
	    exit(0);
	}
    }
    /* child */


    /* get ready for select() */
    FD_ZERO(&read_set);
    FD_SET(s, &read_set);
    nfds = s + 1;

    for (;;) {
	int n;

	/* check for shutdown file */
	if (shutdown_file(NULL, 0)) {
	    /* signal all processes to shutdown */
	    if (verbose || debugmode)
		syslog(LOG_DEBUG, "IDLE_ALERT\n");

	    hash_enumerate(&itable, send_alert, NULL);
	    break;
	}
	if (sigquit) {
	    hash_enumerate(&itable, send_alert, NULL);
	    break;
	}

	/* timeout for select is 1 second */
	timeout.tv_sec = 1;
	timeout.tv_usec = 0;

	/* check for the next input */
	rset = read_set;
	n = select(nfds, &rset, NULL, NULL, &timeout);
	if (n < 0 && errno == EAGAIN) continue;
	if (n < 0 && errno == EINTR) continue;
	if (n == -1) {
	    /* uh oh */
	    syslog(LOG_ERR, "select(): %m");
	    close(s);
	    fatal("select error",-1);
	}

	/* read and process a message */
	if (FD_ISSET(s, &rset)) {
	    struct sockaddr_un from;
	    idle_message_t msg;

	    if (idle_recv(&from, &msg))
		process_message(&from, &msg);
	}

    }

    idle_done_sock();
    cyrus_done();

    exit(1);
}

