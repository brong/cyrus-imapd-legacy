/* fud.c -- long-lived finger information provider
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
 * $Id: fud.c,v 1.59 2010/06/28 12:04:16 brong Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <syslog.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <errno.h>
#include <pwd.h>

#include "assert.h"
#include "mboxlist.h"
#include "global.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "mailbox.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "acl.h"
#include "seen.h"
#include "mboxname.h"
#include "map.h"

#define REQ_OK		0
#define REQ_DENY	1
#define REQ_UNK		2

extern int optind;

/* current namespace */
static struct namespace fud_namespace;

/* config.c info.  note that technically we may need partition data, but
 * only if we're not on a frontend, so we won't flat-out require it here */
const int config_need_data = 0;

/* forward decls */
extern void setproctitle_init(int argc, char **argv, char **envp);

int handle_request(const char *who, const char *name, 
		   struct sockaddr_storage sfrom, socklen_t sfromsiz);

void send_reply(struct sockaddr_storage sfrom, socklen_t sfromsiz, int status,
		const char *user, const char *mbox,
		int numrecent, time_t lastread, time_t lastarrived);

int soc = 0; /* inetd (master) has handed us the port as stdin */

char who[16];

#define MAXLOGNAME 16		/* should find out for real */
#define MAXDOMNAME 20		/* should find out for real */

int begin_handling(void)
{
        struct sockaddr_storage sfrom;
        socklen_t sfromsiz = sizeof(sfrom);
        int r;
        char    buf[MAXLOGNAME + MAXDOMNAME + MAX_MAILBOX_BUFFER];
        char    username[MAXLOGNAME + MAXDOMNAME + 1];
        char    mbox[MAX_MAILBOX_BUFFER];
        char    *q;
        int     off;
	int     maxuserlen = MAXLOGNAME;

	if (config_virtdomains) 
	    maxuserlen += MAXDOMNAME + 1; /* @ + DOM */

        while(1) {
            /* For safety */
            memset(buf, 0, sizeof(buf));
            memset(username, 0, sizeof(username));
            memset(mbox, 0, sizeof(mbox));

	    if (signals_poll() == SIGHUP) {
		/* caught a SIGHUP, return */
		return 0;
	    }
            r = recvfrom(soc, buf, 511, 0, 
			 (struct sockaddr *) &sfrom, &sfromsiz);
            if (r == -1) {
		return(errno);
	    }
            for(off = 0; buf[off] != '|' && off < maxuserlen; off++);
            if(off > 0 && off < maxuserlen) {
		strncpy(username,buf,off);
		username[off] = '\0';
            } else {
		continue;
            }

	    /* Copy what is past the | to the mailbox name */
            q = buf + off + 1;
            strlcpy(mbox, q, sizeof(mbox));

            handle_request(username,mbox,sfrom,sfromsiz);
        }

	/* never reached */
}

void shut_down(int code) __attribute__((noreturn));
void shut_down(int code)
{
    seen_done();
    mboxlist_close();
    mboxlist_done();
    closelog();
    cyrus_done();
    exit(code);
}


/*
 * run once when process is forked;
 * MUST NOT exit directly; must return with non-zero error code
 */
int service_init(int argc, char **argv, char **envp)
{
    if (geteuid() == 0) fatal("must run as the Cyrus user", EC_USAGE);

    setproctitle_init(argc, argv, envp);

    signals_set_shutdown(&shut_down);

    mboxlist_init(0);
    mboxlist_open(NULL);

    return 0;
}

/* Called by service API to shut down the service */
void service_abort(int error)
{
    shut_down(error);
}

int service_main(int argc __attribute__((unused)),
		 char **argv __attribute__((unused)),
		 char **envp __attribute__((unused)))
{
    int r = 0; 

    /* Set namespace */
    if ((r = mboxname_init_namespace(&fud_namespace, 1)) != 0) {
	syslog(LOG_ERR, "%s", error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

    r = begin_handling();

    shut_down(r);
    return 0;
}

static void cyrus_timeout(int signo __attribute__((unused)))
{
    return;
}

static int setsigalrm(int enable)

{
    struct sigaction action;
    
    sigemptyset(&action.sa_mask);
    
    action.sa_flags = 0;

    if(enable) {
	action.sa_handler = cyrus_timeout;
    } else {
	action.sa_handler = SIG_IGN;
    }
    
    if (sigaction(SIGALRM, &action, NULL) < 0) {
	syslog(LOG_ERR, "installing SIGALRM handler: sigaction: %m");
	return -1;
    }
    
    return 0;
}


/* Send a proxy request to the backend, send their reply to sfrom */
int do_proxy_request(const char *who, const char *name,
		     const char *backend_host,
		     struct sockaddr_storage sfrom, socklen_t sfromsiz) 
{
    char tmpbuf[1024];
    int rc;
    int csoc = -1;
    int error;
    struct sockaddr_storage cin, cout;
    struct addrinfo hints, *res0, *res;
    socklen_t cinsiz, coutsiz;
    static char *backend_port = NULL; /* fud port */

    /* Open a UDP socket to the Cyrus mail server */
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = PF_UNSPEC;
    hints.ai_socktype = SOCK_DGRAM;
    if (!backend_port) {
	backend_port = "fud";
	error = getaddrinfo(backend_host, backend_port, &hints, &res0);
	if (error == EAI_SERVICE) {
	    backend_port = "4201"; /* default fud port */
	    error = getaddrinfo(backend_host, backend_port, &hints, &res0);
	}
    } else
	error = getaddrinfo(backend_host, backend_port, &hints, &res0);
    if (error != 0) {
	send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	rc = IMAP_SERVER_UNAVAILABLE;
	goto done;
    }
    
    /*
     * XXX: Since UDP is used, we cannot use an IPv6->IPv4 fallback
     * strategy, here.  So, when we can use same address family with
     * incoming packet, just try it.  When same address family is not
     * found in DNS, we try another one.
     */
    csoc = -1;
    for (res = res0; res; res = res->ai_next) {
	if (res->ai_family == sfrom.ss_family) {
	    csoc = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
	    break;
	}
    }
    if (csoc < 0) {
	for (res = res0; res; res = res->ai_next) {
	    if (res->ai_family != sfrom.ss_family &&
		(res->ai_family == AF_INET || res->ai_family == AF_INET6)) {
		csoc = socket(res->ai_family, res->ai_socktype,
			      res->ai_protocol);
		break;
	    }
	}
    }
    if (csoc < 0) {
	send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	rc = IMAP_SERVER_UNAVAILABLE;
	freeaddrinfo(res0);	
	goto done;
    }

    memcpy(&cin, res->ai_addr, res->ai_addrlen);
    cinsiz = res->ai_addrlen;
    freeaddrinfo(res0);

    /* Write a Cyrus query into *tmpbuf */
    memset (tmpbuf, '\0', sizeof(tmpbuf));
    snprintf (tmpbuf, sizeof(tmpbuf), "%s|%s", who, name);

    /* Send the query and wait for a reply */
    sendto (csoc, tmpbuf, strlen (tmpbuf), 0,
	    (struct sockaddr *) &cin, cinsiz);
    memset (tmpbuf, '\0', strlen (tmpbuf));

    if (setsigalrm(1) < 0) {
	rc = IMAP_SERVER_UNAVAILABLE;
	send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	goto done;
    }

    rc = 0;
    coutsiz = sizeof(cout);
    alarm (1);
    rc = recvfrom (csoc, tmpbuf, sizeof(tmpbuf), 0,
		   (struct sockaddr *) &cout, &coutsiz);
    alarm (0);

    setsigalrm(0);  /* Failure isn't really terrible here */

    if (rc < 1) {
	rc = IMAP_SERVER_UNAVAILABLE;
	send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	goto done;
    }

    /* Send reply back */
    /* rc is size */
    sendto(soc, tmpbuf, rc, 0, (struct sockaddr *) &sfrom, sfromsiz);
    rc = 0;

 done:
    if(csoc != -1) close(csoc);
    return rc;
}

int handle_request(const char *who, const char *name,
		   struct sockaddr_storage sfrom, socklen_t sfromsiz)
{
    int r;
    struct mailbox *mailbox;
    time_t lastread;
    time_t lastarrived;
    unsigned recentuid;
    unsigned numrecent;
    char mboxname[MAX_MAILBOX_BUFFER];
    struct mboxlist_entry mbentry;
    struct auth_state *mystate;
    int internalseen;

    numrecent = 0;
    lastread = 0;
    lastarrived = 0;

    r = (*fud_namespace.mboxname_tointernal)(&fud_namespace,name,who,mboxname);
    if (r) return r; 

    r = mboxlist_lookup(mboxname, &mbentry, NULL);
    if(r || mbentry.mbtype & MBTYPE_RESERVE) {
	send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	return r;
    }

    mystate = auth_newstate("anonymous");

    if(mbentry.mbtype & MBTYPE_REMOTE) {
	char *p = NULL;

	/* xxx hide that we are storing partitions */
	p = strchr(mbentry.partition, '!');
	if(p) *p = '\0';

	/* Check the ACL */
	if(cyrus_acl_myrights(mystate, mbentry.acl) & ACL_USER0) {
	    /* We want to proxy this one */
	    auth_freestate(mystate);
	    return do_proxy_request(who, name, mbentry.partition, sfrom, sfromsiz);
	} else {
	    /* Permission Denied */
	    auth_freestate(mystate);
	    send_reply(sfrom, sfromsiz, REQ_DENY, who, name, 0, 0, 0);
	    return 0;
	}
    }

    /*
     * Open/lock header 
     */
    r = mailbox_open_irl(mboxname, &mailbox);
    if (r) {
        send_reply(sfrom, sfromsiz, REQ_UNK, who, name, 0, 0, 0);
	return r; 
    }

    if (mboxname_isusermailbox(mboxname, 0)) {
	int myrights = cyrus_acl_myrights(mystate, mailbox->acl);
	if (!(myrights & ACL_USER0)) {
	    auth_freestate(mystate);
	    mailbox_close(&mailbox);
	    send_reply(sfrom, sfromsiz, REQ_DENY, who, name, 0, 0, 0);
	    return 0;
	}
    }
    auth_freestate(mystate);
   
    internalseen = mailbox_internal_seen(mailbox, who);
    if (internalseen) {
	lastread = mailbox->i.recenttime;
	recentuid = mailbox->i.recentuid;
    } else {
	struct seen *seendb;
	struct seendata sd;
	r = seen_open(who, 0, &seendb);

	if (!r) {
	    r = seen_read(seendb, mailbox->uniqueid, &sd);
	    seen_close(seendb);
	}

	if (r) {
	    /* Fake Data -- couldn't open seen database */
	    lastread = 0;
	    recentuid = 0;
	}
	else {
	    lastread = sd.lastread;
	    recentuid = sd.lastuid;
	    seen_freedata(&sd);
	}
    }

    lastarrived = mailbox->i.last_appenddate;
    {
	struct index_record record;
	int recno;
	for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	    if (mailbox_read_index_record(mailbox, recno, &record))
		continue;
	    if (record.system_flags & FLAG_EXPUNGED)
		continue;
	    if (record.uid > recentuid) numrecent++;
	}
    }

    mailbox_close(&mailbox);
    
    send_reply(sfrom, sfromsiz, REQ_OK, who, name, numrecent,
	       lastread, lastarrived);
    
    return(0);
}

void
send_reply(struct sockaddr_storage sfrom, socklen_t sfromsiz,
	   int status, const char *user, const char *mbox,
	   int numrecent, time_t lastread, time_t lastarrived)
{
    char buf[MAX_MAILBOX_PATH + 16 + 9];
    int siz;

    switch(status) {
        case REQ_DENY:
            sendto(soc,"PERMDENY",9,0,(struct sockaddr *) &sfrom, sfromsiz);       
            break;
        case REQ_OK:
            siz = snprintf(buf, sizeof(buf), "%s|%s|%d|%d|%d",
			   user,mbox,numrecent,(int) lastread,
			   (int)lastarrived);
            sendto(soc,buf,siz,0,(struct sockaddr *) &sfrom, sfromsiz);       
            break;
        case REQ_UNK:
            sendto(soc,"UNKNOWN",8,0,(struct sockaddr *) &sfrom, sfromsiz);
            break;
    } 
}

void fatal(const char* s, int code)
{
    static int recurse_code = 0;
    if (recurse_code) {
        /* We were called recursively. Just give up */
	exit(code);
    }
    recurse_code = code;
    syslog(LOG_ERR, "Fatal error: %s", s);

    shut_down(code);
}

void printstring(const char *s __attribute__((unused)))
{
    /* needed to link against annotate.o */
    fatal("printstring() executed, but its not used for FUD!",
	  EC_SOFTWARE);
}
