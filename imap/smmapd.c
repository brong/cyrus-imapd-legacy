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
 * $Id: smmapd.c,v 1.23 2010/01/06 17:01:40 murch Exp $
 *
 * smmapd.c -- sendmail socket map daemon
 *
 *
 * From Sendmail Operations Guide:
 *
 * The socket map uses a simple request/reply protocol over TCP or
 * UNIX domain sockets to query an external server.  Both requests and
 * replies are text based and encoded as netstrings, i.e., a string
 * "hello there" becomes:
 *
 * 11:hello there,
 *
 * Note: neither requests nor replies end with CRLF.
 *
 * The request consists of the database map name and the lookup key
 * separated by a space character:
 *
 * <mapname> � � <key>
 *
 * The server responds with a status indicator and the result (if any):
 *
 * <status> � � <result>
 *
 * The status indicator is one of the following upper case words:
 *
 * OK		the key was found, result contains the looked up value
 * NOTFOUND	the key was not found, the result is empty
 * TEMP		a temporary failure occured
 * TIMEOUT	a timeout occured on the server side
 * PERM		a permanent failure occured
 *
 * In case of errors (status TEMP, TIMEOUT or PERM) the result field
 * may contain an explanatory message.
 *
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#include <string.h>
#include <syslog.h>
#include <signal.h>
#include <ctype.h>

#include "acl.h"
#include "append.h"
#include "mboxlist.h"
#include "global.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "mupdate-client.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

const char *BB;
int forcedowncase;

extern int optind;

struct protstream *map_in, *map_out;

/* current namespace */
static struct namespace map_namespace;

/* config.c info */
const int config_need_data = 0;

/* forward decls */
extern void setproctitle_init(int argc, char **argv, char **envp);
int begin_handling(void);

void smmapd_reset(void)
{
    if (map_in) {
	/* Flush the incoming buffer */
	prot_NONBLOCK(map_in);
	prot_fill(map_in);
	prot_free(map_in);
    }

    if (map_out) {
	/* Flush the outgoing buffer */
	prot_flush(map_out);
	prot_free(map_out);
    }

    map_in = map_out = NULL;

    cyrus_reset_stdio(); 
}

void shut_down(int code) __attribute__((noreturn));
void shut_down(int code)
{
    smmapd_reset();

    mboxlist_close();
    mboxlist_done();

    quotadb_close();
    quotadb_done();

    cyrus_done();
    exit(code);
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
    abort();

    shut_down(code);
}

/*
 * run once when process is forked;
 * MUST NOT exit directly; must return with non-zero error code
 */
int service_init(int argc, char **argv, char **envp)
{
    int r;

    if (geteuid() == 0) fatal("must run as the Cyrus user", EC_USAGE);

    setproctitle_init(argc, argv, envp);

    signals_set_shutdown(&shut_down);
    signal(SIGPIPE, SIG_IGN);

    BB = config_getstring(IMAPOPT_POSTUSER);
    forcedowncase = config_getswitch(IMAPOPT_LMTP_DOWNCASE_RCPT);

    /* so we can do mboxlist operations */
    mboxlist_init(0);
    mboxlist_open(NULL);

    /* so we can check the quotas */
    quotadb_init(0);
    quotadb_open(NULL);

    /* Set namespace */
    if ((r = mboxname_init_namespace(&map_namespace, 1)) != 0) {
	syslog(LOG_ERR, "%s", error_message(r));
	fatal(error_message(r), EC_CONFIG);
    }

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

    map_in = prot_new(0, 0);
    map_out = prot_new(1, 1);
    prot_setflushonread(map_in, map_out);
    prot_settimeout(map_in, 360);

    if (begin_handling() != 0) shut_down(0);

    /* prepare for new connection */
    smmapd_reset();
    return 0;
}

int verify_user(const char *key, long quotacheck,
		struct auth_state *authstate)
{
    char rcpt[MAX_MAILBOX_BUFFER], namebuf[MAX_MAILBOX_BUFFER] = "";
    char *user = rcpt, *domain = NULL, *mailbox = NULL;
    int r = 0;

    /* make a working copy of the key and split it into user/domain/mailbox */
    strlcpy(rcpt, key, sizeof(rcpt));

    /* find domain */
    if (config_virtdomains && (domain = strrchr(rcpt, '@'))) {
	*domain++ = '\0';
	/* ignore default domain */
	if (config_defdomain && !strcasecmp(config_defdomain, domain))
	    domain = NULL;
    }

    /* translate any separators in user & mailbox */
    mboxname_hiersep_tointernal(&map_namespace, rcpt, 0);

    /* find mailbox */
    if ((mailbox = strchr(rcpt, '+'))) *mailbox++ = '\0';

    /* downcase the rcpt, if necessary */
    if (forcedowncase) {
	lcase(user);
	if (domain) lcase(domain);
    }

    /* see if its a shared mailbox address */
    if (!strcmp(user, BB)) user = NULL;

    /* XXX  the following is borrowed from lmtpd.c:verify_user() */
    if ((!user && !mailbox) ||
	(domain && (strlen(domain) + 1 > sizeof(namebuf)))) {
	r = IMAP_MAILBOX_NONEXISTENT;
    } else {
	/* construct the mailbox that we will verify */
	if (domain) snprintf(namebuf, sizeof(namebuf), "%s!", domain);

	if (!user) {
	    /* shared folder */
	    if (strlen(namebuf) + strlen(mailbox) > sizeof(namebuf)) {
 		r = IMAP_MAILBOX_NONEXISTENT;
	    } else {
		strlcat(namebuf, mailbox, sizeof(namebuf));
	    }
	} else {
	    /* ordinary user -- check INBOX */
	    if (strlen(namebuf) + 5 + strlen(user) > sizeof(namebuf)) {
		r = IMAP_MAILBOX_NONEXISTENT;
	    } else {
		strlcat(namebuf, "user.", sizeof(namebuf));
		strlcat(namebuf, user, sizeof(namebuf));
	    }
	}
    }

    if (!r) {
	long aclcheck = !user ? ACL_POST : 0;
        struct mboxlist_entry mbentry;
        char *c;
        struct hostent *hp;
        char *host;
        struct sockaddr_in sin,sfrom;
        char buf[512];
        int soc, rc;
	socklen_t x;

	/*
	 * check to see if mailbox exists and we can append to it:
	 *
	 * - must have posting privileges on shared folders
	 * - don't care about ACL on INBOX (always allow post)
	 * - don't care about message size (1 msg over quota allowed)
	 */
	r = mboxlist_lookup(namebuf, &mbentry, NULL);
	if (r == IMAP_MAILBOX_NONEXISTENT && config_mupdate_server) {
	    kick_mupdate();
	    r = mboxlist_lookup(namebuf, &mbentry, NULL);
	}

	if (!r && (mbentry.mbtype & MBTYPE_REMOTE)) {
	    /* XXX  Perhaps we should support the VRFY command in lmtpd
	     * and then we could do a VRFY to the correct backend which
	     * would also do a quotacheck.
	     */
	    int access = cyrus_acl_myrights(authstate, mbentry.acl);

	    if ((access & aclcheck) != aclcheck) {
		r = (access & ACL_LOOKUP) ?
		    IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
                return r;
	    } else {
                r = 0;
            }

            /* proxy the request to the real backend server to 
             * check the quota.  if this fails, just return 0
             * (asuume under quota)
             */

            host = xstrdup(mbentry.partition);
            c = strchr(host, '!');
            if (c) *c = 0;

            syslog(LOG_ERR, "verify_user(%s) proxying to host %s",
                   namebuf, host);

            hp = gethostbyname(host);
            if (hp == (struct hostent*) 0) {
               syslog(LOG_ERR, "verify_user(%s) failed: can't find host %s",
                      namebuf, host);
               return r;
            }

            soc = socket(PF_INET, SOCK_STREAM, 0);
	    if (soc < 0) {
                syslog(LOG_ERR, "verify_user(%s) failed: can't connect to %s", 
                       namebuf, host);
		free(host);
		return r;
	    }
            memcpy(&sin.sin_addr.s_addr,hp->h_addr,hp->h_length);
            sin.sin_family = AF_INET;

            /* XXX port should be configurable */
            sin.sin_port = htons(12345);

            if (connect(soc,(struct sockaddr *) &sin, sizeof(sin)) < 0) { 
                syslog(LOG_ERR, "verify_user(%s) failed: can't connect to %s", 
                       namebuf, host);
		free(host);
                return r;
            }

            sprintf(buf,SIZE_T_FMT ":cyrus %s,%c",strlen(key)+6,key,4);
            sendto(soc,buf,strlen(buf),0,(struct sockaddr *)&sin,sizeof(sin));

            x = sizeof(sfrom);
            rc = recvfrom(soc,buf,512,0,(struct sockaddr *)&sfrom,&x);
 
            close(soc);

            if (rc >= 0) {
		buf[rc] = '\0';
		prot_printf(map_out, "%s", buf);
	    }
	    free(host);
            return -1;   /* tell calling function we already replied */

	} else if (!r) {
	    r = append_check(namebuf, authstate,
			     aclcheck, (quotacheck < 0 )
			     || config_getswitch(IMAPOPT_LMTP_STRICT_QUOTA) ?
			     quotacheck : 0);
	}
    }

    if (r) syslog(LOG_DEBUG, "verify_user(%s) failed: %s", namebuf,
		  error_message(r));

    return r;
}

/*
 * begin_handling: handle requests on a single connection.
 * returns non-zero if requested to stop handling new connections (SIGHUP)
 */
#define MAXREQUEST 1024		/* XXX  is this reasonable? */

int begin_handling(void)
{
    int c;

    while ((c = prot_getc(map_in)) != EOF) {
	int r = 0, len = 0, size = 0;
	struct auth_state *authstate = NULL;
	char request[MAXREQUEST+1];
	char *mapname = NULL, *key = NULL;
	const char *errstring = NULL;

	if (signals_poll() == SIGHUP) {
	    /* caught a SIGHUP, return */
	    return 1;
	}

	prot_ungetc(c, map_in);
	c = getint32(map_in, &len);
	if (c == EOF) {
	    errstring = prot_error(map_in);
	    r = IMAP_IOERROR;
	}
	if (len == -1 || c != ':') {
	    errstring = "missing length";
	    r = IMAP_PROTOCOL_ERROR;
	}
	if (!r && prot_read(map_in, request, len) != len) {
	    errstring = "request size doesn't match length";
	    r = IMAP_PROTOCOL_ERROR;
	}
	if (!r && (c = prot_getc(map_in)) != ',') {
	    errstring = "missing terminator";
	    r = IMAP_PROTOCOL_ERROR;
	}

	if (!r) {
	    request[len] = '\0';
	    mapname = request;
	    if (!(key = strchr(request, ' '))) {
		errstring = "missing key";
		r = IMAP_PROTOCOL_ERROR;
	    }
	}

	if (!r) {
	    *key++ = '\0';

	    r = verify_user(key, size, authstate);
	}

	switch (r) {
        case -1:
            /* reply already sent */
            break;

	case 0:
	    prot_printf(map_out, SIZE_T_FMT ":OK %s,", 3+strlen(key), key);
	    break;

	case IMAP_MAILBOX_NONEXISTENT:
	    prot_printf(map_out, SIZE_T_FMT ":NOTFOUND %s,",
			9+strlen(error_message(r)), error_message(r));
	    break;

	case IMAP_QUOTA_EXCEEDED:
	    if (!config_getswitch(IMAPOPT_LMTP_OVER_QUOTA_PERM_FAILURE)) {
		prot_printf(map_out, SIZE_T_FMT ":TEMP %s,", strlen(error_message(r))+5,
			    error_message(r));
		break;
	    }
	    /* fall through - permanent failure */

	default:
	    if (errstring)
		prot_printf(map_out, SIZE_T_FMT ":PERM %s (%s),",
			    5+strlen(error_message(r))+3+strlen(errstring),
			    error_message(r), errstring);
	    else
		prot_printf(map_out, SIZE_T_FMT ":PERM %s,",
			    5+strlen(error_message(r)), error_message(r));
	    break;
	}
    }

    return 0;
}

void printstring(const char *s __attribute__((unused)))
{
    /* needed to link against annotate.o */
    fatal("printstring() executed, but its not used for smmapd!",
	  EC_SOFTWARE);
}
