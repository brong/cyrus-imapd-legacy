/*
 * lmtp_proxy.c - LMTP proxy support functions
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
 *    "This product includes software developed by Computing Services
 *    acknowledgment:
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
 * $Id: lmtp_proxy.c,v 1.1.2.1 2004/02/14 16:15:14 ken3 Exp $
 */

#include <config.h>

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <syslog.h>
#include <sys/un.h>

#include "backend.h"
#include "exitcodes.h"
#include "global.h"
#include "imap_err.h"
#include "lmtpengine.h"
#include "lmtp_proxy.h"
#include "mboxname.h"
#include "mupdate-client.h"
#include "prot.h"
#include "xmalloc.h"

extern struct backend **backend_cached;

/* return the connection to the server */
struct backend *proxyd_findserver(const char *server)
{
    int i = 0;
    struct backend *ret = NULL;

    while (backend_cached && backend_cached[i]) {
	if (!strcmp(server, backend_cached[i]->hostname)) {
	    ret = backend_cached[i];
	    /* ping/noop the server */
	    if (backend_ping(ret, &protocol[PROTOCOL_LMTP])) {
		backend_disconnect(ret, &protocol[PROTOCOL_LMTP]);
	    }
	    break;
	}
	i++;
    }

    if (!ret || (ret->sock == -1)) {
	/* need to (re)establish connection to server or create one */
	ret = backend_connect(ret, server, &protocol[PROTOCOL_LMTP], "", NULL);
	if (!ret) return NULL;
    }

    /* insert server in list of cached connections */
    if (!backend_cached[i]) {
	backend_cached = (struct backend **) 
	    xrealloc(backend_cached, (i + 2) * sizeof(struct backend *));
	backend_cached[i] = ret;
	backend_cached[i + 1] = NULL;
    }

    return ret;
}

void adddest(remote_msgdata_t *mydata, const char *rcpt,
	     char *server, char *mailbox, const char *authas)
{
    struct rcpt *new_rcpt = xmalloc(sizeof(struct rcpt));
    struct dest *d;

    strlcpy(new_rcpt->rcpt, rcpt, sizeof(new_rcpt->rcpt));
    new_rcpt->rcpt_num = mydata->cur_rcpt;
    
    /* see if we currently have a 'mailboxdata->server'/'authas' 
       combination. */
    d = mydata->dlist;
    for (d = mydata->dlist; d != NULL; d = d->next) {
	if (!strcmp(d->server, server) && 
	    !strcmp(d->authas, authas ? authas : "")) break;
    }

    if (d == NULL) {
	/* create a new one */
	d = xmalloc(sizeof(struct dest));
	strlcpy(d->server, server, sizeof(d->server));
	strlcpy(d->authas, authas ? authas : "", sizeof(d->authas));
	d->rnum = 0;
	d->to = NULL;
	d->next = mydata->dlist;
	mydata->dlist = d;
    }

    /* add rcpt to d */
    d->rnum++;
    new_rcpt->next = d->to;
    d->to = new_rcpt;
}

void runme(remote_msgdata_t *mydata, message_data_t *msgdata)
{
    struct dest *d;

    /* run the txns */
    d = mydata->dlist;
    while (d) {
	struct lmtp_txn *lt = LMTP_TXN_ALLOC(d->rnum);
	struct rcpt *rc;
	struct backend *remote;
	int i = 0;
	int r = 0;
	
	lt->from = msgdata->return_path;
	lt->auth = d->authas[0] ? d->authas : NULL;
	lt->isdotstuffed = 0;
	
	prot_rewind(msgdata->data);
	lt->data = msgdata->data;
	lt->rcpt_num = d->rnum;
	rc = d->to;
	for (rc = d->to; rc != NULL; rc = rc->next, i++) {
	    assert(i < d->rnum);
	    lt->rcpt[i].addr = rc->rcpt;
	    lt->rcpt[i].ignorequota =
		msg_getrcpt_ignorequota(msgdata, rc->rcpt_num);
	}
	assert(i == d->rnum);

	remote = proxyd_findserver(d->server);
	if (remote) {
	    r = lmtp_runtxn(remote, lt);
	} else {
	    /* remote server not available; tempfail all deliveries */
	    for (rc = d->to, i = 0; i < d->rnum; i++) {
		lt->rcpt[i].result = RCPT_TEMPFAIL;
		lt->rcpt[i].r = IMAP_SERVER_UNAVAILABLE;
	    }
	}

	/* process results of the txn, propogating error state to the
	   recipients */
	for (rc = d->to, i = 0; rc != NULL; rc = rc->next, i++) {
	    int j = rc->rcpt_num;
	    switch (mydata->pend[j]) {
	    case s_wait:
		/* hmmm, if something fails we'll want to try an 
		   error delivery */
		if (lt->rcpt[i].result != RCPT_GOOD) {
		    mydata->pend[j] = s_err;
		}
		break;
	    case s_err:
		/* we've already detected an error for this recipient,
		   and nothing will convince me otherwise */
		break;
	    case nosieve:
		/* this is the only delivery we're attempting for this rcpt */
		msg_setrcpt_status(msgdata, j, lt->rcpt[i].r);
		mydata->pend[j] = done;
		break;
	    case done:
	    case s_done:
		/* yikes! we shouldn't be getting a notification for this
		   person! */
		abort();
		break;
	    }
	}

	free(lt);
	d = d->next;
    }
}

void kick_mupdate(void)
{
    char buf[2048];
    struct sockaddr_un srvaddr;
    int s, r;
    int len;
    
    s = socket(AF_UNIX, SOCK_STREAM, 0);
    if (s == -1) {
	syslog(LOG_ERR, "socket: %m");
	return;
    }

    strlcpy(buf, config_dir, sizeof(buf));
    strlcat(buf, FNAME_MUPDATE_TARGET_SOCK, sizeof(buf));
    memset((char *)&srvaddr, 0, sizeof(srvaddr));
    srvaddr.sun_family = AF_UNIX;
    strcpy(srvaddr.sun_path, buf);
    len = sizeof(srvaddr.sun_family) + strlen(srvaddr.sun_path) + 1;

    r = connect(s, (struct sockaddr *)&srvaddr, len);
    if (r == -1) {
	syslog(LOG_ERR, "kick_mupdate: can't connect to target: %m");
	close(s);
	return;
    }

    r = read(s, buf, sizeof(buf));
    if (r <= 0) {
	syslog(LOG_ERR, "kick_mupdate: can't read from target: %m");
	close(s);
	return;
    }

    /* if we got here, it's been kicked */
    close(s);
    return;
}
