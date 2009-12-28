/* message.c -- message parsing functions
 * Larry Greenfield
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
 * $Id: message.c,v 1.29.2.2 2009/12/28 21:51:54 murch Exp $
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>

#include "md5global.h"
#include "md5.h"
#include "sieve_interface.h"
#include "interp.h"
#include "message.h"
#include "parseaddr.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "util.h"

/* reject message m with message msg
 *
 * incompatible with: fileinto, redirect
 */
int do_reject(action_list_t *a, const char *msg)
{
    action_list_t *b = NULL;

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_FILEINTO ||
	    a->a == ACTION_KEEP ||
	    a->a == ACTION_REDIRECT ||
	    a->a == ACTION_REJECT ||
	    a->a == ACTION_VACATION ||
	    a->a == ACTION_SETFLAG ||
	    a->a == ACTION_ADDFLAG ||
	    a->a == ACTION_REMOVEFLAG ||
	    a->a == ACTION_MARK ||
	    a->a == ACTION_UNMARK
	    )
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_REJECT;
    a->cancel_keep = 1;
    a->u.rej.msg = msg;
    b->next = a;
    a->next =  NULL;
    return 0;
}

/* fileinto message m into mailbox 
 *
 * incompatible with: reject
 */
int do_fileinto(action_list_t *a, const char *mbox, int cancel_keep,
		sieve_imapflags_t *imapflags)
{
    action_list_t *b = NULL;

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_FILEINTO;
    a->cancel_keep = cancel_keep;
    a->u.fil.mailbox = mbox;
    a->u.fil.imapflags = imapflags;
    b->next = a;
    a->next = NULL;
    return 0;
}

/* redirect message m to to addr
 *
 * incompatible with: reject
 */
int do_redirect(action_list_t *a, const char *addr, int cancel_keep)
{
    action_list_t *b = NULL;

    /* xxx we should validate addr */

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_REDIRECT;
    a->cancel_keep = cancel_keep;
    a->u.red.addr = addr;
    a->next = NULL;
    b->next = a;
    return 0;
}

/* keep message
 *
 * incompatible with: reject
 */
int do_keep(action_list_t *a, sieve_imapflags_t *imapflags)
{
    action_list_t *b = NULL;

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	if (a->a == ACTION_KEEP) /* don't bother doing it twice */
	    return 0;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_KEEP;
    a->cancel_keep = 1;
    a->u.keep.imapflags = imapflags;
    a->next = NULL;
    b->next = a;
    return 0;
}

/* discard message m
 *
 * incompatible with: nothing---it doesn't cancel any actions
 */
int do_discard(action_list_t *a)
{
    action_list_t *b = NULL;

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_DISCARD) /* don't bother doing twice */
	    return 0;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_DISCARD;
    a->cancel_keep = 1;
    a->next = NULL;
    b->next = a;
    return 0;
}

static int makehash(unsigned char hash[],
		    const char *s1, const char *s2, const char *s3)
{
    MD5_CTX ctx;

    MD5Init(&ctx);
    MD5Update(&ctx, s1, strlen(s1));
    MD5Update(&ctx, s2, strlen(s2));
    if (s3) MD5Update(&ctx, s3, strlen(s3));
    MD5Final(hash, &ctx);

    return SIEVE_OK;
}

int do_vacation(action_list_t *a, char *addr, char *fromaddr,
		char *subj, const char *msg, int days,
		int mime, const char *handle)
{
    action_list_t *b = NULL;

    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT ||
	    a->a == ACTION_VACATION) /* vacation can't be used twice */
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }

    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_VACATION;
    a->cancel_keep = 0;
    a->u.vac.send.addr = addr;
    a->u.vac.send.fromaddr = fromaddr;
    a->u.vac.send.subj = subj;	/* user specified subject */
    a->u.vac.send.msg = msg;
    a->u.vac.send.mime = mime;
    if (handle)
	makehash(a->u.vac.autoresp.hash, addr, handle, NULL);
    else
	makehash(a->u.vac.autoresp.hash, addr, fromaddr, msg);
    a->u.vac.autoresp.days = days;
    a->next = NULL;
    b->next = a;
    return 0;
}

/* setflag f on message m
 *
 * incompatible with: reject
 */
int do_setflag(action_list_t *a, const char *flag)
{
    action_list_t *b = NULL;
 
    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }
 
    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_SETFLAG;
    a->cancel_keep = 0;
    a->u.fla.flag = flag;
    b->next = a;
    a->next = NULL;
    return 0;
}

/* addflag f on message m
 *
 * incompatible with: reject
 */
int do_addflag(action_list_t *a, const char *flag)
{
    action_list_t *b = NULL;
 
    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }
 
    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_ADDFLAG;
    a->cancel_keep = 0;
    a->u.fla.flag = flag;
    b->next = a;
    a->next = NULL;
    return 0;
}

/* removeflag f on message m
 *
 * incompatible with: reject
 */
int do_removeflag(action_list_t *a, const char *flag)
{
    action_list_t *b = NULL;
 
    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }
 
    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_REMOVEFLAG;
    a->cancel_keep = 0;
    a->u.fla.flag = flag;
    b->next = a;
    a->next = NULL;
    return 0;
}


/* mark message m
 *
 * incompatible with: reject
 */
int do_mark(action_list_t *a)
{
    action_list_t *b = NULL;
 
    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }
 
    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_MARK;
    a->cancel_keep = 0;
    b->next = a;
    a->next = NULL;
    return 0;
}


/* unmark message m
 *
 * incompatible with: reject
 */
int do_unmark(action_list_t *a)
{

    action_list_t *b = NULL;
    /* see if this conflicts with any previous actions taken on this message */
    while (a != NULL) {
	b = a;
	if (a->a == ACTION_REJECT)
	    return SIEVE_RUN_ERROR;
	a = a->next;
    }
 
    /* add to the action list */
    a = (action_list_t *) xmalloc(sizeof(action_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;
    a->a = ACTION_UNMARK;
    a->cancel_keep = 0;
    b->next = a;
    a->next = NULL;
    return 0;
}

/* notify
 *
 * incompatible with: none
 */
int do_notify(notify_list_t *a, const char *id,
	      const char *method, const char **options,
	      const char *priority, const char *message)
{
    notify_list_t *b = NULL;

    /* find the end of the notify list */
    while (a != NULL) {
	b = a;
	a = a->next;
    }

    /* add to the notify list */
    a = (notify_list_t *) xmalloc(sizeof(notify_list_t));
    if (a == NULL)
	return SIEVE_NOMEM;

    b->next = a;
    a->isactive = 1;
    a->id = id;
    a->method = method;
    a->options = options;
    a->priority = priority;
    a->message = message;
    a->next = NULL;
    return 0;
}

/* denotify
 *
 * incomaptible with: none
 */
int do_denotify(notify_list_t *n, comparator_t *comp, const void *pat,
		void *comprock, const char *priority)
{
    while (n != NULL) {
	if (n->isactive && 
	    (!priority || !strcasecmp(n->priority, priority)) &&
	    (!comp || (n->id && comp(n->id, strlen(n->id), pat, comprock)))) {
	    n->isactive = 0;
	}
	n = n->next;
    }

    return 0;
}



/* given a header, extract an address out of it.  if marker points to NULL,
   extract the first address.  otherwise, it's an index into the header to
   say where to start extracting */
struct addr_marker {
    struct address *where;
    char *freeme;
};

int parse_address(const char *header, void **data, void **marker)
{
    struct addr_marker *am = (struct addr_marker *) *marker;

    parseaddr_list(header, (struct address **) data);
    am = (void *) xmalloc(sizeof(struct addr_marker));
    am->where = *data;
    am->freeme = NULL;
    *marker = am;
    return SIEVE_OK;
}

char *get_address(address_part_t addrpart,
		  void **data __attribute__((unused)),
		  void **marker,
		  int canon_domain)
{
    char *ret = NULL;
    struct address *a;
    struct addr_marker *am = *marker;

    a = am->where;
    if (am->freeme) {
	free(am->freeme);
	am->freeme = NULL;
    }

    if (a == NULL) {
	ret = NULL;
    } else {
	if (canon_domain && a->domain)
	    lcase(a->domain);

	switch (addrpart) { 
	case ADDRESS_ALL:
#define U_DOMAIN "unspecified-domain"
#define U_USER "unknown-user"
	    if (a->mailbox || a->domain) {
		char *m = a->mailbox ? a->mailbox : U_USER;
		char *d = a->domain ? a->domain : U_DOMAIN;
		am->freeme = (char *) xmalloc(strlen(m) + strlen(d) + 2);

		sprintf(am->freeme, "%s@%s", m, d);
		ret = am->freeme;
	    } else {
		ret = NULL;
	    }
	    break;

	case ADDRESS_LOCALPART:
	    ret = a->mailbox;
	    break;
	    
	case ADDRESS_DOMAIN:
	    ret = a->domain;
	    break;

	case ADDRESS_USER:
	    if (a->mailbox) {
		char *p = strchr(a->mailbox, '+');
		int len = p ? p - a->mailbox : (int)strlen(a->mailbox);

		am->freeme = (char *) xmalloc(len + 1);
		strncpy(am->freeme, a->mailbox, len);
		am->freeme[len] = '\0';
		ret = am->freeme;
	    } else {
		ret = NULL;
	    }
	    break;

	case ADDRESS_DETAIL:
	    if (a->mailbox)
	    {	    
		char *p = strchr(a->mailbox, '+');
		ret = (p ? p + 1 : NULL);
	    }
	    else
	    {
		ret = NULL;
	    }
	    break;
	}
	a = a->next;
	am->where = a;
    }
    *marker = am;
    return ret;
}

int free_address(void **data, void **marker)
{
    struct addr_marker *am = (struct addr_marker *) *marker;

    if (*data)
	parseaddr_free((struct address *) *data);
    *data = NULL;
    if (am->freeme) free(am->freeme);
    free(am);
    *marker = NULL;
    return SIEVE_OK;
}

notify_list_t *new_notify_list(void)    
{
    notify_list_t *ret = xmalloc(sizeof(notify_list_t));

    if (ret != NULL) {
	ret->isactive = 0;
	ret->id       = NULL;
	ret->method   = NULL;
	ret->options  = NULL;
	ret->priority = NULL;
	ret->message  = NULL;
	ret->next     = NULL;
    }
    return ret;
}

void free_notify_list(notify_list_t *n)
{
    while (n) {
	notify_list_t *b = n->next;
	free(n->options); /* strings live in bytecode, only free the array */
	free(n);
	n = b;
    }
}

action_list_t *new_action_list(void)
{
    action_list_t *ret = xmalloc(sizeof(action_list_t));

    if (ret != NULL) {
	ret->a = ACTION_NONE;
	ret->param = NULL;
	ret->next = NULL;
	ret->cancel_keep = 0;
    }
    return ret;
}

void free_action_list(action_list_t *a)
{
    while (a) {
	action_list_t *b = a->next;

	if(a->a == ACTION_VACATION) {
	    if(a->u.vac.send.subj) free(a->u.vac.send.subj);
	    if(a->u.vac.send.addr) free(a->u.vac.send.addr);
	    if(a->u.vac.send.fromaddr) free(a->u.vac.send.fromaddr);
	}

	free(a);
	a = b;
    }
}

