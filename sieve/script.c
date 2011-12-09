/* script.c -- sieve script functions
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
 * $Id: script.c,v 1.71.2.1 2010/02/12 03:40:51 brong Exp $
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <syslog.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <assert.h>

#include "charset.h"
#include "hash.h"
#include "xmalloc.h"

#include "sieve_interface.h"
#include "interp.h"
#include "script.h"
#include "tree.h"
#include "map.h"
#include "sieve.h"
#include "util.h"
#include "message.h"
#include "bytecode.h"
#include "libconfig.h"

#define ERR_BUF_SIZE 1024

/* does this interpretor support this requirement? */
int script_require(sieve_script_t *s, char *req)
{
    unsigned long config_sieve_extensions =
	config_getbitfield(IMAPOPT_SIEVE_EXTENSIONS);

    if (!strcmp("fileinto", req)) {
	if (s->interp.fileinto &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_FILEINTO)) {
	    s->support.fileinto = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("reject", req)) {
	if (s->interp.reject &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_REJECT)) {
	    s->support.reject = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("envelope", req)) {
	if (s->interp.getenvelope &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_ENVELOPE)) {
	    s->support.envelope = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("body", req)) {
	if (s->interp.getbody &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_BODY)) {
	    s->support.body = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("vacation", req)) {
	if (s->interp.vacation &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_VACATION)) {
	    s->support.vacation = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("imapflags", req)) {
	if (s->interp.markflags->count &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_IMAPFLAGS)) {
	    s->support.imapflags = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("notify",req)) {
	if (s->interp.notify &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_NOTIFY)) {
	    s->support.notify = 1;
	    return 1;
	} else {
	    return 0;
	}
    } else if (!strcmp("include", req)) {
	if (s->interp.getinclude &&
	    (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_INCLUDE)) {
	    s->support.include = 1;
	    return 1;
	} else {
	    return 0;
	}
#ifdef ENABLE_REGEX
    } else if (!strcmp("regex", req) &&
	       (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_REGEX)) {
	s->support.regex = 1;
	return 1;
#endif
    } else if (!strcmp("subaddress", req) &&
	       (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_SUBADDRESS)) {
	s->support.subaddress = 1;
	return 1;
    } else if (!strcmp("relational", req) &&
	       (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_RELATIONAL)) {
	s->support.relational = 1;
	return 1;
    } else if (!strcmp("comparator-i;octet", req)) {
	return 1;
    } else if (!strcmp("comparator-i;ascii-casemap", req)) {
	return 1;
    } else if (!strcmp("comparator-i;ascii-numeric", req)) {
	s->support.i_ascii_numeric = 1;
	return 1;
    } else if (!strcmp("copy", req) &&
	       (config_sieve_extensions & IMAP_ENUM_SIEVE_EXTENSIONS_COPY)) {
	s->support.copy = 1;
	return 1;
    }
    return 0;
}

/* given an interpretor and a script, produce an executable script */
int sieve_script_parse(sieve_interp_t *interp, FILE *script,
		       void *script_context, sieve_script_t **ret)
{
    sieve_script_t *s;
    int res = SIEVE_OK;
    extern int yylineno;

    res = interp_verify(interp);
    if (res != SIEVE_OK) {
	return res;
    }

    s = (sieve_script_t *) xmalloc(sizeof(sieve_script_t));
    s->interp = *interp;
    s->script_context = script_context;
    /* clear all support bits */
    memset(&s->support, 0, sizeof(struct sieve_support));

    s->err = 0;

    yylineno = 1;		/* reset line number */
    s->cmds = sieve_parse(s, script);
    if (s->err > 0) {
	if (s->cmds) {
	    free_tree(s->cmds);
	}
	s->cmds = NULL;
	res = SIEVE_PARSE_ERROR;
    }

    *ret = s;
    return res;
}

int sieve_script_free(sieve_script_t **s)
{
    if (*s) {
	if ((*s)->cmds) {
	    free_tree((*s)->cmds);
	}
	free(*s);
    }

    return SIEVE_OK;
}
 
static void add_header(sieve_interp_t *i, int isenv, char *header, 
		       void *message_context, struct buf *out)
{
    const char **h;
    char *decoded_header;
    /* get header value */
    if (isenv)
	i->getenvelope(message_context, header, &h);	
    else
	i->getheader(message_context, header, &h);	

    if (!h || !h[0])
	return;

    decoded_header = charset_parse_mimeheader(h[0]);
    buf_appendcstr(out, decoded_header);
    free(decoded_header);
}

static int build_notify_message(sieve_interp_t *i,
				const char *msg, 
				void *message_context,
				struct buf *out)
{
    const char *c;
    size_t n;

    if (msg == NULL) return SIEVE_OK;

    /* construct the message */
    c = msg;
    while (*c) {
	/* expand variables */
	if (!strncasecmp(c, "$from$", 6)) {
	    add_header(i, 0 ,"From", message_context, out);
	    c += 6;
	}
	else if (!strncasecmp(c, "$env-from$", 10)) {
	    add_header(i, 1, "From", message_context, out);
	    c += 10;
	}
	else if (!strncasecmp(c, "$subject$", 9)) {
	    add_header(i, 0, "Subject", message_context, out);
	    c += 9;
	}
	else if (i->getbody &&
		 !strncasecmp(c, "$text", 5) && (c[5] == '[' || c[5] == '$')) {
	    const char *content_types[] = { "text", NULL };
	    sieve_bodypart_t **parts = NULL;

	    c += 5;
	    n = 0;
	    if (*c++ == '[') {
		while (*c != ']') n = n * 10 + (*c++ - '0');
		c += 2; /* skip ]$ */
	    }

	    i->getbody(message_context, content_types, &parts);

	    /* we only use the first text part */
	    if (parts && parts[0] && parts[0]->decoded_body) {
		size_t size = strlen(parts[0]->decoded_body);
		if (n && size > n) size = n;
		buf_appendmap(out, parts[0]->decoded_body, size);
	    }

	    /* free the results */
	    if (parts) {
		sieve_bodypart_t **p;

		for (p = parts; *p; p++) free(*p);
		free(parts);
	    }
	}
	else {
	    /* find length of plaintext up to next potential variable */
	    n = strcspn(c+1, "$") + 1; /* skip opening '$' */
	    buf_appendmap(out, c, n);
	    c += n;
	}
    }

    buf_cstring(out);
    return SIEVE_OK;
}

static int sieve_addflag(strarray_t *imapflags, const char *flag)
{
    int n;
    /* search for flag already in list */
    for (n = 0; n < imapflags->count; n++) {
	if (!strcmp(imapflags->data[n], flag))
	    break;
    }

    /* add flag to list, iff not in list */
    if (n == imapflags->count)
	strarray_append(imapflags, flag);

    return SIEVE_OK;
}

static int sieve_removeflag(strarray_t *imapflags, const char *flag)
{
    int n;
    /* search for flag already in list */
    for (n = 0; n < imapflags->count; n++) {
      if (!strcmp(imapflags->data[n], flag))
	break;
    }

     /* remove flag from list, iff in list */
    if (n < imapflags->count)
	free(strarray_remove(imapflags, n));

    return SIEVE_OK;
}

static int send_notify_callback(sieve_interp_t *interp,
				void *message_context, 
				void * script_context, notify_list_t *notify, 
				char *actions_string __attribute__((unused)),
				const char **errmsg)
{
    sieve_notify_context_t nc;
    struct buf out = BUF_INITIALIZER;
    int ret;

    assert(notify->isactive);

    if (!notify->method || !notify->options ||
	!notify->priority || !notify->message) {
	return SIEVE_RUN_ERROR;
    }

    nc.method = notify->method;
    nc.options = notify->options ? notify->options : NULL;
    nc.priority = notify->priority;

    if(nc.options && !strcmp(nc.method,"mailto"))
      if(!strcmp("$env-from$",*nc.options))
        interp->getenvelope(message_context, "From", &nc.options);

    build_notify_message(interp, notify->message, message_context,
			 &out);
    buf_appendcstr(&out, "\n\n");
    /* buf_appendcstr(&out, actions_string); */

    nc.message = buf_cstring(&out);

    ret = interp->notify(&nc,
			 interp->interp_context,
			 script_context,
			 message_context,
			 errmsg);    

    buf_free(&out);

    return ret;
}

static char *action_to_string(action_t action)
{
    switch(action)
	{
	case ACTION_REJECT: return "Reject";
	case ACTION_FILEINTO: return "Fileinto";
	case ACTION_KEEP: return "Keep";
	case ACTION_REDIRECT: return "Redirect";
	case ACTION_DISCARD: return "Discard";
	case ACTION_VACATION: return "Vacation";
	case ACTION_SETFLAG: return "Setflag";
	case ACTION_ADDFLAG: return "Addflag";
	case ACTION_REMOVEFLAG: return "Removeflag";
	case ACTION_MARK: return "Mark";
	case ACTION_UNMARK: return "Unmark";
	case ACTION_NOTIFY: return "Notify";
	case ACTION_DENOTIFY: return "Denotify";
	default: return "Unknown";
	}

    /* never reached */
}

static char *sieve_errstr(int code)
{
    switch (code)
	{
	case SIEVE_FAIL: return "Generic Error";
	case SIEVE_NOT_FINALIZED: return "Sieve not finalized";
	case SIEVE_PARSE_ERROR: return "Parse error";
	case SIEVE_RUN_ERROR: return "Run error";
	case SIEVE_INTERNAL_ERROR: return "Internal Error";
	case SIEVE_NOMEM: return "No memory";
	default: return "Unknown error";
	}

    /* never reached */
}


/******************************bytecode functions*****************************
 *****************************************************************************/

/* Load a compiled script */
int sieve_script_load(const char *fname, sieve_execute_t **ret) 
{
    struct stat sbuf;
    sieve_execute_t *ex;
    sieve_bytecode_t *bc;
    int dofree = 0;
   
    if (!fname || !ret) return SIEVE_FAIL;
    
    if (stat(fname, &sbuf) == -1) {
	syslog(LOG_DEBUG, "IOERROR: fstating sieve script %s: %m", fname);
	return SIEVE_FAIL;
    }

    if (!*ret) {
	/* new sieve_bytecode_t */
	ex = (sieve_execute_t *) xzmalloc(sizeof(sieve_execute_t));
	dofree = 1;
    } else {
	/* existing sieve_execute_t (INCLUDE) */
	ex = *ret;
    }

    /* see if we already have this script loaded */
    bc = ex->bc_list;
    while (bc) {
	if (sbuf.st_ino == bc->inode) break;
	bc = bc->next;
    }

    if (!bc) {
	int fd;

	/* new script -- load it */
	fd = open(fname, O_RDONLY);
	if (fd == -1) {
	    syslog(LOG_ERR, "IOERROR: can not open sieve script %s: %m", fname);
	    if (dofree) free(ex);
	    return SIEVE_FAIL;
	}
	if (fstat(fd, &sbuf) == -1) {
	    syslog(LOG_ERR, "IOERROR: fstating sieve script %s: %m", fname);
	    close(fd);
	    if (dofree) free(ex);
	    return SIEVE_FAIL;
	}

	bc = (sieve_bytecode_t *) xzmalloc(sizeof(sieve_bytecode_t));

	bc->fd = fd;
	bc->inode = sbuf.st_ino;

	map_refresh(fd, 1, &bc->data, &bc->len, sbuf.st_size,
		    fname, "sievescript");

	/* add buffer to list */
	bc->next = ex->bc_list;
	ex->bc_list = bc;
    }

    ex->bc_cur = bc;
    *ret = ex;
    return SIEVE_OK;
}



int sieve_script_unload(sieve_execute_t **s) 
{
    if(s && *s) {
	sieve_bytecode_t *bc = (*s)->bc_list;
	sieve_bytecode_t *nextbc;

	/* free each bytecode buffer in the linked list */
	while (bc) {
	    map_free(&(bc->data), &(bc->len));
	    close(bc->fd);
	    nextbc = bc->next;
	    free(bc);
	    bc = nextbc;
	}
	free(*s);
	*s = NULL;
    } 
    /*i added this else, i'm not sure why, but this function always returned SIEVE_FAIL*/
    else
      return SIEVE_FAIL;
    return SIEVE_OK;
}


#define ACTIONS_STRING_LEN 4096

static int do_sieve_error(int ret,
			  sieve_interp_t *interp,
			  void *script_context,
			  void *message_context,
			  strarray_t *imapflags,
			  action_list_t *actions,
			  notify_list_t *notify_list,
			  /* notify_action_t *notify_action,*/
			  int lastaction,
			  int implicit_keep,
			  char *actions_string,
			  const char *errmsg
			  ) 
{
   if (ret != SIEVE_OK) {
	if (lastaction == -1) /* we never executed an action */
	    snprintf(actions_string+strlen(actions_string),
		     ACTIONS_STRING_LEN-strlen(actions_string),
		     "script execution failed: %s\n",
		     errmsg ? errmsg : sieve_errstr(ret));
	else
	    snprintf(actions_string+strlen(actions_string),
		     ACTIONS_STRING_LEN-strlen(actions_string),
		     "%s action failed: %s\n",
		     action_to_string(lastaction),
		     errmsg ? errmsg : sieve_errstr(ret));
    }
 
   
    /* Process notify actions */
    if (interp->notify && notify_list) 
      {
	notify_list_t *n = notify_list;
	int notify_ret = SIEVE_OK;
	
	while (n != NULL) 
	  {
	    if (n->isactive) 
	      {
	      lastaction = ACTION_NOTIFY;
	       notify_ret = send_notify_callback(interp,
						 message_context, 
						 script_context,n,
						 actions_string, &errmsg);
	      ret |= notify_ret;
	      }
	    n = n->next;
	  }
	
	if (notify_list) free_notify_list(notify_list);
	notify_list = NULL;	/* don't try any notifications again */
	
	
	if (notify_ret != SIEVE_OK) 
	  return do_sieve_error(ret, interp,
				script_context, message_context,
				imapflags, actions, notify_list, lastaction,
				implicit_keep, actions_string, errmsg);
      
      }
    
    if ((ret != SIEVE_OK) && interp->execute_err) {
	char buf[ERR_BUF_SIZE];
	if (lastaction == -1) /* we never executed an action */
	    snprintf(buf, ERR_BUF_SIZE,
		     "%s", errmsg ? errmsg : sieve_errstr(ret));
	else {
	    if (interp->lastitem) {
		snprintf(buf, ERR_BUF_SIZE, "%s (%s): %s", 
			 action_to_string(lastaction), interp->lastitem,
			 errmsg ? errmsg : sieve_errstr(ret));
	    }
	    else {
		snprintf(buf, ERR_BUF_SIZE, "%s: %s",
			 action_to_string(lastaction),
			 errmsg ? errmsg : sieve_errstr(ret));
	    }
	}
 
	ret |= interp->execute_err(buf, interp->interp_context,
				   script_context, message_context);
    }

    if (implicit_keep) {
	sieve_keep_context_t keep_context;
	int keep_ret;
	keep_context.imapflags = imapflags;
 
	lastaction = ACTION_KEEP;
	keep_ret = interp->keep(&keep_context, interp->interp_context,
				script_context, message_context, &errmsg);
	ret |= keep_ret;
        if (keep_ret == SIEVE_OK)
            snprintf(actions_string+strlen(actions_string),
		     ACTIONS_STRING_LEN-strlen(actions_string),
		     "Kept\n");
	else {
	    implicit_keep = 0;	/* don't try an implicit keep again */
	    return do_sieve_error(ret, interp,
				  script_context, message_context,
				  imapflags, actions, notify_list, lastaction,
				  implicit_keep, actions_string, errmsg);
	}
    }

    if (actions)
	free_action_list(actions);

    return ret;
}


static int do_action_list(sieve_interp_t *interp,
			  void *script_context,
			  void *message_context,
			  strarray_t *imapflags,
			  action_list_t *actions,
			  notify_list_t *notify_list,
			  /* notify_action_t *notify_action,*/
			  char *actions_string,
			  const char *errmsg) 
{
    action_list_t *a;
    action_t lastaction = -1;
    int ret = 0;
    int implicit_keep = 1;
    
    strcpy(actions_string,"Action(s) taken:\n");
  
    /* now perform actions attached to m */
    a = actions;
    while (a != NULL) {
	lastaction = a->a;
	errmsg = NULL;
	implicit_keep = implicit_keep && !a->cancel_keep;
	switch (a->a) {
	case ACTION_REJECT:
	    if (!interp->reject)
		return SIEVE_INTERNAL_ERROR;
	    ret = interp->reject(&a->u.rej,
				 interp->interp_context,
				 script_context,
				 message_context,
				 &errmsg);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.rej.msg);
	    
	    if (ret == SIEVE_OK)
		snprintf(actions_string+strlen(actions_string),
			 ACTIONS_STRING_LEN-strlen(actions_string), 
			 "Rejected with: %s\n", a->u.rej.msg);

	    break;
	case ACTION_FILEINTO:
	    if (!interp->fileinto)
		return SIEVE_INTERNAL_ERROR;
	    ret = interp->fileinto(&a->u.fil,
				   interp->interp_context,
				   script_context,
				   message_context,
				   &errmsg);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.fil.mailbox);

	    if (ret == SIEVE_OK)
		snprintf(actions_string+strlen(actions_string),
			 ACTIONS_STRING_LEN-strlen(actions_string),
			 "Filed into: %s\n",a->u.fil.mailbox);
	    break;
	case ACTION_KEEP:
	    if (!interp->keep)
		return SIEVE_INTERNAL_ERROR;
	    ret = interp->keep(&a->u.keep,
			       interp->interp_context,
			       script_context,
			       message_context,
			       &errmsg);
	    free(interp->lastitem);
	    interp->lastitem = NULL;
	    if (ret == SIEVE_OK)
		snprintf(actions_string+strlen(actions_string),
			 ACTIONS_STRING_LEN-strlen(actions_string),
			 "Kept\n");
	    break;
	case ACTION_REDIRECT:
	    if (!interp->redirect)
		return SIEVE_INTERNAL_ERROR;
	    ret = interp->redirect(&a->u.red,
				   interp->interp_context,
				   script_context,
				   message_context,
				   &errmsg);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.red.addr);
	    if (ret == SIEVE_OK)
		snprintf(actions_string+strlen(actions_string),
			 ACTIONS_STRING_LEN-strlen(actions_string),
			 "Redirected to %s\n", a->u.red.addr);
	    break;
	case ACTION_DISCARD:
	    if (interp->discard) /* discard is optional */
		ret = interp->discard(NULL, interp->interp_context,
				      script_context,
				      message_context,
				      &errmsg);
	    free(interp->lastitem);
	    interp->lastitem = NULL;
	    if (ret == SIEVE_OK)
		snprintf(actions_string+strlen(actions_string),
			 ACTIONS_STRING_LEN-strlen(actions_string),
			 "Discarded\n");
	    break;

	case ACTION_VACATION:
	    {
		if (!interp->vacation)
		    return SIEVE_INTERNAL_ERROR;

		/* first, let's figure out if we should respond to this */
		ret = interp->vacation->autorespond(&a->u.vac.autoresp,
						    interp->interp_context,
						    script_context,
						    message_context,
						    &errmsg);
		free(interp->lastitem);
		interp->lastitem = NULL;

		if (ret == SIEVE_OK) {
		    /* send the response */
		    ret = interp->vacation->send_response(&a->u.vac.send,
							  interp->interp_context,
							  script_context, 
							  message_context,
							  &errmsg);

		    if (ret == SIEVE_OK)
			snprintf(actions_string+strlen(actions_string),
				 ACTIONS_STRING_LEN-strlen(actions_string),
				 "Sent vacation reply\n");

		} else if (ret == SIEVE_DONE) {
		    snprintf(actions_string+strlen(actions_string),
			     ACTIONS_STRING_LEN-strlen(actions_string),
			     "Vacation reply suppressed\n");

		    ret = SIEVE_OK;
		}
	    
		break;
	    }

 
	case ACTION_SETFLAG:
	    strarray_fini(imapflags);
	    ret = sieve_addflag(imapflags, a->u.fla.flag);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.fla.flag);
	    break;
	case ACTION_ADDFLAG:
	    ret = sieve_addflag(imapflags, a->u.fla.flag);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.fla.flag);
	    break;
	case ACTION_REMOVEFLAG:
	    ret = sieve_removeflag(imapflags, a->u.fla.flag);
	    free(interp->lastitem);
	    interp->lastitem = xstrdup(a->u.fla.flag);
	    break;
	case ACTION_MARK:
	    {
		int n = interp->markflags->count;

		ret = SIEVE_OK;
		while (n && ret == SIEVE_OK) {
		    ret = sieve_addflag(imapflags,
					interp->markflags->data[--n]);
		}
		free(interp->lastitem);
		interp->lastitem = NULL;
		break;
	    }
	case ACTION_UNMARK:
	  {
	   
		int n = interp->markflags->count;
		ret = SIEVE_OK;
		while (n && ret == SIEVE_OK) {
		    ret = sieve_removeflag(imapflags,
					   interp->markflags->data[--n]);
		}
		free(interp->lastitem);
		interp->lastitem = NULL;
		break;
	    }

	case ACTION_NONE:
	    break;

	default:
	    ret = SIEVE_INTERNAL_ERROR;
	    break;
	}
	a = a->next;

	if (ret != SIEVE_OK) {
	    /* uh oh! better bail! */
	    break;
	}
    }

    return do_sieve_error(ret, interp,
			  script_context, message_context, 
			  imapflags, actions, notify_list, lastaction, 
			  implicit_keep, actions_string, errmsg);
}


/* execute some bytecode */
int sieve_eval_bc(sieve_execute_t *exe, int is_incl, sieve_interp_t *i,
		  void *sc, void *m,
		  const strarray_t * , action_list_t *actions,
		  notify_list_t *notify_list, const char **errmsg);

int sieve_execute_bytecode(sieve_execute_t *exe, sieve_interp_t *interp,
			   void *script_context, void *message_context) 
{
    action_list_t *actions = NULL;
    notify_list_t *notify_list = NULL;
    /*   notify_action_t *notify_action;*/
    action_t lastaction = -1;
    int ret;
    char actions_string[ACTIONS_STRING_LEN] = "";
    const char *errmsg = NULL;
    strarray_t imapflags = STRARRAY_INITIALIZER;
    
    if (!interp) return SIEVE_FAIL;

    if (interp->notify) {
	notify_list = new_notify_list();
	if (notify_list == NULL) {
	    return do_sieve_error(SIEVE_NOMEM, interp,
				  script_context, message_context, &imapflags,
				  actions, notify_list, lastaction, 0,
				  actions_string, errmsg);
	}
    }

    actions = new_action_list();
    if (actions == NULL) {
	ret = do_sieve_error(SIEVE_NOMEM, interp,
			     script_context, message_context, &imapflags,
			     actions, notify_list, lastaction, 0,
			     actions_string, errmsg);
    }
    else {
	ret = sieve_eval_bc(exe, 0, interp,
			    script_context, message_context,
			    &imapflags, actions, notify_list, &errmsg);

	if (ret < 0) {
	    ret = do_sieve_error(SIEVE_RUN_ERROR, interp,
				 script_context, message_context, &imapflags,
				 actions, notify_list, lastaction, 0,
				 actions_string, errmsg);
	}
	else {
	    ret = do_action_list(interp,
				 script_context, message_context, 
				 &imapflags, actions, notify_list,
				 actions_string, errmsg);
	}
    }

    strarray_fini(&imapflags);

    return ret;
}
