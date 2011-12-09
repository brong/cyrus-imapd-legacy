/* append.c -- Routines for appending messages to a mailbox
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
 * $Id: append.c,v 1.122 2010/01/06 17:01:30 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#include <ctype.h>
#include <utime.h>
#include <string.h>
#include <sys/types.h>
#include <syslog.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <sys/poll.h>

#include "acl.h"
#include "assert.h"
#include "imap_err.h"
#include "mailbox.h"
#include "message.h"
#include "append.h"
#include "global.h"
#include "prot.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "mboxlist.h"
#include "seen.h"
#include "retry.h"
#include "quota.h"
#include "util.h"

#include "annotate.h"
#include "message_guid.h"
#include "strarray.h"
#include "conversations.h"

struct stagemsg {
    char fname[1024];

    strarray_t parts; /* buffer of current stage parts */
    struct message_guid guid;
};

static int append_addseen(struct mailbox *mailbox, const char *userid,
			  struct seqset *newseen);
static void append_setseen(struct appendstate *as, struct index_record *record);

#define zero_index(i) { memset(&i, 0, sizeof(struct index_record)); }

/*
 * Check to see if mailbox can be appended to
 *
 * Arguments:
 *	name	   - name of mailbox directory
 *	aclcheck   - user must have these rights on mailbox ACL
 *	quotastorage_check - mailbox must have this much storage quota left
 *		     (-1 means don't care about quota)
 *	quotamessage_check - mailbox must have this much message quota left
 *		     (-1 means don't care about quota)
 *
 */
int append_check(const char *name,
		 struct auth_state *auth_state,
		 long aclcheck,
		 const quota_t quotacheck[QUOTA_NUMRESOURCES])
{
    struct mailbox *mailbox = NULL;
    int myrights;
    int r;

    r = mailbox_open_irl(name, &mailbox);
    if (r) return r;

    myrights = cyrus_acl_myrights(auth_state, mailbox->acl);

    if ((myrights & aclcheck) != aclcheck) {
	r = (myrights & ACL_LOOKUP) ?
	  IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	goto done;
    }

    if (quotacheck)
	r = mailbox_quota_check(mailbox, quotacheck);

done:
    mailbox_close(&mailbox);

    return r;
}

/*
 * Open a mailbox for appending
 *
 * Arguments:
 *	name	   - name of mailbox directory
 *	aclcheck   - user must have these rights on mailbox ACL
 *	quotastorage_check - mailbox must have this much storage quota left
 *		     (-1 means don't care about quota)
 *	quotamessage_check - mailbox must have this much message quota left
 *		     (-1 means don't care about quota)
 *
 * On success, the struct pointed to by 'as' is set up.
 *
 */
int append_setup(struct appendstate *as, const char *name,
		 const char *userid, struct auth_state *auth_state,
		 long aclcheck, const quota_t quotacheck[QUOTA_NUMRESOURCES],
		 struct namespace *namespace, int isadmin)
{
    int r;
    struct mailbox *mailbox = NULL;

    r = mailbox_open_iwl(name, &mailbox);
    if (r) return r;

    return append_setup_mbox(as, mailbox, userid, auth_state,
			     aclcheck, quotacheck, namespace, isadmin);
}

int append_setup_mbox(struct appendstate *as, struct mailbox *mailbox,
		 const char *userid, struct auth_state *auth_state,
		 long aclcheck, const quota_t quotacheck[QUOTA_NUMRESOURCES],
		 struct namespace *namespace, int isadmin)
{
    int r;

    memset(as, 0, sizeof(*as));
    as->mailbox = mailbox;

    as->myrights = cyrus_acl_myrights(auth_state, as->mailbox->acl);

    if ((as->myrights & aclcheck) != aclcheck) {
	r = (as->myrights & ACL_LOOKUP) ?
	  IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	mailbox_close(&as->mailbox);
	return r;
    }

    if (quotacheck) {
	r = mailbox_quota_check(as->mailbox, quotacheck);
	if (r) {
	    mailbox_close(&as->mailbox);
	    return r;
	}
    }

    if (userid) {
	strlcpy(as->userid, userid, sizeof(as->userid));
    } else {
	as->userid[0] = '\0';
    }
    as->namespace = namespace;
    as->auth_state = auth_state;
    as->isadmin = isadmin;

    /* make sure we can open the cache file, so we
     * abort early otherwise */
    r = mailbox_ensure_cache(as->mailbox, 0);
    if (r) {
	mailbox_close(&as->mailbox);
	return r;
    }

    /* initialize seen list creator */
    as->internalseen = mailbox_internal_seen(as->mailbox, as->userid);
    as->seen_seq = seqset_init(0, SEQ_SPARSE);

    /* zero out metadata */
    as->nummsg = 0;
    as->baseuid = as->mailbox->i.last_uid + 1;
    as->s = APPEND_READY;

    annotatemore_begin();

    return 0;
}


/* may return non-zero, indicating that the entire append has failed
 and the mailbox is probably in an inconsistent state. */
int append_commit(struct appendstate *as, 
		  unsigned long *uidvalidity, 
		  unsigned long *start,
		  unsigned long *num,
		  struct mailbox **mailboxptr)
{
    int r = 0;
    
    if (as->s == APPEND_DONE) return 0;

    if (start) *start = as->baseuid;
    if (num) *num = as->nummsg;
    if (uidvalidity) *uidvalidity = as->mailbox->i.uidvalidity;

    if (as->nummsg) {
	/* Calculate new index header information */
	as->mailbox->i.last_appenddate = time(0);

	/* the cache will be dirty even if we hand added the records */
	as->mailbox->cache_dirty = 1;

	/* set seen state */
	if (as->userid[0])
	    append_addseen(as->mailbox, as->userid, as->seen_seq);
    }
    seqset_free(as->seen_seq);
    
    /* We want to commit here to guarantee mailbox on disk vs
     * duplicate DB consistency */
    r = mailbox_commit(as->mailbox);
    if (r) {
	syslog(LOG_ERR, "IOERROR: commiting mailbox append %s: %s",
	       as->mailbox->name, error_message(r));
	append_abort(as);
	return r;
    }

    /* TODO: what could we do in the case of an error? */
    annotatemore_commit();

    if (mailboxptr) {
	*mailboxptr = as->mailbox;
    }
    else {
	mailbox_close(&as->mailbox);
    }

    as->s = APPEND_DONE;

    return 0;
}

/* may return non-zero, indicating an internal error of some sort. */
int append_abort(struct appendstate *as)
{
    int r = 0;

    if (as->s == APPEND_DONE) return 0;
    as->s = APPEND_DONE;

    /* XXX - clean up neatly so we don't crash and burn here... */

    /* close mailbox */
    mailbox_close(&as->mailbox);

    /* Abort any annotation changes */
    annotatemore_abort();

    seqset_free(as->seen_seq);

    return r;
}

/*
 * staging, to allow for single-instance store.  initializes the stage
 * with the file for the given mailboxname and returns the open file
 * so it can double as the spool file
 */
FILE *append_newstage(const char *mailboxname, time_t internaldate,
		      int msgnum, struct stagemsg **stagep)
{
    struct stagemsg *stage;
    char stagedir[MAX_MAILBOX_PATH+1], stagefile[MAX_MAILBOX_PATH+1];
    FILE *f;
    int r;

    assert(mailboxname != NULL);
    assert(stagep != NULL);

    *stagep = NULL;

    stage = xmalloc(sizeof(struct stagemsg));
    strarray_init(&stage->parts);

    snprintf(stage->fname, sizeof(stage->fname), "%d-%d-%d",
	     (int) getpid(), (int) internaldate, msgnum);

    r = mboxlist_findstage(mailboxname, stagedir, sizeof(stagedir));
    if (r) {
	syslog(LOG_ERR, "couldn't find stage directory for mbox: '%s': %s",
	       mailboxname, error_message(r));
	free(stage);
	return NULL;
    }
    strlcpy(stagefile, stagedir, sizeof(stagefile));
    strlcat(stagefile, stage->fname, sizeof(stagefile));

    /* create this file and put it into stage->parts[0] */
    unlink(stagefile);
    f = fopen(stagefile, "w+");
    if (!f) {
	if (mkdir(stagedir, 0755) != 0) {
	    syslog(LOG_ERR, "couldn't create stage directory: %s: %m",
		   stagedir);
	} else {
	    syslog(LOG_NOTICE, "created stage directory %s",
		   stagedir);
	    f = fopen(stagefile, "w+");
	}
    } 
    if (!f) {
	syslog(LOG_ERR, "IOERROR: creating message file %s: %m", 
	       stagefile);
	strarray_fini(&stage->parts);
	free(stage);
	return NULL;
    }

    strarray_append(&stage->parts, stagefile);

    *stagep = stage;
    return f;
}

/*
 * Send the args down a socket.  We use a counted encoding
 * similar in concept to HTTP chunked encoding, with a decimal
 * ASCII encoded length followed by that many bytes of data.
 * A zero length indicates end of message.
 */
static int callout_send_args(int fd, const struct buf *args)
{
    char lenbuf[32];
    int r = 0;

    snprintf(lenbuf, sizeof(lenbuf), "%u\n", args->len);
    r = retry_write(fd, lenbuf, strlen(lenbuf));
    if (r < 0)
	goto out;

    if (args->len) {
	r = retry_write(fd, args->s, args->len);
	if (r < 0)
	    goto out;
	r = retry_write(fd, "0\n", 2);
    }

out:
    return (r < 0 ? IMAP_SYS_ERROR : 0);
}

#define CALLOUT_TIMEOUT_MS	(10*1000)

static int callout_receive_reply(const char *callout,
				 int fd, struct dlist **results)
{
    struct protstream *p = NULL;
    int r;
    int c;
    struct pollfd pfd;

    memset(&pfd, 0, sizeof(pfd));
    pfd.fd = fd;
    pfd.events = POLLIN;

    r = poll(&pfd, 1, CALLOUT_TIMEOUT_MS);
    if (r < 0) {
	syslog(LOG_ERR, "cannot poll() waiting for callout %s: %m",
	       callout);
	r = IMAP_SYS_ERROR;
	goto out;
    }
    if (r == 0) {
	syslog(LOG_ERR, "timed out waiting for callout %s",
	       callout);
	r = IMAP_SYS_ERROR;
	goto out;
    }

    p = prot_new(fd, /*write*/0);
    prot_setisclient(p, 1);

    /* read and parse the reply as a dlist */
    c = dlist_parse(results, /*parsekeys*/0, p);
    r = (c == EOF ? IMAP_SYS_ERROR : 0);

out:
    if (p)
	prot_free(p);
    return r;
}

/*
 * Handle the callout as a service listening on a UNIX domain socket.
 * Send the encoded arguments down the socket; capture the reply and
 * decode it as a dlist.
 */
static int callout_run_socket(const char *callout,
			      const struct buf *args,
			      struct dlist **results)
{
    int sock = -1;
    struct sockaddr_un sun;
    int r;

    sock = socket(PF_UNIX, SOCK_STREAM, 0);
    if (sock < 0) {
	syslog(LOG_ERR, "cannot create socket for callout: %m");
	r = IMAP_SYS_ERROR;
	goto out;
    }

    memset(&sun, 0, sizeof(sun));
    sun.sun_family = AF_UNIX;
    strncpy(sun.sun_path, callout, sizeof(sun.sun_path));
    r = connect(sock, (struct sockaddr *)&sun, sizeof(sun));
    if (r < 0) {
	syslog(LOG_ERR, "cannot connect socket for callout: %m");
	r = IMAP_SYS_ERROR;
	goto out;
    }

    r = callout_send_args(sock, args);
    if (r)
	goto out;

    r = callout_receive_reply(callout, sock, results);

out:
    if (sock >= 0)
	close(sock);
    return r;
}

/*
 * Handle the callout as an executable.  Fork and exec the callout as an
 * executable, with the encoded arguments appearing on stdin and the
 * stdout captured as a dlist.
 */
static int callout_run_executable(const char *callout,
				  const struct buf *args,
				  struct dlist **results)
{
    pid_t pid, reaped;
#define PIPE_READ    0
#define PIPE_WRITE   1
    int inpipe[2] = { -1, -1 };
    int outpipe[2] = { -1, -1 };
    int status;
    int r;

    r = pipe(inpipe);
    if (!r)
	r = pipe(outpipe);
    if (r < 0) {
	syslog(LOG_ERR, "cannot create pipe for callout: %m");
	r = IMAP_SYS_ERROR;
	goto out;
    }

    pid = fork();
    if (pid < 0) {
	syslog(LOG_ERR, "cannot fork for callout: %m");
	r = IMAP_SYS_ERROR;
	goto out;
    }

    if (pid == 0) {
	/* child process */

	close(inpipe[PIPE_WRITE]);
	dup2(inpipe[PIPE_READ], /*FILENO_STDIN*/0);
	close(inpipe[PIPE_READ]);

	close(outpipe[PIPE_READ]);
	dup2(outpipe[PIPE_WRITE], /*FILENO_STDOUT*/1);
	close(outpipe[PIPE_WRITE]);

	execl(callout, callout, (char *)NULL);
	syslog(LOG_ERR, "cannot exec callout %s: %m", callout);
	exit(1);
    }
    /* parent process */
    close(inpipe[PIPE_READ]);
    inpipe[PIPE_READ] = -1;
    close(outpipe[PIPE_WRITE]);
    outpipe[PIPE_WRITE] = -1;

    r = callout_send_args(inpipe[PIPE_WRITE], args);
    if (r)
	goto out;

    r = callout_receive_reply(callout, outpipe[PIPE_READ], results);
    if (r)
	goto out;

    /* reap the child process */
    do {
	reaped = waitpid(pid, &status, 0);
	if (reaped < 0) {
	    if (errno == EINTR)
		continue;
	    if (errno == ESRCH)
		break;
	    if (errno == ECHILD)
		break;
	    syslog(LOG_ERR, "error reaping callout pid %d: %m",
		    (int)pid);
	    r = IMAP_SYS_ERROR;
	    goto out;
	}
    }
    while (reaped != pid);
    r = 0;

out:
    if (inpipe[PIPE_READ] >= 0)
	close(inpipe[PIPE_READ]);
    if (inpipe[PIPE_WRITE] >= 0)
	close(inpipe[PIPE_WRITE]);
    if (outpipe[PIPE_READ] >= 0)
	close(outpipe[PIPE_READ]);
    if (outpipe[PIPE_WRITE] >= 0)
	close(outpipe[PIPE_WRITE]);
    return r;
#undef PIPE_READ
#undef PIPE_WRITE
}

/*
 * Encode the arguments for a callout into @buf.
 */
static void callout_encode_args(struct buf *args,
				const char *fname,
				const struct body *body,
				struct entryattlist *annotations,
				strarray_t *flags)
{
    struct entryattlist *ee;
    int i;

    buf_putc(args, '(');

    buf_printf(args, "FILENAME ");
    message_write_nstring(args, fname);

    buf_printf(args, " ANNOTATIONS (");
    for (ee = annotations ; ee ; ee = ee->next) {
	struct attvaluelist *av;
	message_write_nstring(args, ee->entry);
	buf_putc(args, ' ');
	buf_putc(args, '(');
	for (av = ee->attvalues ; av ; av = av->next) {
	    message_write_nstring(args, av->attrib);
	    buf_putc(args, ' ');
	    message_write_nstring_map(args, av->value.s, av->value.len);
	    if (av->next)
		buf_putc(args, ' ');
	}
	buf_putc(args, ')');
	if (ee->next)
	    buf_putc(args, ' ');
    }
    buf_putc(args, ')');

    buf_printf(args, " FLAGS (");
    for (i = 0 ; i < flags->count ; i++) {
	if (i)
	    buf_putc(args, ' ');
	buf_appendcstr(args, flags->data[i]);
    }
    buf_putc(args, ')');

    buf_appendcstr(args, " BODY ");
    message_write_body(args, body, 2);

    buf_printf(args, " GUID %s", message_guid_encode(&body->guid));
    buf_putc(args, ')');
    buf_cstring(args);
}

/*
 * Parse the reply from the callout.  This designed to be similar to the
 * arguments of the STORE command, except that we can have multiple
 * items one after the other and the whole thing is in a list.
 *
 * Examples:
 * (+FLAGS \Flagged)
 * (+FLAGS (\Flagged \Seen))
 * (-FLAGS \Flagged)
 * (ANNOTATION (/comment (value.shared "Hello World")))
 * (+FLAGS \Flagged ANNOTATION (/comment (value.shared "Hello")))
 *
 * The result is merged into @user_annots, @system_annots, and @flags.
 * User-set annotations are kept separate from system-set annotations
 * for two reasons: a) system-set annotations need to bypass the ACL
 * check to allow them to work during local delivery, and b) failure
 * to set system-set annotations needs to be logged but must not cause
 * the append to fail.
 */
static void callout_decode_results(const char *callout,
				   const struct dlist *results,
			           struct entryattlist **user_annots,
			           struct entryattlist **system_annots,
				   strarray_t *flags)
{
    struct dlist *dd;

    for (dd = results->head ; dd ; dd = dd->next) {
	const char *key = dlist_cstring(dd);
	const char *val;
	dd = dd->next;
	if (!dd)
	    goto error;

	if (!strcasecmp(key, "+FLAGS")) {
	    if (dd->head) {
		struct dlist *dflag;
		for (dflag = dd->head ; dflag ; dflag = dflag->next)
		    if ((val = dlist_cstring(dflag)))
			strarray_add_case(flags, val);
	    }
	    else if ((val = dlist_cstring(dd))) {
		strarray_add_case(flags, val);
	    }
	}
	else if (!strcasecmp(key, "-FLAGS")) {
	    if (dd->head) {
		struct dlist *dflag;
		for (dflag = dd->head ; dflag ; dflag = dflag->next) {
		    if ((val = dlist_cstring(dflag)))
			strarray_remove_all_case(flags, val);
		}
	    }
	    else if ((val = dlist_cstring(dd))) {
		strarray_remove_all_case(flags, val);
	    }
	}
	else if (!strcasecmp(key, "ANNOTATION")) {
	    const char *entry;
	    struct dlist *dx = dd->head;

	    if (!dx)
		goto error;
	    entry = dlist_cstring(dx);
	    if (!entry)
		goto error;

	    for (dx = dx->next ; dx ; dx = dx->next) {
		const char *attrib;
		const char *valmap;
		size_t vallen;
		struct buf value = BUF_INITIALIZER;

		/* must be a list with exactly two elements,
		 * an attrib and a value */
		if (!dx->head || !dx->head->next || dx->head->next->next)
		    goto error;
		attrib = dlist_cstring(dx->head);
		if (!attrib)
		    goto error;
		if (!dlist_tomap(dx->head->next, &valmap, &vallen))
		    goto error;
		buf_init_ro(&value, valmap, vallen);
		clearentryatt(user_annots, entry, attrib);
		setentryatt(system_annots, entry, attrib, &value);
		buf_free(&value);
	    }
	}
	else {
	    goto error;
	}
    }

    return;
error:
    syslog(LOG_WARNING, "Unexpected data in response from callout %s",
	   callout);
}

static int callout_run(const char *fname,
		       const struct body *body,
		       struct entryattlist **user_annots,
		       struct entryattlist **system_annots,
		       strarray_t *flags)
{
    const char *callout;
    struct stat sb;
    struct buf args = BUF_INITIALIZER;
    struct dlist *results = NULL;
    int r;

    callout = config_getstring(IMAPOPT_ANNOTATION_CALLOUT);
    assert(callout);
    assert(flags);

    callout_encode_args(&args, fname, body, *user_annots, flags);

    if (stat(callout, &sb) < 0) {
	syslog(LOG_ERR, "cannot stat annotation_callout %s: %m", callout);
	r = IMAP_IOERROR;
	goto out;
    }
    if (S_ISSOCK(sb.st_mode)) {
	/* UNIX domain socket on which a service is listening */
	r = callout_run_socket(callout, &args, &results);
	if (r)
	    goto out;
    }
    else if (S_ISREG(sb.st_mode) &&
	     (sb.st_mode & (S_IXUSR|S_IXGRP|S_IXOTH))) {
	/* regular file, executable */
	r = callout_run_executable(callout, &args, &results);
	if (r)
	    goto out;
    }
    else {
	syslog(LOG_ERR, "cannot classify annotation_callout %s", callout);
	r = IMAP_IOERROR;
	goto out;
    }

    if (results) {
	/* We have some results, parse them and merge them back into
	 * the annotations and flags we were given */
	callout_decode_results(callout, results,
			       user_annots, system_annots, flags);
    }

out:
    buf_free(&args);
    dlist_free(&results);

    return r;
}

static int append_apply_flags(struct appendstate *as,
			      struct index_record *record,
			      const strarray_t *flags)
{
    int userflag;
    int i, r = 0;

    assert(flags);

    for (i = 0; i < flags->count; i++) {
	const char *flag = strarray_nth(flags, i);
	if (!strcasecmp(flag, "\\seen")) {
	    append_setseen(as, record);
	}
	else if (!strcasecmp(flag, "\\deleted")) {
	    if (as->myrights & ACL_DELETEMSG) {
		record->system_flags |= FLAG_DELETED;
	    }
	}
	else if (!strcasecmp(flag, "\\draft")) {
	    if (as->myrights & ACL_WRITE) {
		record->system_flags |= FLAG_DRAFT;
	    }
	}
	else if (!strcasecmp(flag, "\\flagged")) {
	    if (as->myrights & ACL_WRITE) {
		record->system_flags |= FLAG_FLAGGED;
	    }
	}
	else if (!strcasecmp(flag, "\\answered")) {
	    if (as->myrights & ACL_WRITE) {
		record->system_flags |= FLAG_ANSWERED;
	    }
	}
	else if (as->myrights & ACL_WRITE) {
	    r = mailbox_user_flag(as->mailbox, flag, &userflag, 1);
	    if (r) goto out;
	    record->user_flags[userflag/32] |= 1<<(userflag&31);
	}
    }

out:
    return r;
}

static void append_make_flags(struct appendstate *as,
			      struct index_record *record,
			      strarray_t *flags)
{
    int i;

    assert(flags);

    /* Note: we don't handle the external seen db here, on
     * the grounds that it would add complexity without
     * actually being useful to annotators */
    if (as->internalseen && (record->system_flags & FLAG_SEEN))
	strarray_append(flags, "\\Seen");

    if ((record->system_flags & FLAG_DELETED))
	strarray_append(flags, "\\Deleted");
    if ((record->system_flags & FLAG_DRAFT))
	strarray_append(flags, "\\Draft");
    if ((record->system_flags & FLAG_FLAGGED))
	strarray_append(flags, "\\Flagged");
    if ((record->system_flags & FLAG_ANSWERED))
	strarray_append(flags, "\\Answered");

    for (i = 0 ; i < MAX_USER_FLAGS ; i++) {
	if (as->mailbox->flagname[i] &&
	    (record->user_flags[i/32] & 1<<(i&31)))
	    strarray_append(flags, as->mailbox->flagname[i]);
    }
}

/*
 * staging, to allow for single-instance store.  the complication here
 * is multiple partitions.
 *
 * Note: @user_annots needs to be freed by the caller but
 * may be modified during processing of callout responses.
 */
int append_fromstage(struct appendstate *as, struct body **body,
		     struct stagemsg *stage, time_t internaldate,
		     const strarray_t *flags, int nolink,
		     struct entryattlist *user_annots)
{
    struct mailbox *mailbox = as->mailbox;
    struct index_record record;
    char *fname;
    FILE *destfile;
    int i, r;
    strarray_t *newflags = NULL;
    struct entryattlist *system_annots = NULL;

    /* for staging */
    char stagefile[MAX_MAILBOX_PATH+1];

    assert(stage != NULL && stage->parts.count);

    zero_index(record);

    /* xxx check errors */
    mboxlist_findstage(mailbox->name, stagefile, sizeof(stagefile));
    strlcat(stagefile, stage->fname, sizeof(stagefile));

    for (i = 0 ; i < stage->parts.count ; i++) {
	if (!strcmp(stagefile, stage->parts.data[i])) {
	    /* aha, this is us */
	    break;
	}
    }

    if (i == stage->parts.count) {
	/* ok, create this file, and copy the name of it into stage->parts. */

	/* create the new staging file from the first stage part */
	r = mailbox_copyfile(stage->parts.data[0], stagefile, 0);
	if (r) {
	    /* maybe the directory doesn't exist? */
	    char stagedir[MAX_MAILBOX_PATH+1];

	    /* xxx check errors */
	    mboxlist_findstage(mailbox->name, stagedir, sizeof(stagedir));
	    if (mkdir(stagedir, 0755) != 0) {
		syslog(LOG_ERR, "couldn't create stage directory: %s: %m",
		       stagedir);
	    } else {
		syslog(LOG_NOTICE, "created stage directory %s",
		       stagedir);
		r = mailbox_copyfile(stage->parts.data[0], stagefile, 0);
	    }
	}
	if (r) {
	    /* oh well, we tried */

	    syslog(LOG_ERR, "IOERROR: creating message file %s: %m", 
		   stagefile);
	    unlink(stagefile);
	    return r;
	}

	strarray_append(&stage->parts, stagefile);
    }

    /* 'stagefile' contains the message and is on the same partition
       as the mailbox we're looking at */

    /* Setup */
    record.uid = as->baseuid + as->nummsg;
    record.internaldate = internaldate;

    /* Create message file */
    as->nummsg++;
    fname = mailbox_message_fname(mailbox, record.uid);

    r = mailbox_copyfile(stagefile, fname, nolink);
    destfile = fopen(fname, "r");
    if (!r && destfile) {
	/* ok, we've successfully created the file */
	if (!*body || (as->nummsg - 1))
	    r = message_parse_file(destfile, NULL, NULL, body);
	if (!r) r = message_create_record(&record, *body);
	if (!r && config_getswitch(IMAPOPT_CONVERSATIONS)) {
	    struct conversations_state *cstate = conversations_get_mbox(mailbox->name);
	    if (cstate)
		r = message_update_conversations(cstate, &record, *body,
						 /*isreplica*/0);
	    else
		r = IMAP_CONVERSATIONS_NOT_OPEN;
	}
    }
    if (destfile) {
	/* this will hopefully ensure that the link() actually happened
	   and makes sure that the file actually hits disk */
	fsync(fileno(destfile));
	fclose(destfile);
    }
    if (!r && config_getstring(IMAPOPT_ANNOTATION_CALLOUT)) {
	if (flags)
	    newflags = strarray_dup(flags);
	else
	    newflags = strarray_new();
	r = callout_run(fname, *body, &user_annots, &system_annots, newflags);
	if (r) {
	    syslog(LOG_ERR, "Annotation callout failed, ignoring\n");
	    r = 0;
	}
	flags = newflags;
    }
    if (!r && (user_annots || system_annots)) {
	annotate_state_t *astate = annotate_state_new();
	annotate_state_set_message(astate, as->mailbox, record.uid);
	if (user_annots) {
	    annotate_state_set_auth(astate, as->namespace, as->isadmin,
				    as->userid, as->auth_state);
	    r = annotate_state_store(astate, user_annots);
	}
	if (!r && system_annots) {
	    /* pretend to be admin to avoid ACL checks */
	    annotate_state_set_auth(astate, as->namespace, /*isadmin*/1,
				    as->userid, as->auth_state);
	    r = annotate_state_store(astate, system_annots);
	    if (r) {
		syslog(LOG_ERR, "Setting annnotations from annotator "
				"callout failed (%s), ignoring\n",
				error_message(r));
		r = 0;
	    }
	}
	annotate_state_free(&astate);
    }
    if (r)
	goto out;

    /* Handle flags the user wants to set in the message */
    if (flags) {
	r = append_apply_flags(as, &record, flags);
	if (r) goto out;
    }
    /* Write out index file entry */
    r = mailbox_append_index_record(mailbox, &record);

out:
    if (newflags)
	strarray_free(newflags);
    freeentryatts(system_annots);
    if (r) {
	append_abort(as);
	return r;
    }

    return 0;
}

int append_removestage(struct stagemsg *stage)
{
    char *p;

    if (stage == NULL) return 0;

    while ((p = strarray_pop(&stage->parts))) {
	/* unlink the staging file */
	if (unlink(p) != 0) {
	    syslog(LOG_ERR, "IOERROR: error unlinking file %s: %m", p);
	}
	free(p);
    }

    strarray_fini(&stage->parts);
    free(stage);
    return 0;
}

/*
 * Append to 'mailbox' from the prot stream 'messagefile'.
 * 'mailbox' must have been opened with append_setup().
 * 'size' is the expected size of the message.
 * 'internaldate' specifies the internaldate for the new message.
 * 'flags' contains the names of the 'nflags' flags that the
 * user wants to set in the message.  If the '\Seen' flag is
 * in 'flags', then the 'userid' passed to append_setup controls whose
 * \Seen flag gets set.
 * 
 * The message is not committed to the mailbox (nor is the mailbox
 * unlocked) until append_commit() is called.  multiple
 * append_onefromstream()s can be aborted by calling append_abort().
 */
int append_fromstream(struct appendstate *as, struct body **body,
		      struct protstream *messagefile,
		      unsigned long size,
		      time_t internaldate,
		      const strarray_t *flags)
{
    struct mailbox *mailbox = as->mailbox;
    struct index_record record;
    char *fname;
    FILE *destfile;
    int r;

    assert(size != 0);

    zero_index(record);
    /* Setup */
    record.uid = as->baseuid + as->nummsg;
    record.internaldate = internaldate;

    /* Create message file */
    fname = mailbox_message_fname(mailbox, record.uid);
    as->nummsg++;

    unlink(fname);
    destfile = fopen(fname, "w+");
    if (!destfile) {
	syslog(LOG_ERR, "IOERROR: creating message file %s: %m", fname);
	r = IMAP_IOERROR;
	goto out;
    }

    /* Copy and parse message */
    r = message_copy_strict(messagefile, destfile, size, 0);
    if (!r) {
	if (!*body || (as->nummsg - 1))
	    r = message_parse_file(destfile, NULL, NULL, body);
	if (!r) r = message_create_record(&record, *body);
    }
    fclose(destfile);
    if (r) goto out;

    /* Handle flags the user wants to set in the message */
    if (flags) {
	r = append_apply_flags(as, &record, flags);
	if (r) goto out;
    }

    /* Write out index file entry; if we abort later, it's not
       important */
    r = mailbox_append_index_record(mailbox, &record);

out:
    if (r) {
	append_abort(as);
	return r;
    }
    
    return 0;
}

static int load_annot_cb(const char *mailbox __attribute__((unused)),
			 uint32_t uid __attribute__((unused)),
			 const char *entry, const char *userid,
			 const struct buf *value, void *rock)
{
    struct entryattlist **eal = (struct entryattlist **)rock;
    const char *attrib = (userid[0] ? "value.priv" : "value.shared");
    setentryatt(eal, entry, attrib, value);
    return 0;
}

int append_run_annotator(struct appendstate *as,
			 struct index_record *record)
{
    char *fname;
    struct entryattlist *user_annots = NULL;
    struct entryattlist *system_annots = NULL;
    strarray_t flags = STRARRAY_INITIALIZER;
    annotate_state_t *astate = NULL;
    struct body *body = NULL;
    int r;

    if (!config_getstring(IMAPOPT_ANNOTATION_CALLOUT))
	return 0;

    append_make_flags(as, record, &flags);

    r = annotatemore_findall(as->mailbox->name, record->uid, "*",
			     load_annot_cb, &user_annots);
    if (r) goto out;

    fname = mailbox_message_fname(as->mailbox, record->uid);
    if (!fname) goto out;

    r = message_parse2(fname, record, &body);
    if (r) goto out;

    r = callout_run(fname, body, &user_annots, &system_annots, &flags);
    if (r) goto out;

    record->system_flags &= FLAG_SEEN;
    memset(&record->user_flags, 0, sizeof(record->user_flags));
    r = append_apply_flags(as, record, &flags);
    if (r) goto out;

    astate = annotate_state_new();
    annotate_state_set_message(astate, as->mailbox, record->uid);
    if (user_annots) {
	annotate_state_set_auth(astate, as->namespace, as->isadmin,
				as->userid, as->auth_state);
	r = annotate_state_store(astate, user_annots);
	if (r) goto out;
    }
    if (system_annots) {
	/* pretend to be admin to avoid ACL checks */
	annotate_state_set_auth(astate, as->namespace, /*isadmin*/1,
				as->userid, as->auth_state);
	r = annotate_state_store(astate, system_annots);
	if (r) {
	    syslog(LOG_ERR, "Setting annnotations from annotator "
			    "callout failed (%s)",
			    error_message(r));
	    goto out;
	}
    }

out:
    annotate_state_free(&astate);
    freeentryatts(user_annots);
    freeentryatts(system_annots);
    strarray_fini(&flags);
    if (body) {
	message_free_body(body);
	free(body);
    }
    return r;
}

/*
 * Append to 'as->mailbox' the 'nummsg' messages from the
 * mailbox 'mailbox' listed in the array pointed to by 'copymsg'.
 * 'as' must have been opened with append_setup().  If the '\Seen'
 * flag is to be set anywhere then 'userid' passed to append_setup()
 * contains the name of the user whose \Seen flag gets set.  
 */
int append_copy(struct mailbox *mailbox, 
		struct appendstate *as,
		int nummsg, 
		struct copymsg *copymsg,
		int nolink)
{
    int msg;
    struct index_record record;
    char *srcfname, *destfname = NULL;
    int r = 0;
    int flag, userflag;
    
    if (!nummsg) {
	append_abort(as);
	return 0;
    }

    /* Copy/link all files and cache info */
    for (msg = 0; msg < nummsg; msg++) {
	zero_index(record);
	record.uid = as->mailbox->i.last_uid + 1;
	as->nummsg++;

	/* copy the parts that are the same regardless */
	record.internaldate = copymsg[msg].internaldate;
	message_guid_copy(&record.guid, &copymsg[msg].guid);

	/* Handle any flags that need to be copied */
	if (as->myrights & ACL_WRITE) {
	    /* deleted is special, different ACL */
	    record.system_flags =
	      copymsg[msg].system_flags & ~FLAG_DELETED;

	    for (flag = 0; copymsg[msg].flag[flag]; flag++) {
		r = mailbox_user_flag(as->mailbox, 
				      copymsg[msg].flag[flag], &userflag, 1);
		if (r) goto out;
		record.user_flags[userflag/32] |= 1<<(userflag&31);
	    }
	}
	/* deleted flag copy as well */
	if (as->myrights & ACL_DELETEMSG) {
	    record.system_flags |= copymsg[msg].system_flags & FLAG_DELETED;
	}

	/* should this message be marked \Seen? */
	if (copymsg[msg].seen) {
	    append_setseen(as, &record);
	}

	/* Link/copy message file */
	free(destfname);
	srcfname = xstrdup(mailbox_message_fname(mailbox, copymsg[msg].uid));
	destfname = xstrdup(mailbox_message_fname(as->mailbox, record.uid));
	r = mailbox_copyfile(srcfname, destfname, nolink);
	free(srcfname);
	if (r) goto out;

	/* Write out cache info, copy other info */
	record.sentdate = copymsg[msg].sentdate;
	record.size = copymsg[msg].size;
	record.header_size = copymsg[msg].header_size;
	record.gmtime = copymsg[msg].gmtime;
	record.content_lines = copymsg[msg].content_lines;
	record.cache_version = copymsg[msg].cache_version;
	record.cache_crc = copymsg[msg].cache_crc;
	record.cid = copymsg[msg].cid;
	record.crec = copymsg[msg].crec;

	if (record.cid == NULLCONVERSATION &&
	    config_getswitch(IMAPOPT_CONVERSATIONS)) {
	    struct conversations_state *cstate = conversations_get_mbox(as->mailbox->name);
	    if (cstate)
		r = message_update_conversations(cstate, &record,
						 NULL, /*isreplica*/0);
	    else
		r = IMAP_CONVERSATIONS_NOT_OPEN;
	    if (r) goto out;
	}

	/* Write out index file entry */
	r = mailbox_append_index_record(as->mailbox, &record);
	if (r) goto out;

	r = annotate_msg_copy(mailbox, copymsg[msg].uid,
			      as->mailbox, record.uid,
			      as->userid);
	if (r) goto out;
    }

out:
    free(destfname);
    if (r) append_abort(as);

    return r;
}

void append_setseen(struct appendstate *as, struct index_record *record)
{
    if (as->internalseen)
	record->system_flags |= FLAG_SEEN;
    else
	seqset_add(as->seen_seq, record->uid, 1);
}

/*
 * Set the \Seen flag for 'userid' in 'mailbox' for the messages from
 * 'msgrange'.  the lowest msgrange must be larger than any previously
 * seen message.
 */
static int append_addseen(struct mailbox *mailbox,
			  const char *userid,
			  struct seqset *newseen)
{
    int r;
    struct seen *seendb = NULL;
    struct seendata sd;
    struct seqset *oldseen;

    if (!newseen->len)
	return 0;

    r = seen_open(userid, SEEN_CREATE, &seendb);
    if (r) goto done;

    r = seen_lockread(seendb, mailbox->uniqueid, &sd);
    if (r) goto done;

    /* parse the old sequence */
    oldseen = seqset_parse(sd.seenuids, NULL, mailbox->i.last_uid);
    free(sd.seenuids);

    /* add the extra items */
    seqset_join(oldseen, newseen);
    sd.seenuids = seqset_cstring(oldseen);
    seqset_free(oldseen);

    /* and write it out */
    sd.lastchange = time(NULL);
    r = seen_write(seendb, mailbox->uniqueid, &sd);
    free(sd.seenuids);

 done:
    seen_close(&seendb);
    return r;
}
