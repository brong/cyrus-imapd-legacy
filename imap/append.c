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

#include "message_guid.h"
#include "strarray.h"
#include "conversations.h"
#include "annotate.h"

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
 *	quotacheck - mailbox must have this much quota left
 *		     (-1 means don't care about quota)
 *
 */
int append_check(const char *name,
		 struct auth_state *auth_state,
		 long aclcheck, quota_t quotacheck)
{
    struct mailbox *mailbox = NULL;
    int myrights;
    int r;
    struct quota q;

    r = mailbox_open_irl(name, &mailbox);
    if (r) return r;

    myrights = cyrus_acl_myrights(auth_state, mailbox->acl);

    if ((myrights & aclcheck) != aclcheck) {
	r = (myrights & ACL_LOOKUP) ?
	  IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	goto done;
    }

    q.root = mailbox->quotaroot;
    r = quota_read(&q, NULL, 0);
    if (!r) {
	if (q.limit >= 0 && quotacheck >= 0 &&
	    q.used + quotacheck > ((uquota_t) q.limit * QUOTA_UNITS)) {
	    r = IMAP_QUOTA_EXCEEDED;
	}
    }
    else if (r == IMAP_QUOTAROOT_NONEXISTENT) r = 0;

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
 *	quotacheck - mailbox must have this much quota left
 *		     (-1 means don't care about quota)
 *
 * On success, the struct pointed to by 'as' is set up.
 *
 */
int append_setup(struct appendstate *as, const char *name,
		 const char *userid, struct auth_state *auth_state,
		 long aclcheck, quota_t quotacheck)
{
    int r;
    struct quota q;

    memset(as, 0, sizeof(*as));

    r = mailbox_open_iwl(name, &as->mailbox);
    if (r) return r;

    as->myrights = cyrus_acl_myrights(auth_state, as->mailbox->acl);

    if ((as->myrights & aclcheck) != aclcheck) {
	r = (as->myrights & ACL_LOOKUP) ?
	  IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	mailbox_close(&as->mailbox);
	return r;
    }

    q.root = as->mailbox->quotaroot;
    r = quota_read(&q, NULL, 0);
    if (!r) {
	if (q.limit >= 0 && quotacheck >= 0 &&
	    q.used + quotacheck > ((uquota_t) q.limit * QUOTA_UNITS)) {
	    r = IMAP_QUOTA_EXCEEDED;
	}
    }
    else if (r == IMAP_QUOTAROOT_NONEXISTENT) r = 0;

    if (r) {
	mailbox_close(&as->mailbox);
	return r;
    }

    if (userid) {
	strlcpy(as->userid, userid, sizeof(as->userid));
    } else {
	as->userid[0] = '\0';
    }

    /* we'll need the cache file open */
    r = mailbox_open_cache(as->mailbox);
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

    return 0;
}

/* may return non-zero, indicating that the entire append has failed
 and the mailbox is probably in an inconsistent state. */
int append_commit(struct appendstate *as, 
		  quota_t quotacheck __attribute__((unused)),
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

    /* Calculate new index header information */
    as->mailbox->i.last_appenddate = time(0);

    /* the cache will be dirty even if we hand added the records */
    as->mailbox->cache_dirty = 1;

    /* set seen state */
    if (as->userid[0])
	append_addseen(as->mailbox, as->userid, as->seen_seq);
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
 * staging, to allow for single-instance store.  the complication here
 * is multiple partitions.
 */
int append_fromstage(struct appendstate *as, struct body **body,
		     struct stagemsg *stage, time_t internaldate,
		     const strarray_t *flags, int nolink)
{
    struct mailbox *mailbox = as->mailbox;
    struct index_record record;
    char *fname;
    FILE *destfile;
    int i, r;
    int userflag;

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
		r = message_update_conversations(cstate, &record, *body);
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
    if (r) {
	append_abort(as);
	return r;
    }

    /* Handle flags the user wants to set in the message */
    for (i = 0; flags && i < flags->count ; i++) {
	const char *flag = strarray_nth(flags, i);
	if (!strcmp(flag, "\\seen")) {
	    append_setseen(as, &record);
	}
	else if (!strcmp(flag, "\\deleted")) {
	    if (as->myrights & ACL_DELETEMSG) {
		record.system_flags |= FLAG_DELETED;
	    }
	}
	else if (!strcmp(flag, "\\draft")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_DRAFT;
	    }
	}
	else if (!strcmp(flag, "\\flagged")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_FLAGGED;
	    }
	}
	else if (!strcmp(flag, "\\answered")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_ANSWERED;
	    }
	}
	else if (as->myrights & ACL_WRITE) {
	    /* User flag */
	    r = mailbox_user_flag(mailbox, flag, &userflag);
	    if (!r) 
		record.user_flags[userflag/32] |= 1<<(userflag&31);
	}
    }
    /* Write out index file entry */
    r = mailbox_append_index_record(mailbox, &record);
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
		      const char **flag,
		      int nflags)
{
    struct mailbox *mailbox = as->mailbox;
    struct index_record record;
    char *fname;
    FILE *destfile;
    int i, r;
    int userflag;

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
	append_abort(as);
	return IMAP_IOERROR;
    }

    /* Copy and parse message */
    r = message_copy_strict(messagefile, destfile, size, 0);
    if (!r) {
	if (!*body || (as->nummsg - 1))
	    r = message_parse_file(destfile, NULL, NULL, body);
	if (!r) r = message_create_record(&record, *body);
    }
    fclose(destfile);
    if (r) {
	append_abort(as);
	return r;
    }

    /* Handle flags the user wants to set in the message */
    for (i = 0; i < nflags; i++) {
	if (!strcmp(flag[i], "\\seen")) {
	    append_setseen(as, &record);
	}
	else if (!strcmp(flag[i], "\\deleted")) {
	    if (as->myrights & ACL_DELETEMSG) {
		record.system_flags |= FLAG_DELETED;
	    }
	}
	else if (!strcmp(flag[i], "\\draft")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_DRAFT;
	    }
	}
	else if (!strcmp(flag[i], "\\flagged")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_FLAGGED;
	    }
	}
	else if (!strcmp(flag[i], "\\answered")) {
	    if (as->myrights & ACL_WRITE) {
		record.system_flags |= FLAG_ANSWERED;
	    }
	}
	else if (as->myrights & ACL_WRITE) {
	    r = mailbox_user_flag(mailbox, flag[i], &userflag);
	    if (!r)
		record.user_flags[userflag/32] |= 1<<(userflag&31);
	}
    }

    /* Write out index file entry; if we abort later, it's not
       important */
    r = mailbox_append_index_record(mailbox, &record);
    if (r) {
	append_abort(as);
	return r;
    }
    
    return 0;
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
				      copymsg[msg].flag[flag], &userflag);
		if (!r)
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
	if (destfname) free(destfname);
	srcfname = xstrdup(mailbox_message_fname(mailbox, copymsg[msg].uid));
	destfname = xstrdup(mailbox_message_fname(as->mailbox, record.uid));
	r = mailbox_copyfile(srcfname, destfname, nolink);
	free(srcfname);
	if (r) goto fail;

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
	    struct conversations_state *cstate = conversations_get_mbox(mailbox->name);
	    if (cstate)
		r = message_update_conversations_file(cstate, &record, destfname);
	    else
		r = IMAP_CONVERSATIONS_NOT_OPEN;
	    if (r) goto fail;
	}

	/* Write out index file entry */
	r = mailbox_append_index_record(as->mailbox, &record);
	if (r) goto fail;

	r = annotate_msg_copy(mailbox->name, copymsg[msg].uid,
			      as->mailbox->name, record.uid,
			      as->userid);
    }

 fail:
    if (destfname) free(destfname);
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
