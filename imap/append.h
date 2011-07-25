/* append.h -- Description of messages to be copied 
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
 * $Id: append.h,v 1.34 2010/01/06 17:01:30 murch Exp $
 */

#ifndef INCLUDED_APPEND_H
#define INCLUDED_APPEND_H

#include "mailbox.h"
#include "message.h"
#include "prot.h"
#include "sequence.h"
#include "strarray.h"
#include "conversations.h"

struct copymsg {
    unsigned long uid;
    time_t internaldate;
    time_t sentdate;
    time_t gmtime;
    unsigned long size;
    unsigned long header_size;
    unsigned long content_lines;
    unsigned long cache_version;
    unsigned long cache_crc;
    struct cacherecord crec;
    int seen;
    struct message_guid guid;
    bit32 system_flags;
    char *flag[MAX_USER_FLAGS+1];
};

/* it's ridiculous i have to expose this structure if i want to allow
   clients to stack-allocate it */
struct appendstate {
    /* mailbox we're appending to */
    struct mailbox *mailbox;
    int myrights;
    char userid[MAX_MAILBOX_BUFFER];

    enum { APPEND_READY, APPEND_DONE } s;
				/* current state of append */

    int nummsg;    /* number of messages appended pending commit.
		      from as->baseuid ... m.baseuid + nummsg - 1 */
    unsigned baseuid; 

    /* set seen on these message on commit */
    int internalseen;
    struct seqset *seen_seq;

    struct conversations_state conversations;
};

/* add helper function to determine uid range appended? */

struct stagemsg;

extern int append_check(const char *name,
			struct auth_state *auth_state,
			long aclcheck, quota_t quotacheck);

/* appendstate must be allocated by client */
extern int append_setup(struct appendstate *as, const char *name,
			const char *userid, struct auth_state *auth_state,
			long aclcheck, quota_t quotacheck);

extern int append_commit(struct appendstate *as,
			 quota_t quotacheck,
			 unsigned long *uidvalidity, 
			 unsigned long *startuid, 
			 unsigned long *num,
			 struct mailbox **mailboxptr);
extern int append_abort(struct appendstate *as);

/* creates a new stage and returns stage file corresponding to mailboxname */
extern FILE *append_newstage(const char *mailboxname, time_t internaldate,
			     int msgnum, struct stagemsg **stagep);

/* adds a new mailbox to the stage initially created by append_newstage() */
extern int append_fromstage(struct appendstate *mailbox, struct body **body,
			    struct stagemsg *stage, time_t internaldate,
			    const strarray_t *flags, int nolink);

/* removes the stage (frees memory, deletes the staging files) */
extern int append_removestage(struct stagemsg *stage);

extern int append_fromstream(struct appendstate *as, struct body **body,
			     struct protstream *messagefile,
			     unsigned long size, time_t internaldate,
			     const char **flag, int nflags);

extern int append_copy(struct mailbox *mailbox,
		       struct appendstate *append_mailbox,
		       int nummsg, struct copymsg *copymsg, int nolink);

extern int append_collectnews(struct appendstate *mailbox,
			      const char *group, unsigned long feeduid);

#define append_getuidvalidity(as) ((as)->m.uidvalidity);
#define append_getlastuid(as) ((as)->m.last_uid);

#endif /* INCLUDED_APPEND_H */
