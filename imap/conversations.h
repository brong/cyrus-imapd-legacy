/* conversations.h -- Routines for dealing with the conversations database
 *
 * Copyright (c) 1994-2010 Carnegie Mellon University.  All rights reserved.
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
 */

#ifndef __CYRUS_CONVERSATIONS_H_
#define __CYRUS_CONVERSATIONS_H_ 1

#if HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdio.h>
#include <string.h>
#include "util.h"

typedef bit64	conversation_id_t;
#define CONV_FMT "%016llx"
#define NULLCONVERSATION	(0ULL)

struct conversations_state {
    struct db *db;
    struct txn *txn;
    char *path;
};

struct conversations_open {
    struct conversations_state s;
    struct conversations_open *next;
};

struct conversations_open *open_conversations;

typedef struct conversation conversation_t;
typedef struct conv_folder  conv_folder_t;
typedef struct conv_sender  conv_sender_t;

struct conv_folder {
    conv_folder_t   *next;
    char	    *mboxname;
    modseq_t	    modseq;
    uint32_t	    exists;
    uint32_t	    prev_exists;
};

struct conv_sender {
    conv_sender_t   *next;
    char	    *name;
    char	    *route;
    char	    *mailbox;
    char	    *domain;
};

struct conversation {
    modseq_t	    modseq;
    uint32_t	    exists;
    uint32_t	    unseen;
    uint32_t	    prev_unseen;
    uint32_t	    drafts;
    uint32_t	    flagged;
    uint32_t	    attachments;
    conv_folder_t   *folders;
    conv_sender_t   *senders;
    int		    dirty;
};

extern char *conversations_getmboxpath(const char *mboxname);
extern char *conversations_getuserpath(const char *username);

extern int conversations_open_path(const char *path,
				   struct conversations_state **statep);
extern int conversations_open_user(const char *username,
				   struct conversations_state **statep);
extern int conversations_open_mbox(const char *mboxname,
				   struct conversations_state **statep);
extern struct conversations_state *conversations_get_path(const char *path);
extern struct conversations_state *conversations_get_user(const char *username);
extern struct conversations_state *conversations_get_mbox(const char *mboxname);

/* either of these close */
extern int conversations_abort(struct conversations_state **state);
extern int conversations_commit(struct conversations_state **state);

/* functions for CONVDB_MSGID database only */
extern int conversations_set_msgid(struct conversations_state *state,
				   const char *msgid,
				   conversation_id_t cid);
extern int conversations_get_msgid(struct conversations_state *state,
				   const char *msgid,
				   conversation_id_t *cidp);

/* functions for CONVDB_COUNTS only */
extern int conversation_getstatus(struct conversations_state *state,
				  const char *mboxname,
				  modseq_t *modseqp,
				  uint32_t *existsp,
				  uint32_t *unseenp);
extern int conversation_setstatus(struct conversations_state *state,
				  const char *mboxname,
				  modseq_t modseq,
				  uint32_t exists,
				  uint32_t unseen);
extern int conversation_save(struct conversations_state *state,
			     conversation_id_t cid,
			     conversation_t *conv);
extern int conversation_load(struct conversations_state *state,
			     conversation_id_t cid,
			     conversation_t **convp);
/* Update the internal data about a conversation, enforcing
 * consistency rules (e.g. the conversation's modseq is the
 * maximum of all the per-folder modseqs).  Sets conv->dirty
 * if any data actually changed.  */
extern void conversation_update(conversation_t *conv,
			        const char *mboxname,
			        int delta_exists,
			        int delta_unseen,
			        int delta_drafts,
			        int delta_flagged,
			        int delta_attachments,
			        modseq_t modseq);
extern conv_folder_t *conversation_find_folder(conversation_t *,
					       const char *mboxname);
extern conv_folder_t *conversation_add_folder(conversation_t *,
					      const char *mboxname);
extern conversation_t *conversation_new(void);
extern void conversation_free(conversation_t *);

extern void conversation_add_sender(conversation_t *conv,
				    const char *name,
				    const char *route,
				    const char *mailbox,
				    const char *domain);

extern int conversations_prune(struct conversations_state *state,
			       time_t thresh, unsigned int *,
			       unsigned int *);
extern void conversations_dump(struct conversations_state *, FILE *);
extern int conversations_undump(struct conversations_state *, FILE *);

extern int conversations_truncate(struct conversations_state *);

extern const char *conversation_id_encode(conversation_id_t cid);
extern int conversation_id_decode(conversation_id_t *cid, const char *text);

typedef void (*conversations_rename_cb_t)(const char *mboxname,
					  conversation_id_t from_cid,
					  conversation_id_t to_cid,
					  void *rock);

extern int conversations_rename_cid(struct conversations_state *state,
				    conversation_id_t from_cid,
				    conversation_id_t to_cid);

extern int conversations_wipe_counts(struct conversations_state *state);

extern int conversations_rename_folder(struct conversations_state *state,
			               const char *from_name,
			               const char *to_name);
#endif /* __CYRUS_CONVERSATIONS_H_ */
