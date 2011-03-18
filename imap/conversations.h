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
#include "strarray.h"

typedef bit64	conversation_id_t;
#define CONV_FMT "%016llx"
#define NULLCONVERSATION	(0ULL)

struct conversations_state
{
    struct db *db;
    struct txn *txn;
};

extern char *conversations_getpath(const char *mboxname);
extern int conversations_open(struct conversations_state *state,
			      const char *fname);
extern int conversations_close(struct conversations_state *state);

extern int conversations_commit(struct conversations_state *state);

extern int conversations_set_msgid(struct conversations_state *state,
				   const char *msgid,
				   conversation_id_t cid);
extern int conversations_get_msgid(struct conversations_state *state,
				   const char *msgid,
				   conversation_id_t *cidp);
extern int conversations_set_folder(struct conversations_state *state,
				    conversation_id_t cid,
				    modseq_t modseq,
				    const char *mboxname);
extern int conversations_get_folders(struct conversations_state *state,
				     conversation_id_t cid,
				     modseq_t *highestmodseqp,
				     strarray_t *sa);

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
				    conversation_id_t to_cid,
				    conversations_rename_cb_t renamecb,
				    void *rock);
extern int conversations_rename_cid_mb(const char *name,
				       conversation_id_t from_cid,
				       conversation_id_t to_cid,
				       conversations_rename_cb_t renamecb,
				       void *rock);

#endif /* __CYRUS_CONVERSATIONS_H_ */
