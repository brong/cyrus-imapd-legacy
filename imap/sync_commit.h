/* sync_commit.h -- Cyrus synchonization mailbox functions
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
 * $Id: sync_commit.h,v 1.2.2.3 2009/12/28 21:51:40 murch Exp $
 *
 * Original version written by David Carter <dpc22@cam.ac.uk>
 * Rewritten and integrated into Cyrus by Ken Murchison <ken@oceana.com>
 */

#ifndef INCLUDED_SYNC_COMMIT_H
#define INCLUDED_SYNC_COMMIT_H

int sync_upload_commit(struct mailbox *mailbox, time_t last_appenddate,
		       struct sync_upload_list  *upload_list,
		       struct sync_message_list *message_list);

int sync_uidlast_commit(struct mailbox *mailbox, unsigned long last_uid,
			time_t last_appenddate);

int
sync_uidvalidity_commit(struct mailbox *mailbox,
                        unsigned long uidvalidity);

int sync_setflags_commit(struct mailbox *mailbox,
			 struct sync_flag_list *flag_list);

int sync_highestmodseq_commit(struct mailbox *mailbox,
                              modseq_t newhighestmodseq);


int sync_modseq_commit(struct mailbox *mailbox,
                       struct sync_modseq_list *modseq_list);


int sync_create_commit(char *name, char *partition, char *uniqueid, char *acl,
		       int mbtype, unsigned long options, unsigned long uidvalidity,
		       int isadmin, char *userid, struct auth_state *auth_state);

#endif /* INCLUDED_SYNC_COMMIT_H */
