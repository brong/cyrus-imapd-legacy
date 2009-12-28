/* lmtpd.h -- Program to deliver mail to a mailbox
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
 * $Id: lmtpd.h,v 1.4.2.1 2009/12/28 21:51:34 murch Exp $
 */

#ifndef LMTPD_H
#define LMTPD_H

#include "append.h"
#include "auth.h"
#include "lmtpengine.h"
#include "mboxname.h"
#include "message.h"

/* data per message */
typedef struct deliver_data {
    message_data_t *m;
    struct message_content *content;

    int cur_rcpt;

    struct stagemsg *stage;	/* staging location for single instance
				   store */
    char *notifyheader;
    const char *temp[2];	/* used to avoid extra indirection in
				   getenvelope() */

    struct namespace *namespace;

    char *authuser;		/* user who submitted message */
    struct auth_state *authstate;
} deliver_data_t;

/* forward declarations */
extern int deliver_local(deliver_data_t *mydata,
			 char **flag,
			 int nflags,
			 const char *username,
			 const char *mailboxname);

extern int deliver_mailbox(FILE *f,
			   struct message_content *content,
			   struct stagemsg *stage,
			   unsigned size,
			   char **flag,
			   int nflags,
			   char *authuser,
			   struct auth_state *authstate,
			   char *id,
			   const char *user,
			   char *notifyheader,
			   const char *mailboxname,
			   int quotaoverride,
			   int acloverride);

extern int fuzzy_match(char *mboxname);

#endif /* LMTPD_H */
