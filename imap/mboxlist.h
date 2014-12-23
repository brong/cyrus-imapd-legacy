/* mboxlist.h -- Mailbox list manipulation routines
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
 */

#ifndef INCLUDED_MBOXLIST_H
#define INCLUDED_MBOXLIST_H

#include "config.h"
#include "cyrusdb.h"
#include "dlist.h"
#include "mailbox.h"
#include "auth.h"
#include "mboxevent.h"
#include "mboxname.h"

extern struct db *mbdb;

/*
 * Maximum length of partition name. [config.c has a limit of 70]
 */
#define MAX_PARTITION_LEN 64
#define MAILBOX_UNIQUEID_LEN 32

/* flags for types of mailboxes */
#define MBTYPE_REMOTE (1<<0) /* Not on this server (part is remote host) */
#define MBTYPE_RESERVE (1<<1) /* Reserved [mupdate/imapd] /
			       Rename Target [imapd] (part is normal, but
			       you are not allowed to create this mailbox,
			       even though it doesn't actually exist */
#define MBTYPE_NETNEWS (1<<2) /* Netnews Mailbox - NO LONGER USED */
#define MBTYPE_MOVING (1<<3) /* Mailbox in mid-transfer (part is remotehost!localpart) */
#define MBTYPE_DELETED (1<<4) /* Mailbox has been deleted, but not yet cleaned up */
#define MBTYPE_CALENDAR (1<<5) /* Calendar Mailbox */
#define MBTYPE_ADDRESSBOOK (1<<6) /* Addressbook Mailbox */

#define MBTYPES_DAV (MBTYPE_CALENDAR|MBTYPE_ADDRESSBOOK)
#define MBTYPES_NONIMAP (MBTYPE_NETNEWS|MBTYPES_DAV)

/* master name of the mailboxes file */
#define FNAME_MBOXLIST "/mailboxes.db"

#define HOSTNAME_SIZE 512

/* each mailbox has the following data */
struct mboxlist_entry {
    char *name;
    char *ext_name;
    time_t mtime;
    uint32_t uidvalidity;
    int mbtype;
    char *partition;
    char *server; /* holds remote machine for REMOTE mailboxes */
    char *acl;
    /* extra fields */
    char *uniqueid;
    /* legacy upgrade support */
    char *legacy_specialuse;
};

typedef struct mboxlist_entry mbentry_t;

mbentry_t *mboxlist_entry_create();

EXPORTED int mboxlist_parse_entry(mbentry_t **mbentryptr,
				  const char *name, size_t namelen,
				  const char *data, size_t datalen);

void mboxlist_entry_free(mbentry_t **mbentryptr);

/* formats a cstring from a mboxlist_entry.  Caller must free
 * after use */
char *mboxlist_entry_cstring(mbentry_t *mbentry);

const char *mboxlist_mbtype_to_string(uint32_t mbtype);
uint32_t mboxlist_string_to_mbtype(const char *string);

/* Lookup 'name' in the mailbox list. */
int mboxlist_lookup(const char *name, mbentry_t **mbentryptr,
		    struct txn **tid);
int mboxlist_lookup_allow_reserved(const char *name,
				   mbentry_t **mbentryptr,
				   struct txn **tid);

int mboxlist_parse_entry(mbentry_t **mbentryptr,
			 const char *name, size_t namelen,
			 const char *data, size_t datalen);


/* insert/delete stub entries */
int mboxlist_insertremote(mbentry_t *mbentry, struct txn **rettid);
int mboxlist_deleteremote(const char *name, struct txn **in_tid);

/* Update a mailbox's entry */
int mboxlist_update(mbentry_t *mbentry, int localonly);

/* check user's ability to create mailbox */
int mboxlist_createmailboxcheck(const char *name, int mbtype,
				const char *partition,
				int isadmin, const char *userid, 
				struct auth_state *auth_state, 
				char **newacl, char **newpartition,
				int forceuser);

/* create mailbox */
/* localonly creates the local mailbox without touching mupdate */
/* forceuser allows the creation of user.x.<name> without a user.x */
/* dbonly skips filesystem operations (e.g. reconstruct) */
/* notify sends a MailboxCreate event notification */
/* if given a mailbox pointer, return the still-locked mailbox
 * for further manipulation */
int mboxlist_createmailbox(const char *name, int mbtype,
			   const char *partition,
			   int isadmin, const char *userid, 
			   struct auth_state *auth_state,
			   int localonly, int forceuser, int dbonly,
			   int notify, struct mailbox **mailboxptr);

/* create mailbox from sync */
int mboxlist_createsync(const char *name, int mbtype,
			const char *partition, 
			const char *userid, struct auth_state *auth_state,
			int options, unsigned uidvalidity, 
			modseq_t highestmodseq, const char *acl,
			const char *uniqueid, struct mailbox **mboxptr);

/* delated delete */
/* Translate delete into rename */
/* prepare MailboxDelete notification if mboxevent is not NULL */
int
mboxlist_delayed_deletemailbox(const char *name, int isadmin, const char *userid, 
                               struct auth_state *auth_state,
                               struct mboxevent *mboxevent,
			       int checkacl,
                               int force);
/* Delete a mailbox. */
/* setting local_only disables any communication with the mupdate server
 * and deletes the mailbox from the filesystem regardless of if it is
 * MBTYPE_REMOTE or not */
/* force ignores errors and just tries to wipe the mailbox off the face of
 * the planet */
/* prepare MailboxDelete notification if mboxevent is not NULL */
int mboxlist_deletemailbox(const char *name, int isadmin, const char *userid, 
			   struct auth_state *auth_state,
			   struct mboxevent *mboxevent,
			   int checkacl,
			   int local_only, int force);

/* Rename/move a mailbox (hierarchical) */
/* prepare MailboxRename notification if mboxevent is not NULL */
int mboxlist_renamemailbox(const char *oldname, const char *newname,
			   const char *partition, unsigned uidvalidity,
			   int isadmin, const char *userid,
			   struct auth_state *auth_state,
			   struct mboxevent *mboxevent,
			   int forceuser, int ignorequota);

/* change ACL */
int mboxlist_setacl(struct namespace *namespace, const char *name,
		    const char *identifier, const char *rights, int isadmin,
		    const char *userid, struct auth_state *auth_state);

/* Change all ACLs on mailbox */
int mboxlist_sync_setacls(const char *name, const char *acl);

/* Find all mailboxes that match 'pattern'. */
int mboxlist_findall(struct namespace *namespace,
		     const char *pattern, int isadmin, const char *userid, 
		     struct auth_state *auth_state, int (*proc)(), void *rock);
int mboxlist_findall_alt(struct namespace *namespace,
			 const char *pattern, int isadmin, const char *userid, 
			 struct auth_state *auth_state, int (*proc)(),
			 void *rock);

/* Find a mailbox's parent (if any) */
int mboxlist_findparent(const char *mboxname,
			mbentry_t **mbentryp);

/* direct access to subs DB */
typedef int user_cb(const char *userid, void *rock);
int mboxlist_allsubs(const char *userid, foreach_cb *proc, void *rock);
int mboxlist_allmbox(const char *prefix, foreach_cb *proc, void *rock, int incdel);
int mboxlist_alluser(user_cb *proc, void *rock);
int mboxlist_allusermbox(const char *userid, foreach_cb *proc, void *rock,
			 int include_deleted);

/* Find subscribed mailboxes that match 'pattern'. */
int mboxlist_findsub(struct namespace *namespace,
		     const char *pattern, int isadmin, const char *userid, 
		     struct auth_state *auth_state, int (*proc)(), void *rock,
		     int force);
int mboxlist_findsub_alt(struct namespace *namespace,
			 const char *pattern, int isadmin, char const *userid, 
			 struct auth_state *auth_state, int (*proc)(),
			 void *rock, int force);

/* given a mailbox 'name', where should we stage messages for it? 
   'stagedir' should be MAX_MAILBOX_PATH. */
int mboxlist_findstage(const char *name, char *stagedir, size_t sd_len);

/* Check 'user's subscription status for mailbox 'name' */
int mboxlist_checksub(const char *name, const char *userid);

/* Change 'user's subscription status for mailbox 'name'. */
int mboxlist_changesub(const char *name, const char *userid, 
		       struct auth_state *auth_state,
		       int add, int force, int notify);

/* set or create quota root */
int mboxlist_setquotas(const char *root,
		       quota_t newquotas[QUOTA_NUMRESOURCES], int force);
int mboxlist_unsetquota(const char *root);

/* open the mailboxes db */
void mboxlist_open(const char *name);

/* close the database */
void mboxlist_close(void);

/* initialize database structures */
#define MBOXLIST_SYNC 0x02
void mboxlist_init(int flags);

/* done with database stuff */
void mboxlist_done(void);

/* for transactions */
int mboxlist_commit(struct txn *tid);
int mboxlist_abort(struct txn *tid);

int mboxlist_delayed_delete_isenabled(void);

#endif
