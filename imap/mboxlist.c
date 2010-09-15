/* uboxlist.c -- Mailbox list manipulation routines
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
 * $Id: mboxlist.c,v 1.275 2010/07/23 19:19:03 wescraig Exp $
 */

#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <fcntl.h>
#include <ctype.h>
#include <syslog.h>

#include <sys/ipc.h>
#include <sys/msg.h>

#include "acl.h"
#include "annotate.h"
#include "auth.h"
#include "glob.h"
#include "assert.h"
#include "global.h"
#include "cyrusdb.h"
#include "util.h"
#include "mailbox.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "user.h"

#include "mboxname.h"
#include "mupdate-client.h"

#include "mboxlist.h"
#include "quota.h"
#include "sync_log.h"

#define DB config_mboxlist_db
#define SUBDB config_subscription_db

cyrus_acl_canonproc_t mboxlist_ensureOwnerRights;

struct db *mbdb;

static int mboxlist_dbopen = 0;

static int mboxlist_opensubs();
static void mboxlist_closesubs();

static int mboxlist_rmquota(const char *name, int matchlen, int maycreate,
			    void *rock);
static int mboxlist_changequota(const char *name, int matchlen, int maycreate,
				void *rock);

struct change_rock {
    struct quota *quota;
    struct txn **tid;
};

char *mboxlist_makeentry(int mbtype, const char *part, const char *acl)
{
    char *mboxent = (char *) xmalloc(sizeof(char) * 
				     (30 + strlen(acl) + strlen(part)));
    sprintf(mboxent, "%d %s %s", mbtype, part, acl);
    return mboxent;
}

/*
 * Lookup 'name' in the mailbox list.
 * The capitalization of 'name' is canonicalized to the way it appears
 * in the mailbox list.
 * If 'path' is non-nil, a pointer to the full pathname of the mailbox
 * is placed in the char * pointed to by it.  If 'acl' is non-nil, a pointer
 * to the mailbox ACL is placed in the char * pointed to by it.
 */
static int mboxlist_read(const char *name, const char **dataptr, int *datalenptr,
			 struct txn **tid, int wrlock)
{
    int namelen = strlen(name);
    int r;

    if (namelen == 0) {
	return IMAP_MAILBOX_NONEXISTENT;
    }
    if (wrlock) {
	r = DB->fetchlock(mbdb, name, namelen, dataptr, datalenptr, tid);
    } else {
	r = DB->fetch(mbdb, name, namelen, dataptr, datalenptr, tid);
    }

    switch (r) {
    case CYRUSDB_OK:
	/* no entry required, just checking if it exists */
	return 0;
	break;

    case CYRUSDB_AGAIN:
	return IMAP_AGAIN;
	break;

    case CYRUSDB_NOTFOUND:
	return IMAP_MAILBOX_NONEXISTENT;
	break;

    default:
	syslog(LOG_ERR, "DBERROR: error fetching mboxlist %s: %s",
	       name, cyrusdb_strerror(r));
	return IMAP_IOERROR;
	break;
    }

    /* never get here */
}

static int mboxlist_mylookup(const char *name, struct mboxlist_entry *entry,
			     struct txn **tid, int wrlock)
{
    int acllen;
    static char partition[MAX_PARTITION_LEN+HOSTNAME_SIZE+2];
    static char *aclresult;
    static int aclresultalloced;
    int r;
    const char *data;
    char *p, *q;
    int datalen;
    int mbtype;

    r = mboxlist_read(name, &data, &datalen, tid, wrlock);
    if (r) return r;

    /* copy out interesting parts */
    mbtype = strtol(data, &p, 10);

    /* here we go, ignore them! */
    if (mbtype & MBTYPE_RESERVE)
	return IMAP_MAILBOX_RESERVED;

    if (*p == ' ') p++;
    q = partition;
    while (*p != ' ') { /* copy out partition name */
	*q++ = *p++;
    }
    *q = '\0';
    p++;

    acllen = datalen - (p - data);
    if (acllen >= aclresultalloced) {
	aclresultalloced = acllen + 100;
	aclresult = xrealloc(aclresult, aclresultalloced);
    }
    memcpy(aclresult, p, acllen);
    aclresult[acllen] = '\0';

    if (entry) {
	entry->name = name;
	entry->partition = partition;
	entry->mbtype = mbtype;
	entry->acl = aclresult;
    }

    return 0;
}

/*
 * Lookup 'name' in the mailbox list.
 * The capitalization of 'name' is canonicalized to the way it appears
 * in the mailbox list.
 * If 'acl' is non-nil, a pointer to the mailbox ACL is placed in the char
 * pointed to by it.
 */
int mboxlist_lookup(const char *name, struct mboxlist_entry *entry, struct txn **tid)
{
    return mboxlist_mylookup(name, entry, tid, 0);
}

int mboxlist_findstage(const char *name, char *stagedir, size_t sd_len) 
{
    const char *root;
    struct mboxlist_entry mbentry;
    int r;

    assert(stagedir != NULL);

    /* Find mailbox */
    r = mboxlist_lookup(name, &mbentry, NULL);
    switch (r) {
    case 0:
	break;
    default:
	return r;
	break;
    }
	    
    root = config_partitiondir(mbentry.partition);
    if (!root) return IMAP_PARTITION_UNKNOWN;
	
    snprintf(stagedir, sd_len, "%s/stage./", root);
    
    return 0;
}

int mboxlist_update(const char *name, int mbtype, 
		    const char *part, const char *uniqueid,
		    const char *acl, int localonly)
{
    int r = 0, r2 = 0;
    char *mboxent = NULL;
    struct txn *tid = NULL;
    
    mboxent = mboxlist_makeentry(mbtype, part, acl);
    r = DB->store(mbdb, name, strlen(name), mboxent, strlen(mboxent), &tid);
    free(mboxent);
    mboxent = NULL;

    if (!r && !localonly && config_mupdate_server) {
        mupdate_handle *mupdate_h = NULL;
	/* commit the update to MUPDATE */
	char buf[MAX_PARTITION_LEN + HOSTNAME_SIZE + 2];
	
	snprintf(buf, sizeof(buf), "%s!%s", config_servername, part);
	
	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if(r) {
	    syslog(LOG_ERR,
		   "cannot connect to mupdate server for update of '%s'",
		   name);
	} else {
	    r = mupdate_activate(mupdate_h, name, buf, acl);
	    if(r) {
		syslog(LOG_ERR,
		       "MUPDATE: can't update mailbox entry for '%s'",
		       name);
	    }
	}
	mupdate_disconnect(&mupdate_h);
    }

    if (tid) {
	if(r) {
	    r2 = DB->abort(mbdb, tid);
	} else {
	    r2 = DB->commit(mbdb, tid);
	}
    }

    if (r2) {
	syslog(LOG_ERR, "DBERROR: error %s txn in mboxlist_update: %s",
	       r ? "aborting" : "commiting", cyrusdb_strerror(r2));
    }

    return r;
}

/*
 * Check/set up for mailbox creation
 */
/* xxx shouldn't we be using mbtype or getting rid of it entirely? */
static int
mboxlist_mycreatemailboxcheck(const char *mboxname,
			      int new_mbtype __attribute__((unused)),
			      const char *partition,
			      int isadmin, const char *userid,
			      struct auth_state *auth_state,
			      char **newacl, char **newpartition,
			      int RMW, int localonly, int force_user_create,
			      struct txn **tid)
{
    int r;
    struct mboxlist_entry mbentry;
    char *name = xstrdup(mboxname);
    char *mbox = name;
    char *p;
    char *defaultacl, *identifier, *rights;
    char parent[MAX_MAILBOX_BUFFER];
    unsigned long parentlen;
    char *parentname = NULL;
    unsigned long parentpartitionlen = 0;
    unsigned long parentacllen = 0;
    int user_folder_limit;
    char *ourpartition;
    char *ouracl;
    
    /* Check for invalid name/partition */
    if (partition && strlen(partition) > MAX_PARTITION_LEN) {
	return IMAP_PARTITION_UNKNOWN;
    }
    if (config_virtdomains && (p = strchr(name, '!'))) {
	/* pointer to mailbox w/o domain prefix */
	mbox = p + 1;
    }
    r = mboxname_policycheck(mbox);
    /* filthy hack to support rename pre-check semantics, which
       will go away when we refactor this code */
    if (r && force_user_create != 1) return r;

    /* you must be a real admin to create a local-only mailbox */
    if(!isadmin && localonly) return IMAP_PERMISSION_DENIED;
    if(!isadmin && force_user_create) return IMAP_PERMISSION_DENIED;

    /* User has admin rights over their own mailbox namespace */
    if (mboxname_userownsmailbox(userid, name) && strchr(mbox+5, '.') &&
	(config_implicitrights & ACL_ADMIN)) {
	isadmin = 1;
    }

    /* Check to see if new mailbox exists */
    r = mboxlist_mylookup(name, &mbentry, tid, RMW);
    switch (r) {
    case 0:
	r = IMAP_MAILBOX_EXISTS;
	
	/* Lie about error if privacy demands */
	if (!isadmin && 
	    !(cyrus_acl_myrights(auth_state, mbentry.acl) & ACL_LOOKUP)) {
	    r = IMAP_PERMISSION_DENIED;
	}

	return r;       
	break;
    case IMAP_MAILBOX_NONEXISTENT:
	break;

    default:
	return r;
	break;
    }

    /* Search for a parent - stop if we hit the domain separator */
    strlcpy(parent, name, sizeof(parent));
    parentlen = 0;
    while ((parentlen==0) && (p = strrchr(parent, '.')) && !strchr(p, '!')) {
	*p = '\0';

	r = mboxlist_mylookup(parent, &mbentry, tid, 0);
	switch (r) {
	case 0:
	  parentlen = strlen(parent);
	  parentname = parent;

	  parentpartitionlen = strlen(mbentry.partition);

	  parentacllen = strlen(mbentry.acl);
	  break;

	case IMAP_MAILBOX_NONEXISTENT:
	    break;

	default:
	    return r;
	    break;
	}
    }

    /* check the folder limit - XXX bogus for two reasons! (user is admin, domain check failure) */
    if (!isadmin && (user_folder_limit = config_getint(IMAPOPT_USER_FOLDER_LIMIT))) {
	char buf[MAX_MAILBOX_NAME+1];
	strncpy(buf, mbox, MAX_MAILBOX_NAME);
	if (!strncmp(buf, "user.", 5)) {
	    char *firstdot = strchr(buf+5, '.');
	    if (firstdot) *firstdot = '\0';
	    if (mboxlist_count_inferiors(buf, isadmin, userid, auth_state) + 1
					 >= user_folder_limit) {
		syslog(LOG_ERR, "LIMIT: refused to create %s for %s because of limit %d",
			        mbox, userid, user_folder_limit);
		return IMAP_PERMISSION_DENIED;
	    }
	}
    }

    if (parentlen != 0) {
	/* check acl */
	if (!isadmin &&
	    !(cyrus_acl_myrights(auth_state, mbentry.acl) & ACL_CREATE)) {
	    return IMAP_PERMISSION_DENIED;
	}

      	/* Copy partition, if not specified */
	if (partition == NULL) {
	    ourpartition = xmalloc(parentpartitionlen + 1);
	    memcpy(ourpartition, mbentry.partition, parentpartitionlen);
	    ourpartition[parentpartitionlen] = '\0';
	} else {
	    ourpartition = xstrdup(partition);
	}

	/* Copy ACL */
	ouracl = xmalloc(parentacllen + 1);
	memcpy(ouracl, mbentry.acl, parentacllen);
	ouracl[parentacllen] = '\0';

	/* Canonicalize case of parent prefix */
	strncpy(name, parent, strlen(parent));
    } else { /* parentlen == 0, no parent mailbox */
	if (!isadmin) {
	    return IMAP_PERMISSION_DENIED;
	}
	
	ouracl = xstrdup("");
	if (!strncmp(mbox, "user.", 5)) {
	    char *firstdot = strchr(mbox+5, '.');
	    if (!force_user_create && firstdot) {
		/* Disallow creating user.X.* when no user.X */
		free(name);
		free(ouracl);
		return IMAP_PERMISSION_DENIED;
	    }

	    /*
	     * Users by default have all access to their personal mailbox(es),
	     * Nobody else starts with any access to same.
	     *
	     * If this is a forced user create, we might have to avoid creating
	     * an acl for the wrong user.
	     */
	    if(firstdot) *firstdot = '\0';
	    identifier = xmalloc(mbox - name + strlen(mbox+5) + 1);
	    strcpy(identifier, mbox+5);
	    if(firstdot) *firstdot = '.';

	    if (config_getswitch(IMAPOPT_UNIXHIERARCHYSEP)) {
		/*
		 * The mailboxname is now in the internal format,
		 * so we we need to change DOTCHARs back to '.'
		 * in the identifier in order to have the correct ACL.
		 */
		for (p = identifier; *p; p++) {
		    if (*p == DOTCHAR) *p = '.';
		}
	    }
	    if (mbox != name) {
		/* add domain to identifier */
		sprintf(identifier+strlen(identifier),
			"@%.*s", (int) (mbox - name - 1), name);
	    }
	    cyrus_acl_set(&ouracl, identifier, ACL_MODE_SET, ACL_ALL,
		    (cyrus_acl_canonproc_t *)0, (void *)0);
	    free(identifier);
	} else {
	    defaultacl = identifier = 
		xstrdup(config_getstring(IMAPOPT_DEFAULTACL));
	    for (;;) {
		while (*identifier && Uisspace(*identifier)) identifier++;
		rights = identifier;
		while (*rights && !Uisspace(*rights)) rights++;
		if (!*rights) break;
		*rights++ = '\0';
		while (*rights && Uisspace(*rights)) rights++;
		if (!*rights) break;
		p = rights;
		while (*p && !Uisspace(*p)) p++;
		if (*p) *p++ = '\0';
		cyrus_acl_set(&ouracl, identifier, ACL_MODE_SET, cyrus_acl_strtomask(rights),
			(cyrus_acl_canonproc_t *)0, (void *)0);
		identifier = p;
	    }
	    free(defaultacl);
	}

	if (!partition) { 
	    if (config_mupdate_server &&
		(config_mupdate_config == IMAP_ENUM_MUPDATE_CONFIG_STANDARD) &&
		!config_getstring(IMAPOPT_PROXYSERVERS)) {
		/* proxy-only server -- caller will find a server */
		partition = NULL;
	    }
	    else {
		/* use defaultpartition if specified */
		partition = (char *)config_defpartition;

		/* otherwise find partition with most available space */
		if (!partition) partition = find_free_partition(NULL);

		if (strlen(partition) > MAX_PARTITION_LEN) {
		    /* Configuration error */
		    fatal("name of default partition is too long", EC_CONFIG);
		}
	    }
	}
	if (partition) ourpartition = xstrdup(partition);
    }

    if (newpartition) *newpartition = ourpartition;
    else free(ourpartition);
    if (newacl) *newacl = ouracl;
    else free(ouracl);

    return 0;
}

int
mboxlist_createmailboxcheck(const char *name, int mbtype,
			    const char *partition, 
			    int isadmin, const char *userid, 
			    struct auth_state *auth_state, 
			    char **newacl, char **newpartition,
			    int forceuser)
{
    return mboxlist_mycreatemailboxcheck(name, mbtype, partition, isadmin,
					 userid, auth_state, newacl, 
					 newpartition, 0, 0, forceuser, NULL);
}

/*
 * Create a mailbox
 *
 * 1. verify ACL's to best of ability (CRASH: abort)
 * 2. verify parent ACL's if need to
 * 3. create the local mailbox locally (exclusive lock) and keep it locked
 * 4. open mupdate connection if necessary
 * 5. create mupdate entry (CRASH: mupdate inconsistant)
 *
 */

int mboxlist_createmailbox_full(const char *name, int mbtype,
				const char *partition,
				int isadmin, const char *userid,
				struct auth_state *auth_state,
				int options, unsigned uidvalidity,
				const char *copyacl, const char *uniqueid,
				int localonly, int forceuser, int dbonly)
{
    int r;
    char *newpartition = NULL;
    mupdate_handle *mupdate_h = NULL;
    char *mboxent = NULL;
    char *acl = NULL;
    struct mailbox *newmailbox = NULL;
    int isremote = mbtype & MBTYPE_REMOTE;

    /* Must be atleast MAX_PARTITION_LEN + 30 for partition, need
     * MAX_PARTITION_LEN + HOSTNAME_SIZE + 2 for mupdate location */
    char buf[MAX_PARTITION_LEN + HOSTNAME_SIZE + 2];

    if (copyacl) {
	newpartition = xstrdup(partition);
	acl = xstrdup(copyacl);
    }
    else {
	/* 2. verify ACL's to best of ability (CRASH: abort) */
	r = mboxlist_mycreatemailboxcheck(name, mbtype, partition, isadmin, 
					  userid, auth_state, 
					  &acl, &newpartition, 1, localonly,
					  forceuser, NULL);
	if (r) goto done;
    }

    if (!dbonly && !isremote) {
	/* Filesystem Operations */
	r = mailbox_create(name, newpartition, acl, uniqueid,
			   options, uidvalidity, &newmailbox);
    }

    if (r) goto done; /* CREATE failed */ 

    /* all is well - activate the mailbox */
    mboxent = mboxlist_makeentry(newmailbox->mbtype, newmailbox->part,
				 newmailbox->acl);
    r = DB->store(mbdb, name, strlen(name), mboxent, strlen(mboxent), NULL);

    if (r) {
	syslog(LOG_ERR, "DBERROR: failed to insert to mailboxes list %s: %s", 
	       name, cyrusdb_strerror(r));
	r = IMAP_IOERROR;
    }

    /* 9. set MUPDATE entry as commited (CRASH: commited) */
    if (!r && config_mupdate_server && !localonly) {
	/* commit the mailbox in MUPDATE */
	snprintf(buf, sizeof(buf), "%s!%s", config_servername, newpartition);

	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if (!r) r = mupdate_reserve(mupdate_h, name, buf);
	if (!r) r = mupdate_activate(mupdate_h, name, buf, acl);
	if (r) {
	    syslog(LOG_ERR,
		   "MUPDATE: can't commit mailbox entry for '%s'", name);
	    DB->delete(mbdb, name, strlen(name), NULL, 0);
	}
	if (mupdate_h) mupdate_disconnect(&mupdate_h);
    }

done:
    if (newmailbox) {
	if (r) mailbox_delete(&newmailbox);
	else mailbox_close(&newmailbox);
    }

    if (acl) free(acl);
    if (newpartition) free(newpartition);
    if (mboxent) free(mboxent);
   
    return r;
}

int mboxlist_createmailbox(const char *name, int mbtype,
			   const char *partition, 
			   int isadmin, const char *userid, 
			   struct auth_state *auth_state,
			   int localonly, int forceuser, int dbonly)
{
    int options = config_getint(IMAPOPT_MAILBOX_DEFAULT_OPTIONS) | OPT_POP3_NEW_UIDL;
    unsigned uidvalidity = time(0);
    return mboxlist_createmailbox_full(name, mbtype, partition,
				       isadmin, userid, auth_state,
				       options, uidvalidity, NULL, NULL,
				       localonly, forceuser, dbonly);
}

int mboxlist_createsync(const char *name, int mbtype,
			const char *partition,
			const char *userid, struct auth_state *auth_state,
			int options, unsigned uidvalidity,
			const char *acl, const char *uniqueid)
{
    return mboxlist_createmailbox_full(name, mbtype, partition,
				       1, userid, auth_state,
				       options, uidvalidity, acl, uniqueid,
				       0, 1, 0);
}

/* insert an entry for the proxy */
int mboxlist_insertremote(const char *name, int mbtype,
			  const char *host, const char *acl,
			  struct txn **tid)
{
    char *mboxent, *p;
    int r = 0;

    assert(name != NULL && host != NULL);

    if ((p = strchr(host, '!'))) {
      /* remote mailbox */
      size_t len = (p - host);
      if (config_mupdate_config == IMAP_ENUM_MUPDATE_CONFIG_UNIFIED &&
	  len == strlen(config_servername) &&
	  !strncasecmp(host, config_servername, len)) {
	/* its on our server, make it a local mailbox */
	mbtype &= ~MBTYPE_REMOTE;
	host += len + 1;
      }
      else {
	/* make sure its a remote mailbox */
	mbtype |= MBTYPE_REMOTE;
      }
    }

    mboxent = mboxlist_makeentry(mbtype, host, acl);

    /* database put */
    r = DB->store(mbdb, name, strlen(name), mboxent, strlen(mboxent), tid);
    switch (r) {
    case CYRUSDB_OK:
	break;
    case CYRUSDB_AGAIN:
	abort(); /* shouldn't happen ! */
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error updating database %s: %s",
	       name, cyrusdb_strerror(r));
	r = IMAP_IOERROR;
	break;
    }

    free(mboxent);
    
    return r;
}

/* Special function to delete a remote mailbox.
 * Only affects mboxlist.
 * Assumes admin powers. */
int mboxlist_deleteremote(const char *name, struct txn **in_tid) 
{
    int r;
    struct txn **tid;
    struct txn *lcl_tid = NULL;
    struct mboxlist_entry mbentry;

    if(in_tid) {
	tid = in_tid;
    } else {
	tid = &lcl_tid;
    }

 retry:
    r = mboxlist_mylookup(name, &mbentry, tid, 1);
    switch (r) {
    case 0:
	break;

    case IMAP_AGAIN:
	goto retry;
	break;

    default:
	goto done;
    }

    if((mbentry.mbtype & MBTYPE_REMOTE) && !strchr(mbentry.partition, '!')) {
	syslog(LOG_ERR,
	       "mboxlist_deleteremote called on non-remote mailbox: %s",
	       name);
	goto done;
    }

 retry_del:
    /* delete entry */
    r = DB->delete(mbdb, name, strlen(name), tid, 0);
    switch (r) {
    case CYRUSDB_OK: /* success */
	break;
    case CYRUSDB_AGAIN:
	goto retry_del;
    default:
	syslog(LOG_ERR, "DBERROR: error deleting %s: %s",
	       name, cyrusdb_strerror(r));
	r = IMAP_IOERROR;
    }

    /* commit db operations, but only if we weren't passed a transaction */
    if (!in_tid) {
	r = DB->commit(mbdb, *tid);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: failed on commit: %s",
		   cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	}
	tid = NULL;
    }

 done:
    if(r && !in_tid && tid) {
	/* Abort the transaction if it is still in progress */
	DB->abort(mbdb, *tid);
    }

    return r;
}
	
/*
 * Delayed Delete a mailbox: translate delete into rename
 *
 * XXX local_only?
 */
int
mboxlist_delayed_deletemailbox(const char *name, int isadmin,
			       const char *userid,
			       struct auth_state *auth_state, int checkacl,
			       int local_only __attribute__((unused)),
			       int force)
{
    struct mboxlist_entry mbentry;
    char newname[MAX_MAILBOX_BUFFER];
    int r;
    long myrights;
    char *p;

    if (!isadmin && force) return IMAP_PERMISSION_DENIED;

    /* Check for request to delete a user:
       user.<x> with no dots after it */
    if ((p = mboxname_isusermailbox(name, 1))) {
	/* Can't DELETE INBOX (your own inbox) */
	if (userid) {
	    size_t len = config_virtdomains ?
                strcspn(userid, "@") : strlen(userid);
	    if ((len == strlen(p)) && !strncmp(p, userid, len)) {
		return(IMAP_MAILBOX_NOTSUPPORTED);
	    }
	}

	/* Only admins may delete user */
	if (!isadmin) return(IMAP_PERMISSION_DENIED);
    }

    r = mboxlist_mylookup(name, &mbentry, NULL, 1);
    if (r) return r;

    /* check if user has Delete right (we've already excluded non-admins
     * from deleting a user mailbox) */
    if (checkacl) {
	myrights = cyrus_acl_myrights(auth_state, mbentry.acl);
	if (!(myrights & ACL_DELETEMBOX)) {
	    /* User has admin rights over their own mailbox namespace */
	    if (mboxname_userownsmailbox(userid, name) &&
		(config_implicitrights & ACL_ADMIN)) {
		isadmin = 1;
	    }
	    
	    /* Lie about error if privacy demands */
	    r = (isadmin || (myrights & ACL_LOOKUP)) ?
		IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    return(r);
	}
    }

    /* get the deleted name */
    mboxname_todeleted(name, newname, 1);

    /* Get mboxlist_renamemailbox to do the hard work. No ACL checks needed */
    r = mboxlist_renamemailbox((char *)name, newname, mbentry.partition,
                               1 /* isadmin */, userid,
                               auth_state, force, 1);

    return r;
}

/*
 * Delete a mailbox.
 * Deleting the mailbox user.FOO may only be performed by an admin.
 *
 * 1. Begin transaction
 * 2. Verify ACL's
 * 3. remove from database
 * 4. remove from disk
 * 5. commit transaction
 * 6. Open mupdate connection if necessary
 * 7. delete from mupdate
 *
 */
int mboxlist_deletemailbox(const char *name, int isadmin,
			   const char *userid,
			   struct auth_state *auth_state, int checkacl,
			   int local_only, int force)
{
    struct mboxlist_entry mbentry;
    int r;
    long myrights;
    struct mailbox *mailbox = NULL;
    int isremote = 0;
    const char *p;
    mupdate_handle *mupdate_h = NULL;

    if (!isadmin && force) return IMAP_PERMISSION_DENIED;

    /* Check for request to delete a user:
       user.<x> with no dots after it */
    if ((p = mboxname_isusermailbox(name, 1))) {
	/* Can't DELETE INBOX (your own inbox) */
	if (userid) {
	    size_t len = config_virtdomains ? strcspn(userid, "@") : strlen(userid);
	    if ((len == strlen(p)) && !strncmp(p, userid, len)) {
		r = IMAP_MAILBOX_NOTSUPPORTED;
		goto done;
	    }
	}

	/* Only admins may delete user */
	if (!isadmin) { r = IMAP_PERMISSION_DENIED; goto done; }
    }

    r = mboxlist_mylookup(name, &mbentry, NULL, 1);
    if (r) goto done;

    isremote = mbentry.mbtype & MBTYPE_REMOTE;

    /* check if user has Delete right (we've already excluded non-admins
     * from deleting a user mailbox) */
    if (checkacl) {
	myrights = cyrus_acl_myrights(auth_state, mbentry.acl);
	if(!(myrights & ACL_DELETEMBOX)) {
	    /* User has admin rights over their own mailbox namespace */
	    if (mboxname_userownsmailbox(userid, name) &&
		(config_implicitrights & ACL_ADMIN)) {
		isadmin = 1;
	    }
	    
	    /* Lie about error if privacy demands */
	    r = (isadmin || (myrights & ACL_LOOKUP)) ?
		IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    goto done;
	}
    }

    /* Lock the mailbox if it isn't a remote mailbox */
    if (!isremote) {
	r = mailbox_open_iwl(name, &mailbox);
    }
    if (r && !force) goto done;

    /* remove from mupdate */
    if (!isremote && !local_only && config_mupdate_server) {
	/* delete the mailbox in MUPDATE */
	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if (r) {
	    syslog(LOG_ERR,
		   "cannot connect to mupdate server for delete of '%s'",
		   name);
	    goto done;
	}
	r = mupdate_delete(mupdate_h, name);
	if(r) {
	    syslog(LOG_ERR,
		   "MUPDATE: can't delete mailbox entry '%s'", name);
	}
	if (mupdate_h) mupdate_disconnect(&mupdate_h);
    }
    if (r && !force) goto done;

    /* delete entry */
    r = DB->delete(mbdb, name, strlen(name), NULL, 0);
    if (r) {
	syslog(LOG_ERR, "DBERROR: error deleting %s: %s",
	       name, cyrusdb_strerror(r));
	r = IMAP_IOERROR;
	if (!force) goto done;
    }
    if (r && !force) goto done;

    /* delete underlying mailbox */
    if (!isremote && mailbox) {
	r = mailbox_delete(&mailbox);
    }
    if (r) goto done;

    /* Clean up annotations */
    r = annotatemore_delete(name);
    if (r) {
	syslog(LOG_ERR,
	       "Failed to delete annotations with mailbox '%s': %s",
	       name, error_message(r));
    }

 done:

    if (mailbox) mailbox_close(&mailbox);

    return r;
}

/*
 * Rename/move a single mailbox (recursive renames are handled at a
 * higher level)
 */
int mboxlist_renamemailbox(const char *oldname, const char *newname, 
			   const char *partition, int isadmin, 
			   const char *userid, struct auth_state *auth_state,
			   int forceuser, int ignorequota)
{
    struct mboxlist_entry mbentry;
    int r;
    long myrights;
    int isusermbox = 0; /* Are we renaming someone's inbox */
    int partitionmove = 0;
    struct mailbox *oldmailbox = NULL;
    struct mailbox *newmailbox = NULL;
    struct txn *tid;
    char *newacl = NULL;
    const char *root = NULL;
    char *newpartition = NULL;
    char *mboxent = NULL;
    char *p;

    mupdate_handle *mupdate_h = NULL;

    r = mailbox_open_iwl(oldname, &oldmailbox);
    if (r) return r;

    myrights = cyrus_acl_myrights(auth_state, oldmailbox->acl);

    /* 2. verify acls */
    /* XXX - handle remote mailbox */
    if (!strcmp(oldname, newname)) {
	char *oldpath = mailbox_datapath(oldmailbox);

	/* Attempt to move mailbox across partition */
	if (!isadmin) {
	    r = IMAP_PERMISSION_DENIED;
	    goto done;
	} else if (!mbentry.partition) {
	    r = IMAP_PARTITION_UNKNOWN;
	    goto done;
	}

	partitionmove = 1;
	/* this is OK because it uses a different static buffer */
	root = config_partitiondir(partition);
	if (!root) {
	    r = IMAP_PARTITION_UNKNOWN;
	    goto done;
	}
	if (!strncmp(root, oldpath, strlen(root)) &&
	    oldpath[strlen(root)] == '/') {
	    /* partitions are the same or share common prefix */
	    r = IMAP_MAILBOX_EXISTS;
	    goto done;
	}
    } else if ((p = mboxname_isusermailbox(oldname, 1))) {
	if (!strncmp(p, userid, config_virtdomains ? strcspn(userid, "@") :
		     strlen(userid))) {
	    /* Special case of renaming inbox */
	    if (!(myrights & ACL_DELETEMBOX)) {
		r = IMAP_PERMISSION_DENIED;
		goto done;
	    }
	    isusermbox = 1;
	} else if ((config_getswitch(IMAPOPT_ALLOWUSERMOVES) &&
		    mboxname_isusermailbox(newname, 1)) ||
		   mboxname_isdeletedmailbox(newname)) {
	    /* Special case of renaming a user */
	    if (!(myrights & ACL_DELETEMBOX) && !isadmin) {
		r = (isadmin || (myrights & ACL_LOOKUP)) ?
		    IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
		goto done;
	    }
	} else {
	    /* Only admins can rename users (INBOX to INBOX) */
	    r = IMAP_MAILBOX_NOTSUPPORTED;
	    goto done;
	}
    } else {
	if (!(myrights & ACL_DELETEMBOX) && !isadmin) {
	    r = (isadmin || (myrights & ACL_LOOKUP)) ?
		IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    goto done;
	}
    }

    /* Check ability to create new mailbox */
    if (!partitionmove) {
	if (mboxname_isusermailbox(newname, 1)) {
	    if ((config_getswitch(IMAPOPT_ALLOWUSERMOVES) &&
		 mboxname_isusermailbox(oldname, 1)) ||
		mboxname_isdeletedmailbox(oldname)) {
		if (!isadmin) {
		    /* Only admins can rename users (INBOX to INBOX) */
		    r = IMAP_MAILBOX_NOTSUPPORTED;
		    goto done;
		}
	    } else {
		/* Even admins can't rename to user's inboxes */
		r = IMAP_MAILBOX_NOTSUPPORTED;
		goto done;
	    }
	}
	r = mboxlist_mycreatemailboxcheck(newname, 0, partition, isadmin, 
					  userid, auth_state, NULL, 
					  &newpartition, 1, 0, forceuser, NULL);
	if (r) goto done;
    }
    else if (partition) {
	newpartition = xstrdup(partition);
    }

    /* Rename the actual mailbox */
    r = mailbox_rename_copy(oldmailbox, newname, newpartition,
			    isusermbox ? userid : NULL, ignorequota,
			    &newmailbox);
    if (r) goto done;

    /* 7a. create new entry */
    mboxent = mboxlist_makeentry(newmailbox->mbtype, newmailbox->part,
				 newmailbox->acl);
    do {
	tid = NULL;
	/* 7b. put it into the db */
	r = DB->store(mbdb, newname, strlen(newname), 
		      mboxent, strlen(mboxent), &tid);

	if (!r && !isusermbox) {
	    /* 4. Delete entry from berkeley db */
	    r = DB->delete(mbdb, oldname, strlen(oldname), &tid, 0);
	}

	switch (r) {
	case 0: /* success */
	    break;
	case CYRUSDB_AGAIN:
	    break;
	default:
	    syslog(LOG_ERR, "DBERROR: error renaming %s %s: %s",
		   oldname, newname, cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	    goto done;
	    break;
	}
    } while (r == CYRUSDB_AGAIN);

    /* 3. Commit transaction */
    r = DB->commit(mbdb, tid);
    tid = NULL;
    if (r) {
	syslog(LOG_ERR, "DBERROR: failed on commit %s %s: %s",
	       oldname, newname, cyrusdb_strerror(r));
	r = IMAP_IOERROR;
	goto done;
    }

    if (config_mupdate_server) {
	/* commit the mailbox in MUPDATE */
	char buf[MAX_PARTITION_LEN + HOSTNAME_SIZE + 2];

	snprintf(buf, sizeof(buf), "%s!%s",
		 config_servername, newpartition);
	
	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if (!partitionmove) {
	    if (!r && !isusermbox)
		r = mupdate_delete(mupdate_h, oldname);
	    if (!r) r = mupdate_reserve(mupdate_h, newname, buf);
	}
	if (!r) r = mupdate_activate(mupdate_h, newname, buf, newacl);
	if (r) {
	    syslog(LOG_ERR,
		   "MUPDATE: can't commit mailbox entry for '%s'",
		   newname);
	}
	if (mupdate_h) mupdate_disconnect(&mupdate_h);
    }

 done: /* Commit or cleanup */
    if (r) {
	/* XXX - rollback DB changes if it was an mupdate failure */
	if (newmailbox) mailbox_delete(&newmailbox);
	if (oldmailbox) mailbox_close(&oldmailbox);
    } else {
	mailbox_close(&newmailbox);
	mailbox_rename_cleanup(&oldmailbox, isusermbox);
	/* log the rename */
	sync_log_mailbox_double(oldname, newname);
    }
    
    /* free memory */
    if (newacl) free(newacl);	/* we're done with the new ACL */
    if (newpartition) free(newpartition);
    if (mboxent) free(mboxent);

    return r;
}

/*
 * Change the ACL for mailbox 'name' so that 'identifier' has the
 * rights enumerated in the string 'rights'.  If 'rights' is the null
 * pointer, removes the ACL entry for 'identifier'.   'isadmin' is
 * nonzero if user is a mailbox admin.  'userid' is the user's login id.
 *
 * 1. Start transaction
 * 2. Check rights
 * 3. Set db entry
 * 4. Change backup copy (cyrus.header)
 * 5. Commit transaction
 * 6. Change mupdate entry 
 *
 */
int mboxlist_setacl(const char *name, const char *identifier,
		    const char *rights, 
		    int isadmin, const char *userid, 
		    struct auth_state *auth_state)
{
    struct mboxlist_entry mbentry;
    int useridlen = strlen(userid), domainlen = 0;
    char *cp, ident[256];
    const char *domain = NULL;
    int r;
    int myrights;
    int mode = ACL_MODE_SET;
    int isusermbox = 0, anyoneuseracl = 1;
    struct mailbox *mailbox;
    int mailbox_open = 0;
    char *newacl = NULL;
    char *mboxent = NULL;
    struct txn *tid = NULL;

    if (config_virtdomains) {
	if ((cp = strchr(userid, '@'))) {
	    useridlen = cp - userid;
	}
	if ((cp = strchr(name, '!'))) {
	    domain = name;
	    domainlen = cp - name + 1;
	}

	/* canonify identifier so it is fully qualified,
	   except for "anonymous", "anyone", the global admin
	   and users in the default domain */
	if ((cp = strchr(identifier, '@'))) {
	    if (rights &&
		((domain && strncasecmp(cp+1, domain, strlen(cp+1))) ||
		 (!domain && (!config_defdomain ||
			      strcasecmp(config_defdomain, cp+1))))) {
		/* can't set cross-domain ACLs */
		return IMAP_INVALID_IDENTIFIER;
	    }
	    if ((config_defdomain && !strcasecmp(config_defdomain, cp+1)) ||
		!strcmp(identifier, "anonymous") ||
		!strcmp(identifier, "anyone")) {
		snprintf(ident, sizeof(ident),
			 "%.*s", (int) (cp - identifier), identifier);
	    } else {
		strlcpy(ident, identifier, sizeof(ident));
	    }
	} else {
	    strlcpy(ident, identifier, sizeof(ident));
	    if (domain && !isadmin &&
		strcmp(ident, "anonymous") && strcmp(ident, "anyone")) {
		snprintf(ident+strlen(ident), sizeof(ident)-strlen(ident),
			 "@%.*s",
			 domainlen ? domainlen-1 : (int) strlen(domain), domain);
	    }
	}

	identifier = ident;
    }

    if (!strncmp(name+domainlen, "user.", 5) &&
	(!(cp = strchr(userid, '.')) || (cp - userid) > useridlen) &&
	!strncmp(name+domainlen+5, userid, useridlen) &&
	(name[domainlen+5+useridlen] == '\0' ||
	 name[domainlen+5+useridlen] == '.')) {
	isusermbox = 1;
    }
    anyoneuseracl = config_getswitch(IMAPOPT_ANYONEUSERACL);

    /* 1. Start Transaction */
    /* lookup the mailbox to make sure it exists and get its acl */
    do {
	r = mboxlist_mylookup(name, &mbentry, &tid, 1);
    } while(r == IMAP_AGAIN);

    /* Can't do this to an in-transit or reserved mailbox */
    if(!r && mbentry.mbtype & (MBTYPE_MOVING | MBTYPE_RESERVE)) {
	r = IMAP_MAILBOX_NOTSUPPORTED;
    }

    /* if it is not a remote mailbox, we need to unlock the mailbox list,
     * lock the mailbox, and re-lock the mailboxes list */
    /* we must do this to obey our locking rules */
    if (!r && !(mbentry.mbtype & MBTYPE_REMOTE)) {
	DB->abort(mbdb, tid);
	tid = NULL;

	/* open & lock mailbox header */
        r = mailbox_open_iwl(name, &mailbox);

	if (!r) {
	    mailbox_open = 1;
	    do {
		/* lookup the mailbox to make sure it exists and get its acl */
		r = mboxlist_mylookup(name, &mbentry, &tid, 1);
	    } while( r == IMAP_AGAIN );
	}

	if(r) goto done;
    }

    /* 2. Check Rights */
    if (!r && !isadmin) {
	myrights = cyrus_acl_myrights(auth_state, mbentry.acl);
	if (!(myrights & ACL_ADMIN)) {
	    r = (myrights & ACL_LOOKUP) ?
		IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    goto done;
	}
    }

    /* 2.1 Only admin user can set 'anyone' rights if config says so */
    if (!r && !isadmin && !anyoneuseracl && !strncmp(identifier, "anyone", 6)) {
      r = IMAP_PERMISSION_DENIED;
      goto done;
    }

    /* 3. Set DB Entry */
    if(!r) {
	/* Make change to ACL */
	newacl = xstrdup(mbentry.acl);
	if (rights && *rights) {
	    /* rights are present and non-empty */
	    mode = ACL_MODE_SET;
	    if (*rights == '+') {
		rights++;
		mode = ACL_MODE_ADD;
	    }
	    else if (*rights == '-') {
		rights++;
		mode = ACL_MODE_REMOVE;
	    }
	    
	    if (cyrus_acl_set(&newacl, identifier, mode,
			      cyrus_acl_strtomask(rights),
			      isusermbox ? mboxlist_ensureOwnerRights : 0,
			      (void *)userid)) {
		r = IMAP_INVALID_IDENTIFIER;
	    }
	} else {
	    if (cyrus_acl_remove(&newacl, identifier,
				 isusermbox ? mboxlist_ensureOwnerRights : 0,
				 (void *)userid)) {
		r = IMAP_INVALID_IDENTIFIER;
	    }
	}
    }

    if(!r) {
	/* ok, change the database */
	mboxent = mboxlist_makeentry(mbentry.mbtype, mbentry.partition, newacl);

	do {
	    r = DB->store(mbdb, name, strlen(name),
			  mboxent, strlen(mboxent), &tid);
	} while(r == CYRUSDB_AGAIN);
    
	if(r) {
	    syslog(LOG_ERR, "DBERROR: error updating acl %s: %s",
		   name, cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	}
    }

    /* 4. Change backup copy (cyrus.header) */
    /* we already have it locked from above */
    if (!r && !(mbentry.mbtype & MBTYPE_REMOTE)) {
	mailbox_set_acl(mailbox, newacl);
	r = mailbox_commit(mailbox);
    }

    /* 5. Commit transaction */
    if (!r) {
	if((r = DB->commit(mbdb, tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: failed on commit: %s",
		   cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	}
	tid = NULL;
    }

    /* 6. Change mupdate entry  */
    if (!r && config_mupdate_server) {
        mupdate_handle *mupdate_h = NULL;
	/* commit the update to MUPDATE */
	char buf[MAX_PARTITION_LEN + HOSTNAME_SIZE + 2];

	snprintf(buf, sizeof(buf), "%s!%s", config_servername, mbentry.partition);

	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if(r) {
	    syslog(LOG_ERR,
		   "cannot connect to mupdate server for setacl on '%s'",
		   name);
	} else {
	    r = mupdate_activate(mupdate_h, name, buf, newacl);
	    if(r) {
		syslog(LOG_ERR,
		       "MUPDATE: can't update mailbox entry for '%s'",
		       name);
	    }
	}
	mupdate_disconnect(&mupdate_h);
    }

  done:
    if (r && tid) {
	/* if we are mid-transaction, abort it! */
	int r2 = DB->abort(mbdb, tid);
	if(r2) {
	    syslog(LOG_ERR,
		   "DBERROR: error aborting txn in mboxlist_setacl: %s",
		   cyrusdb_strerror(r2));
	}
    }
    if (mailbox_open) mailbox_close(&mailbox);
    if (mboxent) free(mboxent);
    if (newacl) free(newacl);

    return r;
}

/*
 * Change the ACL for mailbox 'name'.  We already have it locked
 * and have written the backup copy to the header, so there's
 * nothing left but to write the mailboxes.db.
 *
 * 1. Start transaction
 * 2. Set db entry
 * 3. Commit transaction
 * 4. Change mupdate entry 
 *
 */
int
mboxlist_sync_setacls(const char *name, const char *newacl)
{
    struct mboxlist_entry mbentry;
    int r;
    struct txn *tid = NULL;

    /* 1. Start Transaction */
    /* lookup the mailbox to make sure it exists and get its acl */
    do {
	r = mboxlist_mylookup(name, &mbentry, &tid, 1);
    } while(r == IMAP_AGAIN);    

    /* Can't do this to an in-transit or reserved mailbox */
    if (!r && mbentry.mbtype & (MBTYPE_MOVING | MBTYPE_RESERVE)) {
	r = IMAP_MAILBOX_NOTSUPPORTED;
    }

    /* 2. Set DB Entry */
    if (!r) {
	/* ok, change the database */
	char *mboxent = mboxlist_makeentry(mbentry.mbtype,
					   mbentry.partition, newacl);

	do {
	    r = DB->store(mbdb, name, strlen(name),
			  mboxent, strlen(mboxent), &tid);
	} while (r == CYRUSDB_AGAIN);
    
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error updating acl %s: %s",
		   name, cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	}

	free(mboxent);
    }

    /* 3. Commit transaction */
    if (!r) {
	r = DB->commit(mbdb, tid);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: failed on commit %s: %s",
		   name, cyrusdb_strerror(r));
	    r = IMAP_IOERROR;
	}
	tid = NULL;
    }

    /* 4. Change mupdate entry  */
    if (!r && config_mupdate_server) {
        mupdate_handle *mupdate_h = NULL;
	/* commit the update to MUPDATE */
	char buf[MAX_PARTITION_LEN + HOSTNAME_SIZE + 2];
	sprintf(buf, "%s!%s", config_servername, mbentry.partition);

	r = mupdate_connect(config_mupdate_server, NULL, &mupdate_h, NULL);
	if(r) {
	    syslog(LOG_ERR,
		   "cannot connect to mupdate server for syncacl on '%s'",
		   name);
	} else {
	    r = mupdate_activate(mupdate_h, name, buf, newacl);
	    if(r) {
		syslog(LOG_ERR,
		       "MUPDATE: can't update mailbox entry for '%s'",
		       name);
	    }
	}
	mupdate_disconnect(&mupdate_h);
    }

    if (r && tid) {
	/* if we are mid-transaction, abort it! */
	int r2 = DB->abort(mbdb, tid);
	if (r2) {
	    syslog(LOG_ERR,
		   "DBERROR: error aborting txn in sync_setacls %s: %s",
		   name, cyrusdb_strerror(r2));
	}
    }

    return r;
}

struct find_rock {
    struct glob *g;
    struct namespace *namespace;
    int find_namespace;
    int domainlen;
    int inboxoffset;
    const char *inboxcase;
    const char *usermboxname;
    int usermboxnamelen;
    int checkmboxlist;
    int checkshared;
    int isadmin;
    struct auth_state *auth_state;
    int (*proc)(char *, int, int, void *rock);
    void *procrock;
};

/* return non-zero if we like this one */
static int find_p(void *rockp, 
		  const char *key, int keylen,
		  const char *data, int datalen)
{
    struct find_rock *rock = (struct find_rock *) rockp;
    long minmatch;
    struct glob *g = rock->g;
    long matchlen;

    /* don't list mailboxes outside of the default domain */
    if (!rock->domainlen && !rock->isadmin && memchr(key, '!', keylen)) return 0; 

    minmatch = 0;
    if (rock->inboxoffset) {
	char namebuf[MAX_MAILBOX_BUFFER];

	if(keylen >= (int) sizeof(namebuf)) {
	    syslog(LOG_ERR, "oversize keylen in mboxlist.c:find_p()");
	    return 0;
	}
	memcpy(namebuf, key, keylen);
	namebuf[keylen] = '\0';
	
	if (rock->inboxoffset) {
	    namebuf[rock->inboxoffset] = rock->inboxcase[0];
	    namebuf[rock->inboxoffset+1] = rock->inboxcase[1];
	    namebuf[rock->inboxoffset+2] = rock->inboxcase[2];
	    namebuf[rock->inboxoffset+3] = rock->inboxcase[3];
	    namebuf[rock->inboxoffset+4] = rock->inboxcase[4];
	}
	
	matchlen = glob_test(g, namebuf+rock->inboxoffset,
			     keylen-rock->inboxoffset, &minmatch);
    } else {
	matchlen = glob_test(g, key, keylen, &minmatch);
    }

    /* If its not a match, skip it -- partial matches are ok. */
    if(matchlen == -1) return 0;

    if (rock->find_namespace != NAMESPACE_INBOX &&
	rock->usermboxname &&
	keylen >= rock->usermboxnamelen &&
	(keylen == rock->usermboxnamelen || 
	 key[rock->usermboxnamelen] == '.') &&
	!strncmp(key, rock->usermboxname, rock->usermboxnamelen)) {
	/* this would've been output with the inbox stuff, so skip it */
	return 0;
    }

    if (rock->find_namespace == NAMESPACE_SHARED &&
	rock->namespace && rock->namespace->isalt &&
	!strncmp(key+rock->domainlen, "user", 4) &&
	(key[rock->domainlen+4] == '\0' || key[rock->domainlen+4] == '.')) {
	/* this would've been output with the user stuff, so skip it */
	return 0;
    }

    /* Suppress deleted hierarchy unless admin: overrides ACL_LOOKUP test */
    if (!rock->isadmin) {
	char namebuf[MAX_MAILBOX_BUFFER];

	memcpy(namebuf, key, keylen);
	namebuf[keylen] = '\0';
	if (mboxlist_delayed_delete_isenabled() && 
	    mboxname_isdeletedmailbox(namebuf))
	    return 0;
    }


    /* check acl */
    if (!rock->isadmin) {
	/* check the acls */
	const char *p, *acl;
	int rights;
	int acllen;
	static char *aclbuf = NULL;
	static int aclbufsz = 0;

	p = strchr(data, ' ');
	if (!p) {
	    syslog(LOG_ERR, "%s: can't find partition", key);
	    return 0;
	}
	p++;
	acl = strchr(p, ' ');
	if (!acl) {
	    syslog(LOG_ERR, "%s: can't find acl", key);
	    return 0;
	}
	acl++;
	acllen = datalen - (acl - data);
	if (acllen >= aclbufsz) {
	    aclbufsz = acllen + 500;
	    aclbuf = xrealloc(aclbuf, aclbufsz);
	}
	memcpy(aclbuf, acl, acllen);
	aclbuf[acllen] = '\0';

	rights = cyrus_acl_myrights(rock->auth_state, aclbuf);
	if (!(rights & ACL_LOOKUP)) {
	    return 0;
	}
    }
    
    /* if we get here, close enough for us to spend the time
       acting interested */
    return 1;
}

static int find_cb(void *rockp, 
		   const char *key, int keylen,
		   const char *data __attribute__((unused)),
		   int datalen __attribute__((unused)))
{
    char namebuf[MAX_MAILBOX_BUFFER];
    struct find_rock *rock = (struct find_rock *) rockp;
    int r = 0;
    long minmatch;
    struct glob *g = rock->g;

    /* foreach match, do this test */
    minmatch = 0;
    while (minmatch >= 0) {
	long matchlen;
	
	if(keylen >= (int) sizeof(namebuf)) {
	    syslog(LOG_ERR, "oversize keylen in mboxlist.c:find_cb()");
	    return 0;
	}
	memcpy(namebuf, key, keylen);
	namebuf[keylen] = '\0';
	
	if (rock->find_namespace != NAMESPACE_INBOX &&
	    rock->usermboxname &&
	    !strncmp(namebuf, rock->usermboxname, rock->usermboxnamelen)
	    && (keylen == rock->usermboxnamelen || 
		namebuf[rock->usermboxnamelen] == '.')) {
	    /* this would've been output with the inbox stuff, so skip it */
	    return 0;
	}

      	/* make sure it's in the mailboxes db */
	if (rock->checkmboxlist) {
	    r = mboxlist_lookup(namebuf, NULL, NULL);
	} else {
	    r = 0;		/* don't bother checking */
	}

	if (!r && rock->inboxoffset) {
	    namebuf[rock->inboxoffset] = rock->inboxcase[0];
	    namebuf[rock->inboxoffset+1] = rock->inboxcase[1];
	    namebuf[rock->inboxoffset+2] = rock->inboxcase[2];
	    namebuf[rock->inboxoffset+3] = rock->inboxcase[3];
	    namebuf[rock->inboxoffset+4] = rock->inboxcase[4];
	}
	
	matchlen = glob_test(g, namebuf+rock->inboxoffset,
			     keylen-rock->inboxoffset, &minmatch);

	if (matchlen == -1) {
	    r = 0;
	    break;
	}

	switch (r) {
	case 0:
	    /* found the entry; output it */
	    if (rock->find_namespace == NAMESPACE_SHARED &&
		rock->checkshared && rock->namespace) {
		/* special case:  LIST "" *% -- output prefix */
		r = (*rock->proc)(rock->namespace->prefix[NAMESPACE_SHARED],
				  strlen(rock->namespace->prefix[NAMESPACE_SHARED])-1,
				  1, rock->procrock);

		if (rock->checkshared > 1) {
		    /* special case:  LIST "" % -- output prefix only */
		    /* short-circuit the foreach - one mailbox is sufficient */
		    return CYRUSDB_DONE;
		}
	    }

	    rock->checkshared = 0;
	    r = (*rock->proc)(namebuf+rock->inboxoffset, matchlen, 
			      1, rock->procrock);

	    break;
	    
	case IMAP_MAILBOX_NONEXISTENT:
	    /* didn't find the entry */
	    r = 0;
	    break;

	default:
	    break;
	}

	if (r) break;
    }

    return r;
}

/*
 * Find all mailboxes that match 'pattern'.
 * 'isadmin' is nonzero if user is a mailbox admin.  'userid'
 * is the user's login id.  For each matching mailbox, calls
 * 'proc' with the name of the mailbox.  If 'proc' ever returns
 * a nonzero value, mboxlist_findall immediately stops searching
 * and returns that value.  'rock' is passed along as an argument to proc in
 * case it wants some persistant storage or extra data.
 */
/* Find all mailboxes that match 'pattern'. */
int mboxlist_findall(struct namespace *namespace __attribute__((unused)),
		     const char *pattern, int isadmin, const char *userid, 
		     struct auth_state *auth_state, int (*proc)(), void *rock)
{
    struct find_rock cbrock;
    char usermboxname[MAX_MAILBOX_BUFFER];
    int usermboxnamelen = 0;
    const char *data;
    int datalen;
    int r = 0;
    char *p;
    int prefixlen;
    int userlen = userid ? strlen(userid) : 0, domainlen = 0;
    char domainpat[MAX_MAILBOX_BUFFER] = ""; /* do intra-domain fetches only */
    char *pat = NULL;

    if (config_virtdomains) {
	char *domain;

	if (userid && (domain = strrchr(userid, '@'))) {
	    userlen = domain - userid;
	    domainlen = strlen(domain); /* includes separator */

	    if ((p = strchr(pattern , '!'))) {
		if ((p-pattern != domainlen-1) ||
		    strncmp(pattern, domain+1, domainlen-1)) {
		    /* don't allow cross-domain access */
		    return IMAP_MAILBOX_BADNAME;
		}

		pattern = p+1;
	    }

	    snprintf(domainpat, sizeof(domainpat), "%s!%s", domain+1, pattern);
	}
	if ((p = strrchr(pattern, '@'))) {
	    /* global admin specified mbox@domain */
	    if (domainlen) {
		/* can't do both user@domain and mbox@domain */
		return IMAP_MAILBOX_BADNAME;
	    }

	    /* don't prepend default domain */
	    if (!(config_defdomain && !strcasecmp(config_defdomain, p+1))) {
		snprintf(domainpat, sizeof(domainpat), "%s!", p+1);
		domainlen = strlen(p);
	    }
	    snprintf(domainpat+domainlen, sizeof(domainpat)-domainlen,
		     "%.*s", (int) (p - pattern), pattern);
	}
    }

    if (domainpat[0] == '\0')
	strlcpy(domainpat, pattern, sizeof(domainpat));

    cbrock.g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    cbrock.namespace = NULL;
    cbrock.domainlen = domainlen;
    cbrock.inboxcase = glob_inboxcase(cbrock.g);
    cbrock.isadmin = isadmin;
    cbrock.auth_state = auth_state;
    cbrock.checkmboxlist = 0;	/* don't duplicate work */
    cbrock.checkshared = 0;
    cbrock.proc = proc;
    cbrock.procrock = rock;

    /* Build usermboxname */
    if (userid && (!(p = strchr(userid, '.')) || ((p - userid) > userlen)) &&
	strlen(userid)+5 < MAX_MAILBOX_BUFFER) {
	if (domainlen)
	    snprintf(usermboxname, sizeof(usermboxname),
		     "%s!", userid+userlen+1);
	snprintf(usermboxname+domainlen, sizeof(usermboxname)-domainlen,
		 "user.%.*s", userlen, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = NULL;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(cbrock.g, "INBOX") != -1) {
	    r = DB->fetch(mbdb, usermboxname, usermboxnamelen,
			  &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(cbrock.inboxcase, 5, 1, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}
	else if (!strncmp(pattern,
			  usermboxname+domainlen, usermboxnamelen-domainlen) &&
		 GLOB_TEST(cbrock.g, usermboxname+domainlen) != -1) {
	    r = DB->fetch(mbdb, usermboxname, usermboxnamelen,
			  &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(usermboxname, usermboxnamelen, 1, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}
	strlcat(usermboxname, ".", sizeof(usermboxname));
	usermboxnamelen++;

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    } else {
	cbrock.usermboxname = NULL;
	cbrock.usermboxnamelen = 0;
    }

    if (r) goto done;

    /* Make a working copy of pattern */
    pattern = pat = xstrdup(pattern);

    /* Find fixed-string pattern prefix */
    for (p = pat; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?' || *p == '@') break;
    }
    prefixlen = p - pattern;
    *p = '\0';

    /*
     * If user.X.* or INBOX.* can match pattern,
     * search for those mailboxes next
     */
    if (userid &&
	(!strncmp(usermboxname+domainlen, pattern, usermboxnamelen-domainlen-1) ||
	 !strncasecmp("inbox.", pattern, prefixlen < 6 ? prefixlen : 6))) {

	if (!strncmp(usermboxname+domainlen, pattern, usermboxnamelen-domainlen-1)) {
	    /* switch to pattern with domain prepended */
	    glob_free(&cbrock.g);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	    cbrock.inboxoffset = 0;
	}
	else {
	    cbrock.inboxoffset = domainlen + userlen;
	}

	cbrock.find_namespace = NAMESPACE_INBOX;
	/* iterate through prefixes matching usermboxname */
	r = DB->foreach(mbdb,
			usermboxname, usermboxnamelen,
			&find_p, &find_cb, &cbrock,
			NULL);
    }

    if(!r) {
	cbrock.find_namespace = NAMESPACE_USER;
	/* switch to pattern with domain prepended */
	glob_free(&cbrock.g);
	cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	cbrock.inboxoffset = 0;
	if (usermboxnamelen) {
	    usermboxname[--usermboxnamelen] = '\0';
	    cbrock.usermboxname = usermboxname;
	    cbrock.usermboxnamelen = usermboxnamelen;
	}
	/* search for all remaining mailboxes.
	   just bother looking at the ones that have the same pattern
	   prefix. */
	r = DB->foreach(mbdb,
			domainpat, domainlen + prefixlen,
			&find_p, &find_cb, &cbrock,
			NULL);
    }
    

  done:
    glob_free(&cbrock.g);
    if (pat) free(pat);

    return r;
}

int mboxlist_findall_alt(struct namespace *namespace,
			 const char *pattern, int isadmin, const char *userid,
			 struct auth_state *auth_state, int (*proc)(),
			 void *rock)
{
    struct find_rock cbrock;
    char usermboxname[MAX_MAILBOX_BUFFER], patbuf[MAX_MAILBOX_BUFFER];
    int usermboxnamelen = 0;
    const char *data;
    int datalen;
    int r = 0;
    char *p;
    int prefixlen, len;
    int userlen = userid ? strlen(userid) : 0, domainlen = 0;
    char domainpat[MAX_MAILBOX_BUFFER]; /* do intra-domain fetches only */
    char *pat = NULL;

    if (config_virtdomains && userid && (p = strchr(userid, '@'))) {
	userlen = p - userid;
	domainlen = strlen(p); /* includes separator */
	snprintf(domainpat, sizeof(domainpat), "%s!", p+1);
    }
    else
	domainpat[0] = '\0';

    cbrock.g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    cbrock.namespace = namespace;
    cbrock.domainlen = domainlen;
    cbrock.inboxcase = glob_inboxcase(cbrock.g);
    cbrock.isadmin = isadmin;
    cbrock.auth_state = auth_state;
    cbrock.checkmboxlist = 0;	/* don't duplicate work */
    cbrock.checkshared = 0;
    cbrock.proc = proc;
    cbrock.procrock = rock;

    /* Build usermboxname */
    if (userid && (!(p = strchr(userid, '.')) || ((p - userid) > userlen)) &&
	strlen(userid)+5 < MAX_MAILBOX_BUFFER) {
	if (domainlen)
	    snprintf(usermboxname, sizeof(usermboxname),
		     "%s!", userid+userlen+1);
	snprintf(usermboxname+domainlen, sizeof(usermboxname)-domainlen,
		 "user.%.*s", userlen, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = 0;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(cbrock.g, "INBOX") != -1) {
	    r = DB->fetch(mbdb, usermboxname, usermboxnamelen,
			  &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(cbrock.inboxcase, 5, 0, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}

	strlcat(usermboxname, ".", sizeof(usermboxname));
	usermboxnamelen++;

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    } else {
	cbrock.usermboxname = NULL;
	cbrock.usermboxnamelen = 0;
    }

    if (r) goto done;

    glob_free(&cbrock.g);

    /* Make a working copy of pattern */
    pattern = pat = xstrdup(pattern);

    /* Find fixed-string pattern prefix */
    for (p = pat; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?' || *p == '@') break;
    }
    prefixlen = p - pattern;

    /*
     * Personal (INBOX) namespace
     *
     * Append pattern to "INBOX.", search for those mailboxes next
     */
    if (userid) {
	strlcpy(patbuf, "INBOX.", sizeof(patbuf));
	strlcat(patbuf, pattern, sizeof(patbuf));
	cbrock.g = glob_init(patbuf, GLOB_HIERARCHY|GLOB_INBOXCASE);
	cbrock.inboxcase = glob_inboxcase(cbrock.g);
	cbrock.inboxoffset = domainlen+userlen;
	cbrock.find_namespace = NAMESPACE_INBOX;

	/* iterate through prefixes matching usermboxname */
	DB->foreach(mbdb,
		    usermboxname, usermboxnamelen,
		    &find_p, &find_cb, &cbrock,
		    NULL);

	glob_free(&cbrock.g);
    }

    if (usermboxnamelen) {
	usermboxname[--usermboxnamelen] = '\0';
	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    }

    /*
     * Other Users namespace
     *
     * If "Other Users*" can match pattern, search for those mailboxes next
     */
    len = strlen(namespace->prefix[NAMESPACE_USER]);
    if(len>0) len--;

    if (!strncmp(namespace->prefix[NAMESPACE_USER], pattern,
		 prefixlen < len ? prefixlen : len)) {

	if (prefixlen < len) {
	    strlcpy(domainpat+domainlen, pattern+prefixlen,
		    sizeof(domainpat)-domainlen);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	}
	else {
	    strlcpy(domainpat+domainlen, "user", sizeof(domainpat)-domainlen);
	    strlcat(domainpat, pattern+len, sizeof(domainpat));
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	}
	cbrock.find_namespace = NAMESPACE_USER;
	cbrock.inboxoffset = 0;
	
	/* iterate through prefixes matching usermboxname */
	strlcpy(domainpat+domainlen, "user", sizeof(domainpat)-domainlen);
	DB->foreach(mbdb,
		    domainpat, strlen(domainpat),
		    &find_p, &find_cb, &cbrock,
		    NULL);

	glob_free(&cbrock.g);
    }

    /*
     * Shared namespace
     *
     * search for all remaining mailboxes.
     * just bother looking at the ones that have the same pattern prefix.
     */
    len = strlen(namespace->prefix[NAMESPACE_SHARED]);
    if(len>0) len--;
    if (!strncmp(namespace->prefix[NAMESPACE_SHARED], pattern,
		 prefixlen < len ? prefixlen : len)) {

	cbrock.find_namespace = NAMESPACE_SHARED;
	cbrock.inboxoffset = 0;

	if (prefixlen <= len) {
	    /* Skip pattern which matches shared namespace prefix */
	    for (p = pat+prefixlen; *p; p++) {
		if (*p == '%') continue;
		else if (*p == '.') p++;
		break;
	    }

	    if (*pattern && !strchr(pattern, '.') &&
		pattern[strlen(pattern)-1] == '%') {
		/* special case:  LIST "" *% -- output prefix */
  		cbrock.checkshared = 1;
  	    }

	    if ((cbrock.checkshared || prefixlen == len) && !*p) {
		/* special case:  LIST "" % -- output prefix
 		   (if we have a shared mbox) and quit */
		strlcpy(domainpat+domainlen, "*", sizeof(domainpat)-domainlen);
		cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
		cbrock.checkshared = 2;
	    }
	    else {
		strlcpy(domainpat+domainlen, p, sizeof(domainpat)-domainlen);
		cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	    }
		
	    domainpat[domainlen] = '\0';
	    DB->foreach(mbdb,
			domainpat, domainlen,
			&find_p, &find_cb, &cbrock,
			NULL);
	}
	else if (pattern[len] == '.') {
	    strlcpy(domainpat+domainlen, pattern+len+1,
		    sizeof(domainpat)-domainlen);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);

	    DB->foreach(mbdb,
			domainpat, domainlen+prefixlen-(len+1),
			&find_p, &find_cb, &cbrock,
			NULL);
	}
    }

  done:
    glob_free(&cbrock.g);
    if (pat) free(pat);

    return r;
}

static int child_cb(char *name,
		    int matchlen __attribute__((unused)),
		    int maycreate __attribute__((unused)),
		    void *rock)
{
    if (!name) return 0;
    return (*((int *) rock) = 1);
}

/*
 * Set the quota on or create a quota root
 */
int mboxlist_setquota(const char *root, int newquota, int force)
{
    char pattern[MAX_MAILBOX_PATH+1];
    struct quota q;
    int have_mailbox = 1;
    int r;
    struct txn *tid = NULL;
    struct change_rock crock;
    struct mboxlist_entry mbentry;

    if (!root[0] || root[0] == '.' || strchr(root, '/')
	|| strchr(root, '*') || strchr(root, '%') || strchr(root, '?')) {
	return IMAP_MAILBOX_BADNAME;
    }
    
    q.root = root;
    r = quota_read(&q, &tid, 1);

    if (!r) {
	/* unchanged */
	if (q.limit == newquota)
	    return 0;

	/* Just change it */
	q.limit = newquota;
	r = quota_write(&q, &tid);
	if (!r) quota_commit(&tid);
	else quota_abort(&tid);
	goto done;
    }

    if (r != IMAP_QUOTAROOT_NONEXISTENT) goto done;

    /*
     * Have to create a new quota root
     */
    strlcpy(pattern, root, sizeof(pattern));

    if (config_virtdomains && root[strlen(root)-1] == '!') {
	/* domain quota */
	have_mailbox = 0;
	strlcat(pattern, "*", sizeof(pattern));
    }
    else {
	strlcat(pattern, ".*", sizeof(pattern));

	/* look for a top-level mailbox in the proposed quotaroot */
	r = mboxlist_lookup(root, &mbentry, NULL);
	if (r) {
	    if (!force && r == IMAP_MAILBOX_NONEXISTENT) {
		/* look for a child mailbox in the proposed quotaroot */
		 mboxlist_findall(NULL, pattern, 1, NULL, NULL,
				 child_cb, (void *) &force);
	    }

	    /* are we going to force the create anyway? */
	    if (!force) return r;
	    else {
		have_mailbox = 0;
		mbentry.mbtype = 0;
	    }
	}

	if (mbentry.mbtype & (MBTYPE_REMOTE | MBTYPE_MOVING)) {
	    /* Can't set quota on a remote mailbox */
	    r = IMAP_MAILBOX_NOTSUPPORTED;
	    goto done;
	}
    }

    /* initialise the quota */
    q.used = 0;
    q.limit = newquota;

    /* recurse through mailboxes, setting the quota and finding
     * out the usage */
    crock.quota = &q;
    crock.tid = &tid;

    /* top level mailbox */
    if (have_mailbox)
	mboxlist_changequota(q.root, 0, 0, &crock);

    /* submailboxes - we're using internal names here */
    mboxlist_findall(NULL, pattern, 1, 0, 0, mboxlist_changequota, &crock);

    /* write our final value! */
    r = quota_write(&q, &tid);
    if (!r) quota_commit(&tid);
    else quota_abort(&tid);

done:
    if (!r) sync_log_quota(root);

    return r;
}

/*
 *  Remove a quota root
 */
int mboxlist_unsetquota(const char *root)
{
    char pattern[MAX_MAILBOX_PATH+1];
    struct quota q;
    int r=0;

    if (!root[0] || root[0] == '.' || strchr(root, '/')
	|| strchr(root, '*') || strchr(root, '%') || strchr(root, '?')) {
	return IMAP_MAILBOX_BADNAME;
    }
    
    q.root = root;
    r = quota_read(&q, NULL, 0);
    /* already unset */
    if (r == IMAP_QUOTAROOT_NONEXISTENT) return 0;
    if (r) return r;

    /*
     * Have to remove it from all affected mailboxes
     */
    strlcpy(pattern, root, sizeof(pattern));
    if (config_virtdomains && root[strlen(root)-1] == '!') {
	/* domain quota */
	strlcat(pattern, "*", sizeof(pattern));
    }
    else
	strlcat(pattern, ".*", sizeof(pattern));
    
    /* top level mailbox */
    mboxlist_rmquota(root, 0, 0, (void *)root);
    /* submailboxes - we're using internal names here */
    mboxlist_findall(NULL, pattern, 1, 0, 0, mboxlist_rmquota, (void *)root);

    r = quota_deleteroot(root);
    if (!r) sync_log_quota(root);

    return r;
}

/*
 * ACL access canonicalization routine which ensures that 'owner'
 * retains lookup, administer, and create rights over a mailbox.
 */
int mboxlist_ensureOwnerRights(rock, identifier, myrights)
void *rock;
const char *identifier;
int myrights;
{
    char *owner = (char *)rock;
    if (strcmp(identifier, owner) != 0) return myrights;
    return myrights|config_implicitrights;
}

/*
 * Helper function to remove the quota root for 'name'
 */
static int mboxlist_rmquota(const char *name,
			    int matchlen __attribute__((unused)),
			    int maycreate __attribute__((unused)),
			    void *rock)
{
    int r;
    struct mailbox *mailbox;
    const char *oldroot = (const char *) rock;

    assert(rock != NULL);

    r = mailbox_open_iwl(name, &mailbox);
    if (r) goto error_noclose;

    if (mailbox->quotaroot) {
	if (strlen(mailbox->quotaroot) != strlen(oldroot)
	    || strcmp(mailbox->quotaroot, oldroot)) {
	    /* Part of a different quota root */
	    mailbox_close(&mailbox);
	    return 0;
	}

	mailbox_set_quotaroot(mailbox, NULL);

	r = mailbox_commit(mailbox);
	if (r) goto error;
    }

    mailbox_close(&mailbox);
    return 0;

 error:
    mailbox_close(&mailbox);
 error_noclose:
    syslog(LOG_ERR, "LOSTQUOTA: unable to remove quota root %s for %s: %s",
	   oldroot, name, error_message(r));
    
    return 0;
}

/*
 * Helper function to change the quota root for 'name' to that pointed
 * to by the static global struct pointer 'mboxlist_newquota'.
 */
static int mboxlist_changequota(const char *name,
				int matchlen __attribute__((unused)),
				int maycreate __attribute__((unused)),
				void *rock)
{
    int r;
    struct mailbox *mailbox;
    struct change_rock *crock = (struct change_rock *) rock;
    struct quota *newquota = crock->quota;
    struct quota q;
    struct txn **tid = crock->tid;

    assert(rock != NULL);

    r = mailbox_open_iwl(name, &mailbox);
    if (r) goto error_noclose;

    if (mailbox->quotaroot) {
	if (strlen(mailbox->quotaroot) >= strlen(newquota->root)) {
	    /* Part of a child quota root - skip */
	    mailbox_close(&mailbox);
	    return 0;
	}

	/* remove usage from the old quotaroot */
	q.root = mailbox->quotaroot;
	r = quota_read(&q, tid, 1);
	if (r) goto error;
	if (q.used >= mailbox->i.quota_mailbox_used) {
	    q.used -= mailbox->i.quota_mailbox_used;
	}
	else {
	    q.used = 0;
	}

	r = quota_write(&q, tid);
	if (r) {
	    syslog(LOG_ERR,
		   "LOSTQUOTA: unable to record free of " UQUOTA_T_FMT " bytes in quota %s",
		   mailbox->i.quota_mailbox_used, mailbox->quotaroot);
	}
    }

    /* update (or set) the quotaroot */
    mailbox_set_quotaroot(mailbox, newquota->root);
    r = mailbox_commit(mailbox);
    if (r) goto error;

    /* track this mailbox's usage */
    newquota->used += mailbox->i.quota_mailbox_used;

 error:
    mailbox_close(&mailbox);

 error_noclose:
    if (r)
	syslog(LOG_ERR, "LOSTQUOTA: unable to change quota root for %s to %s: %s",
	       name, newquota->root, error_message(r));

    /* Note, we're a callback, and it's not a huge tragedy if we
     * fail, so we don't ever return a failure */
    return 0;
}

/* must be called after cyrus_init */
void mboxlist_init(int myflags)
{
    int r;

    if (myflags & MBOXLIST_SYNC) {
	r = DB->sync();
    }
}

void mboxlist_open(const char *fname)
{
    int ret, flags;
    char *tofree = NULL;

    /* create db file name */
    if (!fname) {
	size_t fname_len = strlen(config_dir)+strlen(FNAME_MBOXLIST)+1;

	tofree = xmalloc(fname_len);
	strlcpy(tofree, config_dir, fname_len);
	strlcat(tofree, FNAME_MBOXLIST, fname_len);

	fname = tofree;
    }

    flags = CYRUSDB_CREATE;
    if (config_getswitch(IMAPOPT_IMPROVED_MBOXLIST_SORT)) {
	flags |= CYRUSDB_MBOXSORT;
    }

    ret = (DB->open)(fname, flags, &mbdb);
    if (ret != 0) {
	syslog(LOG_ERR, "DBERROR: opening %s: %s", fname,
	       cyrusdb_strerror(ret));
	    /* Exiting TEMPFAIL because Sendmail thinks this
	       EC_OSFILE == permanent failure. */
	fatal("can't read mailboxes file", EC_TEMPFAIL);
    }    

    if (tofree) free(tofree);

    mboxlist_dbopen = 1;
}

void mboxlist_close(void)
{
    int r;

    if (mboxlist_dbopen) {
	r = (DB->close)(mbdb);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error closing mailboxes: %s",
		   cyrusdb_strerror(r));
	}
	mboxlist_dbopen = 0;
    }
}

void mboxlist_done(void)
{
    /* DB->done() handled by cyrus_done() */
}

/*
 * Open the subscription list for 'userid'.
 * 
 * On success, returns zero.
 * On failure, returns an error code.
 */
static int
mboxlist_opensubs(const char *userid,
		  struct db **ret)
{
    int r = 0, flags;
    char *subsfname;

    /* Build subscription list filename */
    subsfname = user_hash_subs(userid);

    flags = CYRUSDB_CREATE;
    if (config_getswitch(IMAPOPT_IMPROVED_MBOXLIST_SORT)) {
	flags |= CYRUSDB_MBOXSORT;
    }

    r = (SUBDB->open)(subsfname, flags, ret);
    if (r != CYRUSDB_OK) {
	r = IMAP_IOERROR;
    }
    free(subsfname);

    return r;
}

/*
 * Close a subscription file
 */
static void mboxlist_closesubs(struct db *sub)
{
    (SUBDB->close)(sub);
}

/*
 * Find subscribed mailboxes that match 'pattern'.
 * 'isadmin' is nonzero if user is a mailbox admin.  'userid'
 * is the user's login id.  For each matching mailbox, calls
 * 'proc' with the name of the mailbox.
 */
int mboxlist_findsub(struct namespace *namespace __attribute__((unused)),
		     const char *pattern, int isadmin __attribute__((unused)),
		     const char *userid, struct auth_state *auth_state, 
		     int (*proc)(), void *rock, int force)
{
    struct db *subs = NULL;
    struct find_rock cbrock;
    char usermboxname[MAX_MAILBOX_BUFFER];
    int usermboxnamelen = 0;
    const char *data;
    int datalen;
    int r = 0;
    char *p;
    int prefixlen;
    int userlen = userid ? strlen(userid) : 0, domainlen = 0;
    char domainpat[MAX_MAILBOX_BUFFER]; /* do intra-domain fetches only */
    char *pat = NULL;

    if (config_virtdomains && userid && (p = strchr(userid, '@'))) {
	userlen = p - userid;
	domainlen = strlen(p); /* includes separator */
	snprintf(domainpat, sizeof(domainpat), "%s!%s", p+1, pattern);
    }
    else
	strncpy(domainpat, pattern, sizeof(domainpat));

    cbrock.g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    cbrock.namespace = NULL;
    cbrock.domainlen = domainlen;
    cbrock.inboxcase = glob_inboxcase(cbrock.g);
    cbrock.isadmin = 1;		/* user can always see their subs */
    cbrock.auth_state = auth_state;
    cbrock.checkmboxlist = !force;
    cbrock.checkshared = 0;
    cbrock.proc = proc;
    cbrock.procrock = rock;

    /* open the subscription file that contains the mailboxes the 
       user is subscribed to */
    if ((r = mboxlist_opensubs(userid, &subs)) != 0) {
	goto done;
    }

    /* Build usermboxname */
    if (userid && (!(p = strchr(userid, '.')) || ((p - userid) > userlen)) &&
	strlen(userid)+5 < MAX_MAILBOX_BUFFER) {
	if (domainlen)
	    snprintf(usermboxname, sizeof(usermboxname),
		     "%s!", userid+userlen+1);
	snprintf(usermboxname+domainlen, sizeof(usermboxname)-domainlen,
		 "user.%.*s", userlen, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = 0;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(cbrock.g, "INBOX") != -1) {
	    r = SUBDB->fetch(subs, usermboxname, usermboxnamelen,
			     &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(cbrock.inboxcase, 5, 1, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}
	else if (!strncmp(pattern,
			  usermboxname+domainlen, usermboxnamelen-domainlen) &&
		 GLOB_TEST(cbrock.g, usermboxname+domainlen) != -1) {
	    r = SUBDB->fetch(subs, usermboxname, usermboxnamelen,
			     &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(usermboxname, usermboxnamelen, 1, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}
	strlcat(usermboxname, ".", sizeof(usermboxname));
	usermboxnamelen++;

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    }

    if (r) goto done;

    /* Make a working copy of pattern */
    pattern = pat = xstrdup(pattern);

    /* Find fixed-string pattern prefix */
    for (p = pat; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?' || *p == '@') break;
    }
    prefixlen = p - pattern;
    *p = '\0';

    /*
     * If user.X.* or INBOX.* can match pattern,
     * search for those mailboxes next
     */
    if (userid &&
	(!strncmp(usermboxname+domainlen, pattern, usermboxnamelen-domainlen-1) ||
	 !strncasecmp("inbox.", pattern, prefixlen < 6 ? prefixlen : 6))) {

	if (!strncmp(usermboxname+domainlen, pattern, usermboxnamelen-domainlen-1)) {
	    /* switch to pattern with domain prepended */
	    glob_free(&cbrock.g);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	    cbrock.inboxoffset = 0;
	}
	else {
	    cbrock.inboxoffset = strlen(userid);
	}

	cbrock.find_namespace = NAMESPACE_INBOX;
	/* iterate through prefixes matching usermboxname */
	SUBDB->foreach(subs,
		       usermboxname, usermboxnamelen,
		       &find_p, &find_cb, &cbrock,
		       NULL);

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    } else {
	cbrock.usermboxname = NULL;
	cbrock.usermboxnamelen = 0;
    }

    cbrock.find_namespace = NAMESPACE_USER;
    /* switch to pattern with domain prepended */
    glob_free(&cbrock.g);
    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
    cbrock.inboxoffset = 0;
    if (usermboxnamelen) {
	usermboxname[--usermboxnamelen] = '\0';
	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    }
    /* search for all remaining mailboxes.
       just bother looking at the ones that have the same pattern prefix. */
    SUBDB->foreach(subs, domainpat, domainlen + prefixlen, 
		   &find_p, &find_cb, &cbrock, NULL);

  done:
    if (subs) mboxlist_closesubs(subs);
    glob_free(&cbrock.g);
    if (pat) free(pat);

    return r;
}

int mboxlist_findsub_alt(struct namespace *namespace,
			 const char *pattern, int isadmin __attribute__((unused)),
			 const char *userid, struct auth_state *auth_state, 
			 int (*proc)(), void *rock, int force)
{
    struct db *subs = NULL;
    struct find_rock cbrock;
    char usermboxname[MAX_MAILBOX_BUFFER], patbuf[MAX_MAILBOX_BUFFER];
    int usermboxnamelen = 0;
    const char *data;
    int datalen;
    int r = 0;
    char *p;
    int prefixlen, len;
    int userlen = userid ? strlen(userid) : 0, domainlen = 0;
    char domainpat[MAX_MAILBOX_BUFFER]; /* do intra-domain fetches only */
    char *pat = NULL;

    if (config_virtdomains && userid && (p = strchr(userid, '@'))) {
	userlen = p - userid;
	domainlen = strlen(p); /* includes separator */
	snprintf(domainpat, sizeof(domainpat), "%s!", p+1);
    }
    else
	domainpat[0] = '\0';

    cbrock.g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    cbrock.namespace = namespace;
    cbrock.domainlen = domainlen;
    cbrock.inboxcase = glob_inboxcase(cbrock.g);
    cbrock.isadmin = 1;		/* user can always see their subs */
    cbrock.auth_state = auth_state;
    cbrock.checkmboxlist = !force;
    cbrock.checkshared = 0;
    cbrock.proc = proc;
    cbrock.procrock = rock;

    /* open the subscription file that contains the mailboxes the 
       user is subscribed to */
    if ((r = mboxlist_opensubs(userid, &subs)) != 0) {
	goto done;
    }

    /* Build usermboxname */
    if (userid && (!(p = strchr(userid, '.')) || ((p - userid) > userlen)) &&
	strlen(userid)+5 < MAX_MAILBOX_BUFFER) {
	if (domainlen)
	    snprintf(usermboxname, sizeof(usermboxname),
		     "%s!", userid+userlen+1);
	snprintf(usermboxname+domainlen, sizeof(usermboxname)-domainlen,
		 "user.%.*s", userlen, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = 0;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(cbrock.g, "INBOX") != -1) {
	    r = SUBDB->fetch(subs, usermboxname, usermboxnamelen,
			     &data, &datalen, NULL);
	    if (!r && data) {
		r = (*proc)(cbrock.inboxcase, 5, 0, rock);
	    }
	    else if (r == CYRUSDB_NOTFOUND) r = 0;
	}
	strlcat(usermboxname, ".", sizeof(usermboxname));
	usermboxnamelen++;

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    }

    if (r) goto done;

    glob_free(&cbrock.g);

    /* Make a working copy of pattern */
    pattern = pat = xstrdup(pattern);

    /* Find fixed-string pattern prefix */
    for (p = pat; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?' || *p == '@') break;
    }
    prefixlen = p - pattern;

    /*
     * Personal (INBOX) namespace
     *
     * Append pattern to "INBOX.", search for those subscriptions next
     */
    if (userid) {
	strlcpy(patbuf, "INBOX.", sizeof(patbuf));
	strlcat(patbuf, pattern, sizeof(patbuf));
	cbrock.g = glob_init(patbuf, GLOB_HIERARCHY|GLOB_INBOXCASE);
	cbrock.inboxcase = glob_inboxcase(cbrock.g);
	cbrock.inboxoffset = domainlen+userlen;
	cbrock.find_namespace = NAMESPACE_INBOX;

	/* iterate through prefixes matching usermboxname */
	SUBDB->foreach(subs,
		       usermboxname, usermboxnamelen,
		       &find_p, &find_cb, &cbrock,
		       NULL);

	glob_free(&cbrock.g);

	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    } else {
	cbrock.usermboxname = NULL;
	cbrock.usermboxnamelen = 0;
    }

    if (usermboxnamelen) {
	usermboxname[--usermboxnamelen] = '\0';
	cbrock.usermboxname = usermboxname;
	cbrock.usermboxnamelen = usermboxnamelen;
    }

    /*
     * Other Users namespace
     *
     * If "Other Users*" can match pattern, search for those subscriptions next
     */
    len = strlen(namespace->prefix[NAMESPACE_USER]);
    if(len>0) len--; /* Remove Separator */
    if (!strncmp(namespace->prefix[NAMESPACE_USER], pattern,
		 prefixlen < len ? prefixlen : len)) {

	if (prefixlen < len) {
	    strlcpy(domainpat+domainlen, pattern+prefixlen,
		    sizeof(domainpat)-domainlen);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	}
	else {
	    strlcpy(domainpat+domainlen, "user",
		   sizeof(domainpat)-domainlen);
	    strlcat(domainpat, pattern+len, sizeof(domainpat));
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	}
	cbrock.find_namespace = NAMESPACE_USER;
	cbrock.inboxoffset = 0;
	
	/* iterate through prefixes matching usermboxname */
	strlcpy(domainpat+domainlen, "user", sizeof(domainpat)-domainlen);
	SUBDB->foreach(subs,
		       domainpat, strlen(domainpat),
		       &find_p, &find_cb, &cbrock,
		       NULL);

	glob_free(&cbrock.g);
    }

    /*
     * Shared namespace
     *
     * search for all remaining subscriptions.
     * just bother looking at the ones that have the same pattern prefix.
     */
    len = strlen(namespace->prefix[NAMESPACE_SHARED]);
    if(len>0) len--; /* Remove Separator */
    if (!strncmp(namespace->prefix[NAMESPACE_SHARED], pattern,
		 prefixlen < len ? prefixlen : len)) {

	cbrock.find_namespace = NAMESPACE_SHARED;
	cbrock.inboxoffset = 0;

	if (prefixlen <= len) {
	    /* Skip pattern which matches shared namespace prefix */
	    for (p = pat+prefixlen; *p; p++) {
		if (*p == '%') continue;
		else if (*p == '.') p++;
		break;
	    }

	    if (*pattern && !strchr(pattern, '.') &&
		pattern[strlen(pattern)-1] == '%') {
		/* special case:  LSUB "" *% -- output prefix */
  		cbrock.checkshared = 1;
	    }

	    if ((cbrock.checkshared || prefixlen == len) && !*p) {
		/* special case:  LSUB "" % -- output prefix
		   (if we have a shared mbox) and quit */
		strlcpy(domainpat+domainlen, "*", sizeof(domainpat)-domainlen);
		cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
		cbrock.checkshared = 2;
	    }
	    else {
		strlcpy(domainpat+domainlen, p, sizeof(domainpat)-domainlen);
		cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);
	    }

	    domainpat[domainlen] = '\0';
	    SUBDB->foreach(subs,
			   domainpat, domainlen,
			   &find_p, &find_cb, &cbrock,
			   NULL);
	}
	else if (pattern[len] == '.') {
	    strlcpy(domainpat+domainlen, pattern+len+1,
		    sizeof(domainpat)-domainlen);
	    cbrock.g = glob_init(domainpat, GLOB_HIERARCHY);

	    SUBDB->foreach(subs,
			   domainpat, domainlen+prefixlen-(len+1),
			   &find_p, &find_cb, &cbrock,
			   NULL);
	}
    }

  done:
    if (subs) mboxlist_closesubs(subs);
    glob_free(&cbrock.g);
    if (pat) free(pat);

    return r;
}

/* returns CYRUSDB_NOTFOUND if the folder doesn't exist, and 0 if it does! */
int mboxlist_checksub(const char *name, const char *userid)
{
    int r;
    struct db *subs;
    const char *val;
    int vallen;

    r = mboxlist_opensubs(userid, &subs);

    if (!r) r = SUBDB->fetch(subs, name, strlen(name), &val, &vallen, NULL);

    mboxlist_closesubs(subs);
    return r;
}

/*
 * Change 'user's subscription status for mailbox 'name'.
 * Subscribes if 'add' is nonzero, unsubscribes otherwise.
 * if 'force' is set, force the subscription through even if
 * we don't know about 'name'.
 */
int mboxlist_changesub(const char *name, const char *userid, 
		       struct auth_state *auth_state, int add, int force)
{
    struct mboxlist_entry mbentry;
    int r;
    struct db *subs;
    
    if ((r = mboxlist_opensubs(userid, &subs)) != 0) {
	return r;
    }

    if (add && !force) {
	/* Ensure mailbox exists and can be seen by user */
	if ((r = mboxlist_lookup(name, &mbentry, NULL))!=0) {
	    mboxlist_closesubs(subs);
	    return r;
	}
	if ((cyrus_acl_myrights(auth_state, mbentry.acl) & ACL_LOOKUP) == 0) {
	    mboxlist_closesubs(subs);
	    return IMAP_MAILBOX_NONEXISTENT;
	}
    }

    if (add) {
	r = SUBDB->store(subs, name, strlen(name), "", 0, NULL);
    } else {
	r = SUBDB->delete(subs, name, strlen(name), NULL, 0);
	/* if it didn't exist, that's ok */
	if (r == CYRUSDB_EXISTS) r = CYRUSDB_OK;
    }

    switch (r) {
    case CYRUSDB_OK:
	r = 0;
	break;

    default:
	r = IMAP_IOERROR;
	break;
    }

    sync_log_subscribe(userid, name);
    mboxlist_closesubs(subs);
    return r;
}

/* Transaction Handlers */
int mboxlist_commit(struct txn *tid) 
{
    assert(tid);
    
    return DB->commit(mbdb, tid);
}

int mboxlist_abort(struct txn *tid) 
{
    assert(tid);

    return DB->abort(mbdb, tid);
}

int mboxlist_delayed_delete_isenabled(void)
{
    enum enum_value config_delete_mode = config_getenum(IMAPOPT_DELETE_MODE);

    return(config_delete_mode == IMAP_ENUM_DELETE_MODE_DELAYED);
}

/* Callback used by mboxlist_count_inferiors below */
static int
mboxlist_count_addmbox(char *name __attribute__((unused)),
                       int matchlen __attribute__((unused)),
                       int maycreate __attribute__((unused)),
                       void *rock)
{
    int *count = (int *)rock;

    (*count)++;
    
    return 0;
}

/* Count how many children a mailbox has */
int
mboxlist_count_inferiors(const char *mailboxname, int isadmin,
			 const char *userid, struct auth_state *authstate)
{
    int count = 0;
    char mailboxname2[MAX_MAILBOX_BUFFER];
    char *p;

    strcpy(mailboxname2, mailboxname);
    p = mailboxname2 + strlen(mailboxname2); /* end of mailboxname */
    strcpy(p, ".*");

    mboxlist_findall(NULL, mailboxname2, isadmin, userid,
                     authstate, mboxlist_count_addmbox, &count);

    return(count);
}
