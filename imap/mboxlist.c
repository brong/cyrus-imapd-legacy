/* mboxlist.c -- Mailbox list manipulation routines
 * 
 * Copyright 1998 Carnegie Mellon University
 * 
 * No warranties, either expressed or implied, are made regarding the
 * operation, use, or results of the software.
 *
 * Permission to use, copy, modify and distribute this software and its
 * documentation is hereby granted for non-commercial purposes only
 * provided that this copyright notice appears in all copies and in
 * supporting documentation.
 *
 * Permission is also granted to Internet Service Providers and others
 * entities to use the software for internal purposes.
 *
 * The distribution, modification or sale of a product which uses or is
 * based on the software, in whole or in part, for commercial purposes or
 * benefits requires specific, additional permission from:
 *
 *  Office of Technology Transfer
 *  Carnegie Mellon University
 *  5000 Forbes Avenue
 *  Pittsburgh, PA  15213-3890
 *  (412) 268-4387, fax: (412) 268-7395
 *  tech-transfer@andrew.cmu.edu
 *
 */
/*
 * $Id: mboxlist.c,v 1.94.4.10 1999/10/18 02:47:36 tmartin Exp $
 */

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
#include <time.h>
#include <syslog.h>
#include <com_err.h>

#include <db.h>

extern int errno;

#include "acl.h"
#include "auth.h"
#include "glob.h"
#include "assert.h"
#include "config.h"
#include "map.h"
#include "bsearch.h"
#include "lock.h"
#include "util.h"
#include "retry.h"
#include "mailbox.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "xmalloc.h"

acl_canonproc_t mboxlist_ensureOwnerRights;

static char *listfname;
static DB *mbdb;
static DB_ENV dbenv;
static int list_doingfind = 0;

static int mboxlist_opensubs();
static void mboxlist_closesubs();
static void mboxlist_reopen();
static void mboxlist_badline();
static void mboxlist_parseline();
static int mboxlist_safe_rename();

static struct quota *mboxlist_newquota;
static int mboxlist_changequota();
static int mboxlist_safe_rename();

static char *mboxlist_hash_usersubs(const char *userid);

void mboxlist_open(void);
void mboxlist_init(void);

#define FNAME_MBOXLIST "/mailboxesdb"
#define FNAME_DBDIR "/db"
#define FNAME_USERDIR "/user/"
#define FNAME_SUBSSUFFIX ".sub"

/*
 * Maximum length of partition name.  [xxx probably no longer needed]
 * [config.c has a limit of 70]
 */
#define MAX_PARTITION_LEN 10

struct mbox_entry {
    char name[MAX_MAILBOX_NAME];
    char partition[MAX_PARTITION_LEN];
    char acls[1];
};


/*
 * Check our configuration for consistency, die if there's a problem
 */
void mboxlist_checkconfig()
{
}

/*
 * Lookup 'name' in the mailbox list.
 * The capitalization of 'name' is canonicalized to the way it appears
 * in the mailbox list.
 * If 'path' is non-nil, a pointer to the full pathname of the mailbox
 * is placed in the char * pointed to by it.  If 'acl' is non-nil, a pointer
 * to the mailbox ACL is placed in the char * pointed to by it.
 */
int mboxlist_lookup(const char* name, char** pathp, char** aclp, DB_TXN *tid)
{
    unsigned long offset, len, partitionlen, acllen;
    char optionbuf[MAX_MAILBOX_NAME+1];
    char *partition, *acl;
    const char *root;
    static char pathresult[MAX_MAILBOX_PATH];
    static char *aclresult;
    static int aclresultalloced;
    int r;
    DBT key, data;
    struct mbox_entry *mboxent;

    memset(&data, 0, sizeof(key));

    memset(&key, 0, sizeof(key));
    key.data = (char *) name;
    key.size = strlen(name);

    /* we don't bother with a transaction for this one */
    r = mbdb->get(mbdb, tid, &key, &data, 0);

    switch (r) {
    case 0:
      /* copy out interesting parts */
      mboxent=(struct mbox_entry *) data.data;
      partitionlen=strlen(mboxent->partition);
      acllen=strlen(mboxent->acls);
       
	break;
    case DB_NOTFOUND:
	return IMAP_MAILBOX_NONEXISTENT;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error fetching %s: %s",
	       name, strerror(r));
	return IMAP_IOERROR;
	break;
    }
    mboxent = (struct mbox_entry *) data.data;

    /* construct pathname if requested */
    if (pathp) {
	if (partitionlen > sizeof(optionbuf)-11) {
	    return IMAP_PARTITION_UNKNOWN;
	}
	strcpy(optionbuf, "partition-");
	strcat(optionbuf, mboxent->partition);
	
	root = config_getstring(optionbuf, (char *)0);
	if (!root) {
	    return IMAP_PARTITION_UNKNOWN;
	}
	mailbox_hash_mbox(pathresult, root, name);
	*pathp = pathresult;
    }

    /* return ACL if requested */
    if (aclp) {
	if ((strlen(mboxent->acls) + 1) > aclresultalloced) {
	    aclresultalloced = strlen(mboxent->acls) + 100;
	    aclresult = xrealloc(aclresult, aclresultalloced);
	}
	strcpy(aclresult, mboxent->acls);

	*aclp = aclresult;
    }
    return 0;
}

/*
 * Check/set up for mailbox creation
 */
int
mboxlist_createmailboxcheck(char *name, int format, char *partition, 
			    int isadmin, char *userid, 
			    struct auth_state *auth_state, 
			    char **newacl, char **newpartition,
			    DB_TXN *tid)
{
    int r;
    char *p;
    unsigned long offset;
    char *acl;
    char *defaultacl, *identifier, *rights;
    char parent[MAX_MAILBOX_NAME+1];
    unsigned long parentlen;
    char *parentname, *parentpartition, *parentacl;
    unsigned long parentpartitionlen, parentacllen;
    DBT key, data;
    struct mbox_entry *mboxent;

    /* Check for invalid name/partition */
    if (partition && strlen(partition) > MAX_PARTITION_LEN) {
	return IMAP_PARTITION_UNKNOWN;
    }
    r = mboxname_policycheck(name);
    if (r) return r;

    if (format == MAILBOX_FORMAT_NETNEWS) r = mboxname_netnewscheck(name);
    if (r) return r;

    /* User has admin rights over their own mailbox namespace */
    if (mboxname_userownsmailbox(userid, name)) {
	isadmin = 1;
    }

    /* Check to see if new mailbox exists */

    memset(&data, 0, sizeof(key));

    memset(&key, 0, sizeof(key));
    key.data = (char *) name;
    key.size = strlen(name);

    /* we don't bother with a transaction for this one */
    r = mbdb->get(mbdb, tid, &key, &data, DB_RMW);

    switch (r) {
    case 0:

      mboxent=(struct mbox_entry *) data.data;

      r = IMAP_MAILBOX_EXISTS;
      
      /* Lie about error if privacy demands */
      if (!isadmin) {
	if (!(acl_myrights(auth_state, mboxent->acls) & ACL_LOOKUP)) {
	  r = IMAP_PERMISSION_DENIED;
	}
      }
      return r;       
      break;
    case DB_NOTFOUND:
      break;
    case EAGAIN:
      return EAGAIN;
      break;
    default:
	syslog(LOG_ERR, "DBERROR: error fetching %s: %s",
	       name, strerror(r));
	return IMAP_IOERROR;
	break;
    }

    /* Search for a parent */
    strcpy(parent, name);
    parentlen = 0;
    while ((parentlen==0) && (p = strrchr(parent, '.'))) {
	*p = '\0';
	/* no need to search. we're using a DB! */
	memset(&key, 0, sizeof(key));
	key.data=parent;
	key.size=strlen(parent);
	memset(&data, 0, sizeof(data));

	r = mbdb->get(mbdb, tid, &key, &data, DB_RMW);

	switch (r) {
	case DB_NOTFOUND:	  
	    break;
	case 0:
	  parentlen = strlen(parent);
	  mboxent = data.data;

	  parentname = parent;
	  parentpartition = mboxent->partition;
	  parentpartitionlen = strlen(mboxent->partition);

	  parentacl = mboxent->acls;
	  parentacllen = strlen(mboxent->acls); 
               /* xxx this could be better */
	  break;
	case EAGAIN:
	    return r;
	    break;
	default:
	    syslog(LOG_ERR, "DBERROR: error updating database: %s",
		   name, strerror(r));
	    r = IMAP_IOERROR;	  
	}

    }
    if (parentlen != 0) {
      	/* Copy partition, if not specified */
	if (partition == NULL) {
	    partition = xmalloc(parentpartitionlen + 1);
	    memcpy(partition, parentpartition, parentpartitionlen);
	    partition[parentpartitionlen] = '\0';
	}
	else {
	    partition = xstrdup(partition);
	}

	/* Copy ACL */
	acl = xmalloc(parentacllen + 1);
	memcpy(acl, parentacl, parentacllen);
	acl[parentacllen] = '\0';

	if (!isadmin && !(acl_myrights(auth_state, acl) & ACL_CREATE)) {
	    free(partition);
	    free(acl);
	    return IMAP_PERMISSION_DENIED;
	}

	/* Canonicalize case of parent prefix */
	strncpy(name, parent, strlen(parent));

    } 
    else { /* parentlen == 0 */
	if (!isadmin) {
	    return IMAP_PERMISSION_DENIED;
	}
	
	acl = xstrdup("");
	if (!strncmp(name, "user.", 5)) {
	    if (strchr(name+5, '.')) {
		/* Disallow creating user.X.* when no user.X */
		free(acl);
		return IMAP_PERMISSION_DENIED;
	    }
	    /*
	     * Disallow wildcards in userids with inboxes.
	     * If we allowed them, then the delete-user code
	     * in mboxlist_deletemailbox() could potentially
	     * delete other user's personal mailboxes when applied
	     * to this mailbox
	     */	     
	    if (strchr(name, '*') || strchr(name, '%') || strchr(name, '?')) {
		return IMAP_MAILBOX_BADNAME;
	    }
	    /*
	     * Users by default have all access to their personal mailbox(es),
	     * Nobody else starts with any access to same.
	     */
	    acl_set(&acl, name+5, ACL_MODE_SET, ACL_ALL,
		    (acl_canonproc_t *)0, (void *)0);
	}
	else {
	    defaultacl = identifier = 
	      xstrdup(config_getstring("defaultacl", "anyone lrs"));
	    for (;;) {
		while (*identifier && isspace(*identifier)) identifier++;
		rights = identifier;
		while (*rights && !isspace(*rights)) rights++;
		if (!*rights) break;
		*rights++ = '\0';
		while (*rights && isspace(*rights)) rights++;
		if (!*rights) break;
		p = rights;
		while (*p && !isspace(*p)) p++;
		if (*p) *p++ = '\0';
		acl_set(&acl, identifier, ACL_MODE_SET, acl_strtomask(rights),
			(acl_canonproc_t *)0, (void *)0);
		identifier = p;
	    }
	    free(defaultacl);
	}

	if (!partition) {  
	    partition = (char *)config_defpartition;
	    if (strlen(partition) > MAX_PARTITION_LEN) {
		/* Configuration error */
		fatal("name of default partition is too long", EC_CONFIG);
	    }
	}
	partition = xstrdup(partition);
    }

    if (newpartition) *newpartition = partition;
    else free(partition);
    if (newacl) *newacl = acl;
    else free(acl);

    return 0;
}

/*
 * Create a mailbox
 */
mboxlist_createmailbox(char *name, int format, char *partition, 
		       int isadmin, char *userid, 
		       struct auth_state *auth_state)
{
    int r;
    unsigned long offset, len;
    char *acl;
    char buf2[MAX_MAILBOX_PATH];
    const char *root;
    int newlistfd;
    struct iovec iov[10];
    int n;
    struct mailbox newmailbox;
    DB_TXN *tid;
    DB_TXNMGR *txnp;
    DBT key, keydel, data;
    struct mbox_entry *mboxent=NULL;

    txnp = dbenv.tx_info;

    /* retry the transaction from here */
    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0)
    {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	r=IMAP_IOERROR;
	goto done;
    }

    /* Check ability to create mailbox */
    r = mboxlist_createmailboxcheck(name, format, partition, isadmin, userid,
				    auth_state, &acl, &partition, tid);
    if (r == EAGAIN) {
	goto retry;
    }

    if (r != 0) {
	goto done;
    }

    /* Get partition's path */
    sprintf(buf2, "partition-%s", partition);
    root = config_getstring(buf2, (char *)0);
    if (!root) {
	free(partition);
	free(acl);
	r=IMAP_PARTITION_UNKNOWN;
	goto done;
    }
    if (strlen(root)+strlen(name)+20 > MAX_MAILBOX_PATH) {
	free(partition);
	free(acl);
	r=IMAP_MAILBOX_BADNAME;
	goto done;
    }


    
    /* add the new entry */
    mboxent = (struct mbox_entry *) malloc(sizeof(struct mbox_entry) +
					   strlen(acl));

    memset(mboxent, 0, sizeof(struct mbox_entry)); 
				/* xxx this shouldn't be necessary */

    /* fill in its parameters */
    strcpy(mboxent->name, name);
    strcpy(mboxent->partition, partition);
    strcpy(mboxent->acls, acl);

    memset(&key, 0, sizeof(key));
    key.data = name;
    key.size = strlen(name);

    memset(&data, 0, sizeof(data));
    data.data = mboxent;
    data.size = sizeof(struct mbox_entry) + strlen(acl);

    /* database put */
    r = mbdb->put(mbdb, tid, &key, &data, 0);

    switch (r) {
    case 0:
	break;
    case EAGAIN:
	goto retry;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error updating database: %s",
	       name, strerror(r));
	r = IMAP_IOERROR;
	goto done;
    }

    /* Create new mailbox and move new mailbox list file into place */
    mailbox_hash_mbox(buf2, root, name);
    r = mailbox_create(name, buf2, acl, format, &newmailbox);
    if (r!=0) goto done;
    mailbox_close(&newmailbox);

 done:
    free(mboxent);
    free(partition);
    free(acl);

    if (r!=0)
    {
	txn_abort(tid);
	return r;
    }

    switch (txn_commit(tid)) {
    case 0: 
	break;
    default:
	syslog(LOG_ERR, "DBERROR: failed on commit: %s",
	       strerror(r));
	return IMAP_IOERROR;
    }

    toimsp(name, newmailbox.uidvalidity,
	   "ACLsn", newmailbox.acl, newmailbox.uidvalidity, 0);

    return r;
}
	
/*
 * Delete a mailbox.
 * Deleting the mailbox user.FOO deletes the user "FOO".  It may only be
 * performed by an admin.  The operation removes the user "FOO"'s 
 * subscriptions and all sub-mailboxes of user.FOO
 */
int mboxlist_deletemailbox(name, isadmin, userid, auth_state, checkacl)
char *name;
int isadmin;
char *userid;
struct auth_state *auth_state;
int checkacl;
{
    int r;
    char *acl;
    long access;
    int deleteuser = 0; /* if we are deleting user.<user> */
    unsigned long offset, len;
    char submailboxname[MAX_MAILBOX_NAME+1];
    int newlistfd;
    struct iovec iov[10];
    int n;
    struct mailbox mailbox;
    int delete_quota_root = 0;
    bit32 uidvalidity;
    DB_TXN *tid;
    DB_TXNMGR *txnp = dbenv.tx_info;
    DBT key, data;
    DBC *cursor;


    /* restart transaction place */
    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0) {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	return IMAP_IOERROR;
    }



    /* Check for request to delete a user:
       user.<x> with no dots after it */
    if (!strncmp(name, "user.", 5) && !strchr(name+5, '.')) {
	/* Can't DELETE INBOX (your own inbox) */
	if (!strcmp(name+5, userid)) {
	    return IMAP_MAILBOX_NOTSUPPORTED;
	}

	/* Only admins may delete user */
	if (!isadmin) return IMAP_PERMISSION_DENIED;

	r = mboxlist_lookup(name, (char **)0, &acl, tid);
	if (r) return r;
	
	/* Check ACL before doing anything stupid
	 * We don't have to lie about the error code since we know
	 * the user is an admin.
	 */
	if (!(acl_myrights(auth_state, acl) & ACL_DELETE)) {
	    return IMAP_PERMISSION_DENIED;
	}
	
	deleteuser = 1;

	/* Delete any subscription list file */
	{
	    char *fname;

	    fname = mboxlist_hash_usersubs(name + 5);

	    (void) unlink(fname);
	    free(fname);
	}
    }
    r = mboxlist_lookup(name, (char **)0, &acl, tid);
    if (r!=0) {
	return r;
    }

    /* check if user has Delete right */
    access = acl_myrights(auth_state, acl);
    if (checkacl && !(access & ACL_DELETE)) {

	/* User has admin rights over their own mailbox namespace */
	if (mboxname_userownsmailbox(userid, name))
	{
	    isadmin = 1;
	}

	/* Lie about error if privacy demands */
	return (isadmin || (access & ACL_LOOKUP)) ?
	  IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
    }

    /* delete entry */
    memset(&key, 0, sizeof(key));
    key.data = name;
    key.size = strlen(name);

    r=mbdb->del(mbdb, tid, &key, 0);
    switch(r)
    {
    case 0: /* success */
	break;
    case EAGAIN:
	goto retry;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error deleting %s: %s",
	       name, strerror(r));
	goto done;
	break;
    }


    if (deleteuser==1) {
	int namelen = strlen(name)+1;
	char *endname, *endline;

	strcpy(submailboxname, name);
	strcat(submailboxname, ".");

	/* Delete sub-mailboxes */
	r = mbdb->cursor(mbdb, tid, &cursor, 0);
	if (r != 0) { 
	  goto done;
	}
	
	memset(&data, 0, sizeof(data));
	memset(&key, 0, sizeof(key));
	key.data = submailboxname;
	key.size = strlen(submailboxname);
	
	/* this should start at user.foo */
	r = cursor->c_get(cursor, &key, &data, DB_FIRST);	

	while (r != DB_NOTFOUND) {
	    switch (r) {
	    case 0:
		break;
		
	    case EAGAIN:
		goto retry;
		break;
	    
	    default:
		syslog(LOG_ERR, "DBERROR: error advancing: %s", strerror(r));
		r = IMAP_IOERROR;
		goto done;
	    }

	    /* delete the mailbox */
	    r=mbdb->del(mbdb, tid, &key, 0);
	    switch(r)
	    {
	    case 0: /* success */
	      break;
	    case EAGAIN:
	      goto retry;
	      break;
	    default:
	      /* xxx	      syslog(LOG_ERR, "DBERROR: error deleting %s: %s",
		 name, strerror(r));*/
	      goto done;
	      break;
	    }

	    r = cursor->c_get(cursor, &key, &data, DB_NEXT);
	    /* needs to check if key is a subdataset */
	}
    }

    /*
     * See if we have to remove mailbox's quota root
     *
     * NB: this doesn't catch all cases.  We don't handle removing
     * orphaned quota roots on renaming or when inside the
     * ``if (deleteuser)'' code above.
     */
#if NEEDSTODB
    if (mailbox.quota.root &&
	bsearch_mem(mailbox.quota.root, 1, list_base, list_size, 0, 0) == offset &&
	(list_size <= offset + len + strlen(mailbox.quota.root) ||
	 strncmp(list_base+offset+len, mailbox.quota.root, strlen(mailbox.quota.root)) != 0 ||
	 (list_base[offset+len+strlen(mailbox.quota.root)] != '.' &&
	  list_base[offset+len+strlen(mailbox.quota.root)] != '\t'))) {
	delete_quota_root = 1;
    }
    
    /* Remove the mailbox and move new mailbox list file into place */
    uidvalidity = mailbox.uidvalidity;
    if (!r) r = mailbox_delete(&mailbox, delete_quota_root);
    if (r) {
	close(newlistfd);
	return r;
    }

    if (mboxlist_safe_rename(newlistfname, listfname, newlistfd) == -1) {
	syslog(LOG_ERR, "IOERROR: renaming %s: %m", listfname);
	close(newlistfd);
	/* XXX We're left in an inconsistent state here */
    	return IMAP_IOERROR;
    }

    close(newlistfd);

    toimsp(name, uidvalidity, "RENsn", "", 0, 0);
#endif

  done:
    switch (txn_commit(tid)) {
    case 0:      
	break;
    default:
	syslog(LOG_ERR, "DBERROR: failed on commit: %s",
	       strerror(r));
	return IMAP_IOERROR;
    }

    return 0;
}

/*
 * Rename/move a mailbox
 */
int mboxlist_renamemailbox(oldname, newname, partition, isadmin, userid, auth_state)
char *oldname;
char *newname;
char *partition;
int isadmin;
char *userid;
struct auth_state *auth_state;
{
    int r;
    long access;
    int isusermbox = 0;
    char *oldpath;
    unsigned long oldoffset, oldlen;
    unsigned long newoffset, newlen;
    bit32 olduidvalidity, newuidvalidity;
    char *acl=NULL, *oldacl;
    char buf2[MAX_MAILBOX_PATH];
    const char *root;
    int newlistfd;
    struct iovec iov[10];
    int num_iov;
    int n;
    DB_TXN *tid;
    DB_TXNMGR *txnp = dbenv.tx_info;
    DBT key, data;
    struct mbox_entry *mboxent, *newent=NULL;

    /* we just can't rename if there isn't enough info */
    if (partition && !strcmp(partition, "news")) {
	return IMAP_MAILBOX_NOTSUPPORTED;
    }

    /* place to retry transaction */
    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0) {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	return IMAP_IOERROR;
    }

    /* lookup the mailbox to make sure it exists and get it's acl */
    r = mboxlist_lookup(oldname, &oldpath, &oldacl, tid);

    if (r!=0) {
      goto done;
    }

    /* Check ability to delete old mailbox */
    if (strcmp(oldname, newname) == 0) {
	/* Attempt to move mailbox across partition */
	if (!isadmin || !partition) {	  
	    r=IMAP_MAILBOX_EXISTS;
	    goto done;
	}

	root = config_partitiondir(partition);
	if (!root) {
	    r=IMAP_PARTITION_UNKNOWN;
	    goto done;
	}
	if (!strncmp(root, oldpath, strlen(root)) &&
	    oldpath[strlen(root)] == '/') {
	    /* partitions are the same or share common prefix */
	    r=IMAP_MAILBOX_EXISTS;
	    goto done;
	}
    }
    else if (!strncmp(oldname, "user.", 5) && !strchr(oldname+5, '.')) {
	if (!strcmp(oldname+5, userid)) {
	    /* Special case of renaming inbox */
	    access = acl_myrights(auth_state, oldacl);
	    if (!(access & ACL_DELETE)) {
	      r= IMAP_PERMISSION_DENIED;
	      goto done;
	    }
	    isusermbox = 1;
	}
	else {
	    /* Even admins can't rename users */
	    r=IMAP_MAILBOX_NOTSUPPORTED;
	    goto done;
	}
    }
    else {
	access = acl_myrights(auth_state, oldacl);
	if (!(access & ACL_DELETE)) {

	    r= (isadmin || (access & ACL_LOOKUP)) ?
	      IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    goto done;
	}
    }

    acl = xstrdup(oldacl);

    /* Check ability to create new mailbox */
    if (strcmp(oldname, newname) != 0) {

	if (!strncmp(newname, "user.", 5) && !strchr(newname+5, '.')) {
	    /* Even admins can't rename to user's inboxes */
	    free(acl);
	    r= IMAP_MAILBOX_NOTSUPPORTED;
	    goto done;
	}
	r = mboxlist_createmailboxcheck(newname, 0, partition, isadmin, userid,
					auth_state, (char **)0, &partition, tid);
	if (r) {
	  /* not allowed to create the new mailbox */
	    free(acl);
	    goto done;
	}
    }

    /* delete old entry */
    memset(&key, 0, sizeof(key));
    key.data=oldname;
    key.size=strlen(oldname);

    r=mbdb->del(mbdb, tid, &key, 0);


    switch(r)
    {
    case 0: /* success */
	break;
    case EAGAIN:
	goto retry;
	break;
    case DB_NOTFOUND:
	syslog(LOG_ERR, "DBERROR: error deleting %s from db (NOT FOUND)",
	       newent->name);
	goto done;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error deleting %s: %s",
	       oldname, strerror(r));
	goto done;
	break;
    }

    /* create new entry */
    newent=xmalloc(sizeof(struct mbox_entry)+strlen(acl));
    memset(newent, 0, sizeof(struct mbox_entry)+strlen(acl));

    strcpy(newent->name, newname);
    strcpy(newent->partition, partition);
    strcpy(newent->acls, acl);

    /* make the keys */
    memset(&key, 0, sizeof(key));
    key.data=newname;
    key.size=strlen(newname);

    memset(&data, 0, sizeof(data));
    data.data=newent;
    data.size=sizeof(struct mbox_entry)+strlen(acl);

    /* put it into the db */
    r=mbdb->put(mbdb, tid, &key, &data, 0);

    switch (r) {
    case 0:
	break;
    case EAGAIN:
	goto retry;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error renaming %s: %s",
	       newent->name, strerror(r));
	r = IMAP_IOERROR;
	goto done;
    }

    /* Get partition's path */
    sprintf(buf2, "partition-%s", partition);

    root = config_getstring(buf2, (char *)0);
    if (!root) {
	free(acl);
	free(partition);
	r = IMAP_PARTITION_UNKNOWN;
	goto done;
    }

    /* Rename the actual mailbox and move new mailbox list file into place */
    mailbox_hash_mbox(buf2, root, newname);

    r = mailbox_rename(oldname, oldpath, oldacl, newname, buf2, isusermbox,
		       &olduidvalidity, &newuidvalidity);

    if (r!=0) {
      goto done;
    }
    /* xxx does this need to be in the critical section??? */
    toimsp(oldname, olduidvalidity, "RENsn", newname, newuidvalidity, 0); 


 done:
    free(newent);
    free(acl);

    if (r!=0)
    {
	txn_abort(tid);
	return r;
    }

    switch (txn_commit(tid)) {
    case 0: 
	break;
    default:
	syslog(LOG_ERR, "DBERROR: failed on commit: %s",
	       strerror(r));
	r = IMAP_IOERROR;
    }
    
    return r;
}

/*
 * Change the ACL for mailbox 'name' so that 'identifier' has the
 * rights enumerated in the string 'rights'.  If 'rights' is the null
 * pointer, removes the ACL entry for 'identifier'.   'isadmin' is
 * nonzero if user is a mailbox admin.  'userid' is the user's login id.
 */
int
mboxlist_setacl(name, identifier, rights, isadmin, userid, auth_state)
char *name;
char *identifier;
char *rights;
int isadmin;
char *userid;
struct auth_state *auth_state;
{
    int useridlen = strlen(userid);
    int r;
    int access;
    int mode = ACL_MODE_SET;
    int isusermbox = 0;
    struct mailbox mailbox;
    unsigned long offset, len;
    char *oldacl, *acl, *newacl;
    char *path;
    unsigned long oldacllen;
    int newlistfd;
    struct iovec iov[10];
    int n;
    bit32 uidvalidity, timestamp;
    DB_TXN *tid;
    DB_TXNMGR *txnp = dbenv.tx_info;
    DBT key, data;
    struct mbox_entry *oldent, *newent=NULL;

    if (!strncmp(name, "user.", 5) &&
	!strchr(userid, '.') &&
	!strncmp(name+5, userid, useridlen) &&
	(name[5+useridlen] == '\0' || name[5+useridlen] == '.')) {
	isusermbox = 1;
    }

    /* transaction retry point */
    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0) {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	return IMAP_IOERROR;
    }

    /* Get old ACL */
    r = mboxlist_lookup(name, &path, &oldacl, tid);

    memset(&data, 0, sizeof(data));
    memset(&key, 0, sizeof(key));
    key.data = (char *) name;
    key.size = strlen(name);
    
    /* xxx this is really stupid!!! we're doing a second get */
    if (r==0)
      r = mbdb->get(mbdb, tid, &key, &data, 0);

    switch (r) {
    case 0:
      oldent= (struct mbox_entry *) data.data;      
      break;
    case DB_NOTFOUND:
      r = IMAP_MAILBOX_NONEXISTENT;
      break;
    case EAGAIN:
	goto retry;
    default:
	syslog(LOG_ERR, "DBERROR: error fetching %s: %s",
	       name, strerror(r));
	r = IMAP_IOERROR;
    }

    if (!r && !isadmin && !isusermbox) {
	access = acl_myrights(auth_state, oldacl);
	if (!(access & ACL_ADMIN)) {
	    r = (access & ACL_LOOKUP) ?
	      IMAP_PERMISSION_DENIED : IMAP_MAILBOX_NONEXISTENT;
	    goto done;
	}
    }

    /* Open & lock  mailbox header */
    r = mailbox_open_header_path(name, path, oldacl, auth_state, &mailbox, 0);
    if (r) {
      goto done;
    }
    r = mailbox_lock_header(&mailbox);
    if (r) {
      goto done;
    }

    /* Make change to ACL */
    newacl = xstrdup(oldacl);
    if (rights) {
	if (*rights == '+') {
	    rights++;
	    mode = ACL_MODE_ADD;
	}
	else if (*rights == '-') {
	    rights++;
	    mode = ACL_MODE_REMOVE;
	}
	
	if (acl_set(&newacl, identifier, mode, acl_strtomask(rights),
		    isusermbox ? mboxlist_ensureOwnerRights : 0,
		    (void *)userid)) {
	    mailbox_close(&mailbox);
	    free(newacl);
	    txn_abort(tid);
	    return IMAP_INVALID_IDENTIFIER;
	}
    }
    else {
	if (acl_remove(&newacl, identifier,
		       isusermbox ? mboxlist_ensureOwnerRights : 0,
		       (void *)userid)) {
	    mailbox_close(&mailbox);

	    free(newacl);
	    txn_abort(tid);
	    return IMAP_INVALID_IDENTIFIER;
	}
    }

    /* ok, make the change */
    newent = (struct mbox_entry *) xmalloc(sizeof(struct mbox_entry) +
					   strlen(newacl));
    memset(newent, 0, sizeof(struct mbox_entry) +
					   strlen(newacl));
    strcpy(newent->name, oldent->name);
    strcpy(newent->partition, oldent->partition);
    strcpy(newent->acls, newacl);

    memset(&data, 0, sizeof(data));
    data.data = newent;
    data.size = sizeof(struct mbox_entry) + strlen(newacl);

    r = mbdb->put(mbdb, tid, &key, &data, 0);
    switch (r) {
    case 0:
	break;
    case EAGAIN:
	goto retry;
	break;
    default:
	syslog(LOG_ERR, "DBERROR: error updating acl %s: %s",
	       newent->name, strerror(r));
	r = IMAP_IOERROR;
	goto done;
    }


    /* set it in the /var/spool part */
    free(mailbox.acl);
    mailbox.acl = xstrdup(newacl);
    (void) mailbox_write_header(&mailbox);
    timestamp = time(0);
    uidvalidity = mailbox.uidvalidity;
    toimsp(name, uidvalidity, "ACLsn", newacl, timestamp, 0);
	
    mailbox_close(&mailbox);
    free(newacl);

  done:
    free(newent);

    switch (txn_commit(tid)) {
    case 0: 
	break;
    default:
	syslog(LOG_ERR, "DBERROR: failed on commit: %s",
	       strerror(r));
	return IMAP_IOERROR;
    }

    return 0;
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
int mboxlist_findall(pattern, isadmin, userid, auth_state, proc, rock)
char *pattern;
int isadmin;
char *userid;
struct auth_state *auth_state;
int (*proc)();
void* rock;
{
    struct glob *g;
    char usermboxname[MAX_MAILBOX_NAME+1];
    int usermboxnamelen;
    unsigned long offset, len, namelen, prefixlen, acllen;
    int inboxoffset;
    long matchlen, minmatch;
    char *name, *p, *acl, *aclcopy;
    char aclbuf[1024];
    char namebuf[MAX_MAILBOX_NAME+1];
    int rights;
    int r;
    char *inboxcase;
    DBC *cursor;
    DB_TXN *tid;
    DB_TXNMGR *txnp;
    DBT key, data;
    struct mbox_entry *mboxent;

    txnp = dbenv.tx_info;

    list_doingfind++;

    g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    inboxcase = glob_inboxcase(g);

    /* Build usermboxname */
    if (userid && !strchr(userid, '.') &&
	strlen(userid)+5 < MAX_MAILBOX_NAME) {
	strcpy(usermboxname, "user.");
	strcat(usermboxname, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = 0;
    }

    /* transaction restart place */
    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin the transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0) {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	return IMAP_IOERROR;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(g, "INBOX") != -1) {
	    DBT key, data;

	    memset(&data, 0, sizeof(data));
	    memset(&key, 0, sizeof(key));
	    key.data = usermboxname;
	    key.size = usermboxnamelen;
	    r = mbdb->get(mbdb, tid, &key, &data, 0);
	    switch (r) {
	    case 0:
		r = proc(inboxcase, 5, 1, rock);
		if (r) {
		    glob_free(&g);
		    list_doingfind--;
		    goto done;
		}
		break;
	    case DB_NOTFOUND:
		break;
	    case EAGAIN:
		goto retry;
	    default: /* DB error */
		syslog(LOG_ERR, "DBERROR: error fetching %s: %s",
		       usermboxname, strerror(r));
		r = IMAP_IOERROR;
		goto done;
	    }
	}

	/* "user.X" matches patterns "user.X", "user.X*", "user.X%", etc */
	else if (!strncmp(pattern, usermboxname, usermboxnamelen) &&
		 GLOB_TEST(g, usermboxname) != -1) {
	    key.data = usermboxname;
	    key.size = usermboxnamelen;
	    r = mbdb->get(mbdb, tid, &key, &data, 0);
	    switch (r) {
	    case 0:
		r = proc(usermboxname, usermboxnamelen, 1, rock);
		if (r) {
		    glob_free(&g);
		    list_doingfind--;
		    goto done;
		}
		break;
	    case DB_NOTFOUND:
		break;
	    case EAGAIN:
		goto retry;
		break;
	    default: /* DB error */
		syslog(LOG_ERR, "DBERROR: error fetching %s: %s",
		       usermboxname, strerror(r));
		r = IMAP_IOERROR;
		goto done;
	    }
	}

	strcpy(usermboxname+usermboxnamelen, ".");
	usermboxnamelen++;
    }

    /* Find fixed-string pattern prefix */
    for (p = pattern; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?') break;
    }
    prefixlen = p - pattern;
    *p = '\0';

    /*
     * If user.X.* or INBOX.* can match pattern,
     * search for those mailboxes next
     */

    if (userid &&
	(!strncmp(usermboxname, pattern, usermboxnamelen-1) ||
	 !strncasecmp("inbox.", pattern, prefixlen < 6 ? prefixlen : 6))) {
      int result;
	if (!strncmp(usermboxname, pattern, usermboxnamelen-1)) {
	    inboxoffset = 0;
	}
	else {
	    inboxoffset = strlen(userid);
	}

	r=mbdb->cursor(mbdb, tid, &cursor, 0);
	if (r!=0) { 
	  syslog(LOG_ERR, "Unable to create cursor");
	  goto done;
	}

	memset(&data, 0, sizeof(data));
	memset(&key, 0, sizeof(key));
	key.data = usermboxname;
	key.size = usermboxnamelen;

	r = cursor->c_get(cursor, &key, &data, DB_SET_RANGE);

	while (r != DB_NOTFOUND) {
	    switch (r) {
	    case 0:
	      break;
		
	    case EAGAIN:
		syslog(LOG_WARNING, "unexpected deadlock in mboxlist.c");
		goto retry;
		break;
		
	    default:
		syslog(LOG_ERR, "DBERROR: error advancing: %s", strerror(r));
		r = IMAP_IOERROR;
		goto done;
	    }

	    mboxent = (struct mbox_entry *) data.data;

	    /* make sure has the prefix */
	    if (strncmp(mboxent->name, usermboxname, usermboxnamelen)!=0) break;

	    minmatch = 0;
	    while (minmatch >= 0) {
	      strcpy(namebuf, "INBOX.");
	      strcat(namebuf, mboxent->name+usermboxnamelen);
	      namelen=strlen(namebuf);

	      matchlen = glob_test(g, namebuf,
				   namelen, &minmatch);
	      if (matchlen == -1) { break; }
		
	      r = proc(namebuf, matchlen, 1, rock);
	      if (r) {
		glob_free(&g);
		list_doingfind--;
		goto done;
	      }
	    }

	    memset(&data, 0, sizeof(data));
	    r = cursor->c_get(cursor, &key, &data, DB_NEXT);
	}
    }

    /* Search for all remaining mailboxes.  Start at the pattern prefix */

    r=mbdb->cursor(mbdb, tid, &cursor, 0);
    if (r!=0) { 
      syslog(LOG_ERR, "Unable to create cursor");
      goto done;
    }

    memset(&data, 0, sizeof(data));
    memset(&key, 0, sizeof(key));
    key.data = ""; /* xxx should use pattern */
    key.size = 0;

    r = cursor->c_get(cursor, &key, &data, DB_FIRST);

    if (userid) usermboxname[--usermboxnamelen] = '\0';
    while (r != DB_NOTFOUND) {
	switch (r) {
	case 0:
	  break;

	case EAGAIN:
	    syslog(LOG_WARNING, "unexpected deadlock in mboxlist.c");
	    goto retry;
	    break;
	    
	default:
	    syslog(LOG_ERR, "DBERROR: error advancing: %s", strerror(r));
	    r = IMAP_IOERROR;
	    goto done;
	}
	
	name = key.data;
	namelen = key.size;
	mboxent = (struct mbox_entry *) data.data;

	/* does this even match our prefix? */
	if (strncmp(namebuf, pattern, prefixlen)) break;
	 

	/* does it match the glob? */
	minmatch=0;
	while (minmatch >= 0) {
	    matchlen = glob_test(g, name, namelen, &minmatch);

	    if (matchlen == -1 ||
		(userid && namelen >= usermboxnamelen &&
		 strncmp(name, usermboxname, usermboxnamelen) == 0 &&
		 (namelen == usermboxnamelen ||
		  name[usermboxnamelen] == '.'))) {
		break;
	    }

	    memcpy(namebuf, name, namelen);
	    namebuf[namelen] = '\0';

	    if (isadmin) {
	      r = proc(namebuf, matchlen, 1, rock);
	      if (r) {
		glob_free(&g);
		list_doingfind--;
		goto done;
	      }
	    } else {
	      rights = acl_myrights(auth_state, mboxent->acls);
	      if (rights & ACL_LOOKUP) {
		r = proc(namebuf, matchlen, (rights & ACL_CREATE),
			 rock);
		if (r) {
		  glob_free(&g);
		  list_doingfind--;
		  goto done;
		}
	      }
	  }

	}

	memset(&data, 0, sizeof(data));

	r = cursor->c_get(cursor, &key, &data, DB_NEXT);
    }
    r = 0;

  done:
    switch (txn_commit(tid)) {
    case 0:
	break;
    case EINVAL:
	syslog(LOG_WARNING, "tried to commit an already aborted transaction");
	break;
    default:
	syslog(LOG_WARNING, "failed on commit to read-only transaction");
	r = IMAP_IOERROR;
	break;
    }
	
    glob_free(&g);
    list_doingfind--;
    return r;
}

/*
 * Find subscribed mailboxes that match 'pattern'.
 * 'isadmin' is nonzero if user is a mailbox admin.  'userid'
 * is the user's login id.  For each matching mailbox, calls
 * 'proc' with the name of the mailbox.
 */
int mboxlist_findsub(pattern, isadmin, userid, auth_state, proc)
char *pattern;
int isadmin;
char *userid;
struct auth_state *auth_state;
int (*proc)();
{
    int subsfd;
    const char *subs_base;
    unsigned long subs_size;
    char *subsfname;
    struct glob *g;
    char usermboxname[MAX_MAILBOX_NAME+1];
    int usermboxnamelen;
    char namebuf[MAX_MAILBOX_NAME+1];
    char namematchbuf[MAX_MAILBOX_NAME+1];
    int r;
    unsigned long offset, len, prefixlen, listlinelen;
    int inboxoffset;
    const char *name, *endname;
    char *p;
    unsigned long namelen;
    long matchlen, minmatch;
    char *acl;
    char *inboxcase;

    if (r = mboxlist_opensubs(userid, 0, &subsfd, &subs_base, &subs_size,
			      &subsfname, (char **) 0)) {
	return r;
    }

    list_doingfind++;

    g = glob_init(pattern, GLOB_HIERARCHY|GLOB_INBOXCASE);
    inboxcase = glob_inboxcase(g);

    /* Build usermboxname */
    if (userid && !strchr(userid, '.') &&
	strlen(userid)+5 < MAX_MAILBOX_NAME) {
	strcpy(usermboxname, "user.");
	strcat(usermboxname, userid);
	usermboxnamelen = strlen(usermboxname);
    }
    else {
	userid = 0;
    }

    /* Check for INBOX first of all */
    if (userid) {
	if (GLOB_TEST(g, "INBOX") != -1) {
	    (void) bsearch_mem(usermboxname, 1, subs_base, subs_size, 0, &len);
	    if (len) {
		r = (*proc)(inboxcase, 5, 1);
		if (r) {
		    mboxlist_closesubs(subsfd, subs_base, subs_size);
		    glob_free(&g);
		    list_doingfind--;
		    return r;
		}
	    }
	}
	else if (!strncmp(pattern, usermboxname, usermboxnamelen) &&
		 GLOB_TEST(g, usermboxname) != -1) {
	    (void) bsearch_mem(usermboxname, 1, subs_base, subs_size, 0, &len);
	    if (len) {
		r = (*proc)(inboxcase, 5, 1);
		if (r) {
		    mboxlist_closesubs(subsfd, subs_base, subs_size);
		    glob_free(&g);
		    list_doingfind--;
		    return r;
		}
	    }
	}

	strcpy(usermboxname+usermboxnamelen, ".");
	usermboxnamelen++;
    }

    /* Find fixed-string pattern prefix */
    for (p = pattern; *p; p++) {
	if (*p == '*' || *p == '%' || *p == '?') break;
    }
    prefixlen = p - pattern;
    *p = '\0';

    /*
     * If user.X.* or INBOX.* can match pattern,
     * search for those mailboxes next
     */
    if (userid &&
	(!strncmp(usermboxname, pattern, usermboxnamelen-1) ||
	 !strncasecmp("inbox.", pattern, prefixlen < 6 ? prefixlen : 6))) {

	if (!strncmp(usermboxname, pattern, usermboxnamelen-1)) {
	    inboxoffset = 0;
	}
	else {
	    inboxoffset = strlen(userid);
	}

	offset = bsearch_mem(usermboxname, 1, subs_base, subs_size, 0,
			     (unsigned long *)0);

	while (offset < subs_size) {

	name = subs_base + offset;
	    p = memchr(name, '\n', subs_size - offset);
	    endname = memchr(name, '\t', subs_size - offset);
	    if (!p || !endname || endname - name > MAX_MAILBOX_NAME) {
		syslog(LOG_ERR, "IOERROR: corrupted subscription file %s",
		       subsfname);
		fatal("corrupted subscription file", EC_OSFILE);
	    }

	    len = p - name + 1;
	    namelen = endname - name;

	    if (strncmp(name, usermboxname, usermboxnamelen)) break;
	    minmatch = 0;
	    while (minmatch >= 0) {
		memcpy(namebuf, name, namelen);
		namebuf[namelen] = '\0';
		strcpy(namematchbuf, namebuf);

		if (inboxoffset) {
		    namematchbuf[inboxoffset] = inboxcase[0];
		    namematchbuf[inboxoffset+1] = inboxcase[1];
		    namematchbuf[inboxoffset+2] = inboxcase[2];
		    namematchbuf[inboxoffset+3] = inboxcase[3];
		    namematchbuf[inboxoffset+4] = inboxcase[4];
		}

		matchlen = glob_test(g, namematchbuf+inboxoffset,
				     namelen-inboxoffset, &minmatch);
		if (matchlen == -1) break;

#if NEEDSTODB		
		(void) bsearch_mem(namebuf, 1, list_base, list_size, 0,
				   &listlinelen);
#endif
		
		if (listlinelen) {
		    r = (*proc)(namematchbuf+inboxoffset, matchlen, 1);
		    if (r) {
			mboxlist_closesubs(subsfd, subs_base, subs_size);
			glob_free(&g);
			list_doingfind--;
			return r;
		    }
		}
		else {
		    mboxlist_changesub(namebuf, userid, auth_state, 0);
		    break;
		}
	    }
	    offset += len;
	}
    }

    /* Search for all remaining mailboxes.  Start at the patten prefix */
    offset = bsearch_mem(pattern, 1, subs_base, subs_size, 0,
			 (unsigned long *)0);

    if (userid) usermboxname[--usermboxnamelen] = '\0';
    while (offset < subs_size) {
	name = subs_base + offset;
	p = memchr(name, '\n', subs_size - offset);
	endname = memchr(name, '\t', subs_size - offset);
	if (!p || !endname || endname - name > MAX_MAILBOX_NAME) {
	    syslog(LOG_ERR, "IOERROR: corrupted subscription file %s",
		   subsfname);
	    fatal("corrupted subscription file", EC_OSFILE);
	}

	len = p - name + 1;
	namelen = endname - name;

	if (strncmp(name, pattern, prefixlen)) break;
	minmatch = 0;
	while (minmatch >= 0) {
	    matchlen = glob_test(g, name, namelen, &minmatch);
	    if (matchlen == -1 ||
		(userid && namelen >= usermboxnamelen &&
		 strncmp(name, usermboxname, usermboxnamelen) == 0 &&
		 (namelen == usermboxnamelen ||
		  name[usermboxnamelen] == '.'))) {
		break;
	    }

	    memcpy(namebuf, name, namelen);
	    namebuf[namelen] = '\0';

	    r = mboxlist_lookup(namebuf, (char **)0, &acl, NULL);
	    if (r == 0) {
		r = (*proc)(namebuf, matchlen,
			    (acl_myrights(auth_state, acl) & ACL_CREATE));
		if (r) {
		    mboxlist_closesubs(subsfd, subs_base, subs_size);
		    glob_free(&g);
		    list_doingfind--;
		    return r;
		}
	    }
	    else {
		mboxlist_changesub(namebuf, userid, auth_state, 0);
		break;
	    }
	}
	offset += len;
    }
	
    mboxlist_closesubs(subsfd, subs_base, subs_size);
    glob_free(&g);
    list_doingfind--;
    return 0;
}

/*
 * Change 'user's subscription status for mailbox 'name'.
 * Subscribes if 'add' is nonzero, unsubscribes otherwise.
 */
int 
mboxlist_changesub(name, userid, auth_state, add)
const char *name;
const char *userid;
struct auth_state *auth_state;
int add;
{
    int r;
    char *acl;
    int subsfd, newsubsfd;
    const char *subs_base;
    unsigned long subs_size;
    char *subsfname, *newsubsfname;
    unsigned long offset, len;
    struct iovec iov[10];
    int num_iov;
    int n;
    
    if (r = mboxlist_opensubs(userid, 1, &subsfd, &subs_base, &subs_size,
			      &subsfname, &newsubsfname)) {
	return r;
    }

    if (add) {
	/* Ensure mailbox exists and can be either seen or read by user */
	if (r = mboxlist_lookup(name, (char **)0, &acl, NULL)) {
	    mboxlist_closesubs(subsfd, subs_base, subs_size);
	    return r;
	}
	if ((acl_myrights(auth_state, acl) & (ACL_READ|ACL_LOOKUP)) == 0) {
	    mboxlist_closesubs(subsfd, subs_base, subs_size);
	    return IMAP_MAILBOX_NONEXISTENT;
	}
    }

    /* Find where mailbox is/would go in subscription list */
    offset = bsearch_mem(name, 1, subs_base, subs_size, 0, &len);
    if (add) {
	if (len) {
	    mboxlist_closesubs(subsfd, subs_base, subs_size);
	    return 0;		/* Already unsubscribed */
	}
    }
    else {
	if (!len) {
	    mboxlist_closesubs(subsfd, subs_base, subs_size);
	    return 0;		/* Alredy subscribed */
	}
    }

    newsubsfd = open(newsubsfname, O_RDWR|O_TRUNC|O_CREAT, 0666);
    if (newsubsfd == -1) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", newsubsfname);
	mboxlist_closesubs(subsfd, subs_base, subs_size);
	return IMAP_IOERROR;
    }

    /* Copy over subscription list, making change */
    num_iov = 0;
    iov[num_iov].iov_base = (char *)subs_base;
    iov[num_iov++].iov_len = offset;
    if (add) {
	iov[num_iov].iov_base = (char *)name;
	iov[num_iov++].iov_len = strlen(name);
	iov[num_iov].iov_base = "\t\n";
	iov[num_iov++].iov_len = 2;
    }
    iov[num_iov].iov_base = (char *)subs_base + offset + len;
    iov[num_iov++].iov_len = subs_size - (offset + len);

    n = retry_writev(newsubsfd, iov, num_iov);

    if (n == -1 || fsync(newsubsfd)) {
	syslog(LOG_ERR, "IOERROR: writing %s: %m", newsubsfname);
	mboxlist_closesubs(subsfd, subs_base, subs_size);
	close(newsubsfd);
	return IMAP_IOERROR;
    }	
    if (rename(newsubsfname, subsfname) == -1) {
	syslog(LOG_ERR, "IOERROR: renaming %s: %m", subsfname);
	mboxlist_closesubs(subsfd, subs_base, subs_size);
	close(newsubsfd);
	return IMAP_IOERROR;
    }
    mboxlist_closesubs(subsfd, subs_base, subs_size);
    close(newsubsfd);
    return 0;
}

/*
 * Set the quota on or create a quota root
 */
int
mboxlist_setquota(root, newquota)
const char *root;
int newquota;
{
    char quota_path[MAX_MAILBOX_PATH];
    char pattern[MAX_MAILBOX_PATH];
    struct quota quota;
    static struct quota zeroquota;
    int r;
    unsigned long offset, len;

    if (!root[0] || root[0] == '.' || strchr(root, '/')
	|| strchr(root, '*') || strchr(root, '%') || strchr(root, '?')) {
	return IMAP_MAILBOX_BADNAME;
    }
    
    quota = zeroquota;

    quota.root = (char *) root;
    mailbox_hash_quota(quota_path, root);

    if ((quota.fd = open(quota_path, O_RDWR, 0)) != -1) {
	/* Just lock and change it */
	r = mailbox_lock_quota(&quota);

	quota.limit = newquota;

	if (!r) r = mailbox_write_quota(&quota);
	if (quota.fd != -1) {
	    close(quota.fd);
	}
	return r;
    }

    /*
     * Have to create a new quota root
     */

#if NEEDSTODB
    /* Ensure there is at least one mailbox under the quota root */
    offset = bsearch_mem(quota.root, 1, list_base, list_size, 0, &len);
    if (!len) {
	if (strlen(quota.root) >= list_size - offset ||
	    strncmp(quota.root, list_base + offset,
		    strlen(quota.root)) != 0 ||
	    list_base[offset + strlen(quota.root)] != '.') {

	    return IMAP_MAILBOX_NONEXISTENT;
	}
    }
#endif
    
    /* perhaps create .NEW, lock, check if it got recreated, move in place */
    quota.lock_count = 1;
    quota.used = 0;
    quota.limit = newquota;
    r = mailbox_write_quota(&quota);

    if (r) {

	return r;
    }

    strcpy(pattern, quota.root);
    strcat(pattern, ".*");
    mboxlist_newquota = &quota;
    
    if (len) {
	mboxlist_changequota(quota.root, 0, 0);
    }
    mboxlist_findall(pattern, 1, 0, 0, mboxlist_changequota, NULL);
    
    r = mailbox_write_quota(&quota);
    if (quota.fd != -1) {
	close(quota.fd);
    }

    return r;
}

/*
 * Resynchronize the news mailboxes with the 'num' groups in the
 * sorted array 'group'.  Mark the ones we have seen in the array
 * 'seen'
 */
int
mboxlist_syncnews(num, group, seen)
int num;
char **group;
int *seen;
{
    DB_TXN *tid;
    DB_TXNMGR *txnp = dbenv.tx_info;
    DBC *cursor;
    DBT key, keydel, data;
    struct mbox_entry *mboxent;
    int r;

    int deletethis;
    int deletedsomething = 0;
    int low, high, mid;
    struct mailbox mailbox;

    if (0) {
      retry:
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn: %s",
		   strerror(r));
	    return IMAP_IOERROR;
	}
    }

    /* begin the transaction */
    if ((r = txn_begin(txnp, NULL, &tid)) != 0) {
	syslog(LOG_ERR, "DBERROR: error beginning txn: %s", strerror(r));
	return IMAP_IOERROR;
    }

    mbdb->cursor(mbdb, tid, &cursor, 0);

    r = cursor->c_get(cursor, &key, &data, DB_FIRST);
    while (r != DB_NOTFOUND) {
	switch (r) {
	case 0:
	    break;

	case EAGAIN:
	    goto retry;
	    break;

	default:
	    syslog(LOG_ERR, "DBERROR: error advancing: %s", strerror(r));
	    r = IMAP_IOERROR;
	    goto done;
	}
	
	mboxent = (struct mbox_entry *) data.data;
	deletethis = 0;
	if (!strcasecmp(mboxent->partition, "news")) {
	    deletethis = 1;

	    /* Search for name in 'group' array */
	    low = 0;
	    high = num;
	    while (low <= high) {
		mid = (high - low)/2 + low;
		r = strcmp(key.data, group[mid]);
		if (r == 0) {
		    deletethis = 0;
		    seen[mid] = 1;
		    break;
		}
		else if (r < 0) {
		    high = mid - 1;
		}
		else {
		    low = mid + 1;
		}
	    }
	    if (deletethis) {
		/* Remove the mailbox.  Don't care about errors */
		r = mailbox_open_header(key.data, 0, &mailbox);
		if (!r) {
		    toimsp(key.data, mailbox.uidvalidity, "RENsn", "", 0, 0);
		    r = mailbox_delete(&mailbox, 0);
		}
	    }
	}

	keydel = key;
	r = cursor->c_get(cursor, &key, &data, DB_NEXT);

	if (deletethis) {
	    switch (mbdb->del(mbdb, tid, &keydel, 0)) {
	    case 0:
		break;

	    case EAGAIN:
		goto retry;
		break;

	    default:
		syslog(LOG_ERR, "DBERROR: error deleting newsgroup");
		r = IMAP_IOERROR;
		goto done;
	    }
	}
    }
    r = 0;

    switch (cursor->c_close(cursor)) {
    case 0:
	break;
    case EAGAIN:
	goto retry;
	break;
    }

  done:
    if (r == 0) {
	r = txn_commit(tid);

	switch (txn_commit(tid)) {
	case 0:
	    break;
	case EINVAL:
	    syslog(LOG_WARNING, 
		   "tried to commit an already aborted transaction");
	    break;
	default:
	    syslog(LOG_ERR, "DBERROR: failed on commit: %s",
		   strerror(r));
	    r = IMAP_IOERROR;
	    break;
	}
    } else {
	if ((r = txn_abort(tid)) != 0) {
	    syslog(LOG_ERR, "DBERROR: error aborting txn %s",
		   strerror(r));
	    r = IMAP_IOERROR;
	}
    }

    return r;
}

/*
 * Retrieve internal information, for reconstructing mailboxes file
 */
void mboxlist_getinternalstuff(listfnamep, newlistfnamep, basep, sizep)
const char **listfnamep;
const char **newlistfnamep;
const char **basep;
unsigned long *sizep;
{
    printf("yikes! don't reconstruct me!\n");
    exit(1);
}

/*
 * Open the subscription list for 'userid'.  If 'lock' is nonzero,
 * lock it.
 * 
 * On success, returns zero.  The int pointed to by 'subsfile' is set
 * to the open, locked file.  The file is mapped into memory and the
 * base and size of the mapping are placed in variables pointed to by
 * 'basep' and 'sizep', respectively .  If they are non-null, the
 * character pointers pointed to by 'fname' and 'newfname' are set to
 * the filenames of the old and new subscription files, respectively.
 *
 * On failure, returns an error code.
 */
static int
mboxlist_opensubs(userid, lock, subsfdp, basep, sizep, fname, newfname)
const char *userid;
int lock;
int *subsfdp;
const char **basep;
unsigned long *sizep;
const char **fname;
const char **newfname;
{
    int r;
    static char *subsfname, *newsubsfname;
    int subsfd;
    struct stat sbuf;
    const char *lockfailaction;
    char inboxname[MAX_MAILBOX_NAME+1];

    /* Users without INBOXes may not keep subscriptions */
    if (strchr(userid, '.') || strlen(userid) + 6 > MAX_MAILBOX_NAME) {
	return IMAP_PERMISSION_DENIED;
    }
    strcpy(inboxname, "user.");
    strcat(inboxname, userid);
    if (mboxlist_lookup(inboxname, (char **)0, (char **)0, NULL) != 0) {
	return IMAP_PERMISSION_DENIED;
    }

    if (subsfname) {
	free(subsfname);
	free(newsubsfname);
    }

    /* Build subscription list filename */
    subsfname = mboxlist_hash_usersubs(userid);

    newsubsfname = xmalloc(strlen(subsfname)+5);
    strcpy(newsubsfname, subsfname);
    strcat(newsubsfname, ".NEW");

    subsfd = open(subsfname, O_RDWR|O_CREAT, 0666);
    if (subsfd == -1) {
	syslog(LOG_ERR, "IOERROR: opening %s: %m", subsfname);
	return IMAP_IOERROR;
    }

    if (lock) {
	r = lock_reopen(subsfd, subsfname, &sbuf, &lockfailaction);
	if (r == -1) {
	    syslog(LOG_ERR, "IOERROR: %s %s: %m", lockfailaction, subsfname);
	    close(subsfd);
	    return IMAP_IOERROR;
	}
    }
    else {
	if (fstat(subsfd, &sbuf) == -1) {
	    syslog(LOG_ERR, "IOERROR: fstat on %s: %m", subsfname);
	    fatal("can't fstat subscription list", EC_OSFILE);
	}
    }

    *basep = 0;
    *sizep = 0;
    map_refresh(subsfd, 1, basep, sizep, sbuf.st_size, subsfname, 0);

    *subsfdp = subsfd;
    if (fname) *fname = subsfname;
    if (newfname) *newfname = newsubsfname;
    return 0;
}

/*
 * Close a subscription file
 */
static void
mboxlist_closesubs(subsfd, base, size)
int subsfd;
const char *base;
unsigned long size;
{
    map_free(&base, &size);
    close(subsfd);
}

/* Case-dependent comparison converter.
 * Treats \r and \t as end-of-string and treats '.' lower than
 * everything else.
 */
#define TOCOMPARE(c) (convert_to_compare[(unsigned char)(c)])
static unsigned char convert_to_compare[256] = {
    0x00, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,
    0x0a, 0x01, 0x01, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
    0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x02, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
    0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40, 'A', 'B', 'C', 'D', 'E', 'F', 'G',
    'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O',
    'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W',
    'X', 'Y', 'Z', 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
    0x60, 'a', 'b', 'c', 'd', 'e', 'f', 'g',
    'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o',
    'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
    'x', 'y', 'z', 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,
    0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f,
    0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
    0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
    0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7,
    0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
    0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
    0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf,
    0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7,
    0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf,
    0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7,
    0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
    0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
    0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff
};

__inline__ static int MIN(int a, int b)
{
    if (a < b) {
	return a;
    } else {
	return b;
    }
}

static int mbdb_order(const DBT *a, const DBT *b)
{
    char *s1 = a->data;
    char *s2 = b->data;
    int cmp;
    char c2;
    int i, m;

    m = MIN(a->size, b->size);
    i = 0;
    for (i = 0; i < m; i++) {
        cmp = TOCOMPARE(s1[i]) - TOCOMPARE(s2[i]);
        if (cmp) return cmp;
    }
    if (i == a->size) {
	if (i == b->size) {
	    return 0;
	}
        /* s1 is shorter than s2 */
        return -1;
    }
    /* s2 is shorter than s1 */
    return 1;
}



/*
 * ACL access canonicalization routine which ensures that 'owner'
 * retains lookup, administer, and create rights over a mailbox.
 */
int mboxlist_ensureOwnerRights(rock, identifier, access)
void *rock;
const char *identifier;
int access;
{
    char *owner = (char *)rock;
    if (strcmp(identifier, owner) != 0) return access;
    return access|ACL_LOOKUP|ACL_ADMIN|ACL_CREATE;
}

/*
 * Helper function to change the quota root for 'name' to that pointed
 * to by the static global struct pointer 'mboxlist_newquota'.
 */
static int
mboxlist_changequota(name, matchlen, maycreate)
char *name;
int matchlen;
int maycreate;
{
    int r;
    struct mailbox mailbox;

    r = mailbox_open_header(name, 0, &mailbox);
    if (r) goto error_noclose;

    r = mailbox_lock_header(&mailbox);
    if (r) goto error;

    r = mailbox_open_index(&mailbox);
    if (r) goto error;

    r = mailbox_lock_index(&mailbox);
    if (r) goto error;

    if (mailbox.quota.root) {
	if (strlen(mailbox.quota.root) >= strlen(mboxlist_newquota->root)) {
	    /* Part of a child quota root */
	    mailbox_close(&mailbox);
	    return 0;
	}

	r = mailbox_lock_quota(&mailbox.quota);
	if (r) goto error;
	if (mailbox.quota.used >= mailbox.quota_mailbox_used) {
	    mailbox.quota.used -= mailbox.quota_mailbox_used;
	}
	else {
	    mailbox.quota.used = 0;
	}
	r = mailbox_write_quota(&mailbox.quota);
	if (r) {
	    syslog(LOG_ERR,
		   "LOSTQUOTA: unable to record free of %u bytes in quota %s",
		   mailbox.quota_mailbox_used, mailbox.quota.root);
	}
	mailbox_unlock_quota(&mailbox.quota);
	free(mailbox.quota.root);
    }

    mailbox.quota.root = xstrdup(mboxlist_newquota->root);
    r = mailbox_write_header(&mailbox);
    if (r) goto error;

    mboxlist_newquota->used += mailbox.quota_mailbox_used;
    mailbox_close(&mailbox);
    return 0;

 error:
    mailbox_close(&mailbox);
 error_noclose:
    syslog(LOG_ERR, "LOSTQUOTA: unable to change quota root for %s to %s: %s",
	   name, mboxlist_newquota->root, error_message(r));
    
    return 0;
}

void
mboxlist_close(void)
{
    /* noop with db */
}

void db_panic(DB_ENV *dbenv, int errno)
{
    syslog(LOG_CRIT, "DBERROR: critical database situation");
    /* but don't bounce mail */
    exit(EC_TEMPFAIL);
}

void db_err(char *db_prfx, char *buffer)
{
    syslog(LOG_INFO, "DBINFO: %s", buffer);
}

void mboxlist_init(void)
{
    int r;
    char dbdir[1024];
    
    memset(&dbenv, 0, sizeof(dbenv));
    dbenv.db_paniccall = &db_panic;
    /* dbenv.db_errcall = &db_err; */
    dbenv.db_verbose = 1;

    /* create the name of the db file */
    strcpy(dbdir, config_dir);
    /*    strcat(dbdir, FNAME_DBDIR);*/
    
    r = db_appinit(dbdir, NULL, &dbenv, 
		   DB_INIT_LOCK | DB_INIT_MPOOL | DB_INIT_TXN | DB_TXN_NOSYNC
	         | DB_CREATE);
    if (r) {
	syslog(LOG_ERR, "DBERROR: db_appinit failed: %s", strerror(r));
	exit(EC_TEMPFAIL);
    }

}

void
mboxlist_open(void)
{
    int ret;
    DB_INFO dbinfo;

    mboxlist_init();

    /* create db file name if necessary */
    if (!listfname) {
	listfname = xmalloc(strlen(config_dir)+sizeof(FNAME_MBOXLIST));
	strcpy(listfname, config_dir);
	strcat(listfname, FNAME_MBOXLIST);
    }

    /*    if (list_locked || list_doingfind) return;*/

    memset(&dbinfo, 0, sizeof(dbinfo));
    dbinfo.bt_compare = &mbdb_order;
    /*    dbinfo.bt_prefix = &mbdb_prefix;*/

    ret = db_open(listfname, DB_BTREE, DB_CREATE, 0664, 
		  &dbenv, &dbinfo, &mbdb);
    if (ret != 0) {
	syslog(LOG_ERR, "IOERROR: opening %s: %m", listfname);
	    /* Exiting TEMPFAIL because Sendmail thinks this
	       EC_OSFILE == permanent failure. */
	fatal("can't read mailboxes file", EC_TEMPFAIL);
    }    

}

void mboxlist_done(void)
{
    int r;

    r = mbdb->close(mbdb, 0);
    if (!r) {
	syslog(LOG_ERR, "DBERROR: error closing mailboxes: %s",
	       strerror(r));
    }
    r = db_appexit(&dbenv);
    if (!r) {
	syslog(LOG_ERR, "DBERROR: error exiting application: %s",
	       strerror(r));
    }
}

/* hash the userid to a file containing the subscriptions for that user */
static char *mboxlist_hash_usersubs(const char *userid)
{
    char *fname = xmalloc(strlen(config_dir) + sizeof(FNAME_USERDIR) +
			  strlen(userid) + sizeof(FNAME_SUBSSUFFIX) + 10);
    char c;

    c = (char) tolower((int) *userid);
    if (!islower(c)) {
	c = 'q';
    }
    sprintf(fname, "%s%s%c/%s%s", config_dir, FNAME_USERDIR, c, userid,
	    FNAME_SUBSSUFFIX);

    return fname;
}
