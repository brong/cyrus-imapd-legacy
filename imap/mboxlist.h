/* mboxlist.c -- Mailbox list manipulation routines
 * 
 * Copyright 1999 Carnegie Mellon University
 * 
 * $Id: mboxlist.h,v 1.1.2.2 1999/10/21 22:42:19 leg Exp $
 */

#ifndef MBOXLIST_H
#define MBOXLIST_H

#include "auth.h"

#define MAX_PARTITION_LEN 10

/* Lookup 'name' in the mailbox list. */
int mboxlist_lookup(const char *name, char **pathp, char **aclp, void *tid);

/* create mailbox */
int mboxlist_createmailbox(char *name, int format, char *partition, 
			   int isadmin, char *userid, 
			   struct auth_state *auth_state);

/* Delete a mailbox. */
int mboxlist_deletemailbox(char *name, int isadmin, char *userid, 
			   struct auth_state *auth_state, int checkacl);

/* Rename/move a mailbox */
int mboxlist_renamemailbox(char *oldname, char *newname, char *partition, 
			   int isadmin, char *userid, 
			   struct auth_state *auth_state);

/* change ACL */
int mboxlist_setacl(char *name, char *identifier, char *rights, int isadmin, 
		    char *userid, struct auth_state *auth_state);

/* Find all mailboxes that match 'pattern'. */
int mboxlist_findall(char *pattern, int isadmin, char *userid, 
		     struct auth_state *auth_state, int (*proc)(), void *rock);

/* Find subscribed mailboxes that match 'pattern'. */
int mboxlist_findsub(char *pattern, int isadmin, char *userid, 
		     struct auth_state *auth_state, int (*proc)());

/* Change 'user's subscription status for mailbox 'name'. */
int mboxlist_changesub(const char *name, const char *userid, 
		       struct auth_state *auth_state, int add);

/* set or create quota root */
int mboxlist_setquota(const char *root, int newquota);

/* Resynchronize the news mailboxes. */
int mboxlist_syncnews(int num, char **group, int *seen);

/* open the mailboxes db */
void mboxlist_open(void);

/* close the database */
void mboxlist_close(void);

/* initialize database structures */
void mboxlist_init(void);

/* done with database stuff */
void mboxlist_done(void);

#endif
