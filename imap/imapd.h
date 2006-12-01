/* imapd.h -- Common state for IMAP daemon
 * $Id: imapd.h,v 1.63.2.1 2006/12/01 17:46:41 murch Exp $
 *
 * Copyright (c) 1998-2003 Carnegie Mellon University.  All rights reserved.
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
 *    prior written permission. For permission or any other legal
 *    details, please contact  
 *      Office of Technology Transfer
 *      Carnegie Mellon University
 *      5000 Forbes Avenue
 *      Pittsburgh, PA  15213-3890
 *      (412) 268-4387, fax: (412) 268-7395
 *      tech-transfer@andrew.cmu.edu
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
 */

#ifndef INCLUDED_IMAPD_H
#define INCLUDED_IMAPD_H

#include "annotate.h"
#include "charset.h"
#include "mailbox.h"
#include "prot.h"

/* Userid client has logged in as */
extern char *imapd_userid;

/* Authorization state for logged in userid */
extern struct auth_state *imapd_authstate;

/* Number of messages in currently open mailbox */
extern int imapd_exists;

/* Is client CONDSTORE-aware? */
extern int imapd_condstore_client;

/* List of HEADER.FIELDS[.NOT] fetch specifications */
struct fieldlist {
    char *section;		/* First part of BODY[x] value */
    struct strlist *fields;	/* List of field-names */
    char *trail;		/* Last part of BODY[x] value */
    void *rock;
    struct fieldlist *next;
};

/* Items that may be fetched */
struct fetchargs {
    int fetchitems;		  /* Bitmask */
    struct strlist *binsections;  /* BINARY[x]<x> values */
    struct strlist *sizesections; /* BINARY.SIZE[x] values */
    struct strlist *bodysections; /* BODY[x]<x> values */
    struct fieldlist *fsections;  /* BODY[xHEADER.FIELDSx]<x> values */
    struct strlist *headers;	  /* RFC822.HEADER.LINES */
    struct strlist *headers_not;  /* RFC822.HEADER.LINES.NOT */
    int start_octet;              /* start_octet for partial fetch */
    int octet_count;              /* octet_count for partial fetch, or 0 */
    modseq_t changedsince;        /* changed since modseq, or 0 */

    bit32 cache_atleast;          /* to do headers we need atleast this
				   * cache version */
};

struct octetinfo 
{
    int start_octet;
    int octet_count;
};

/* Bitmasks for fetchitems */
enum {
    FETCH_UID =                 (1<<0),
    FETCH_INTERNALDATE =        (1<<1),
    FETCH_SIZE =                (1<<2),
    FETCH_FLAGS =               (1<<3),
    FETCH_ENVELOPE =	        (1<<4),
    FETCH_BODYSTRUCTURE =	(1<<5),
    FETCH_BODY =                (1<<6),
    FETCH_HEADER =	        (1<<7),
    FETCH_TEXT =                (1<<8),
    FETCH_RFC822 =              (1<<9),
    FETCH_SETSEEN =             (1<<10),
/*     FETCH_UNCACHEDHEADER =      (1<<11) -- obsolete */
    FETCH_IS_PARTIAL =          (1<<12), /* this is the PARTIAL command */
    FETCH_MODSEQ =		(1<<13)
};

enum {
    FETCH_FAST = (FETCH_FLAGS|FETCH_INTERNALDATE|FETCH_SIZE),
    FETCH_ALL = (FETCH_FLAGS|FETCH_INTERNALDATE|FETCH_SIZE|FETCH_ENVELOPE),
    FETCH_FULL = (FETCH_ALL|FETCH_BODY)
};

/* Arguments to Store functions */
struct storeargs {
    int operation;
    modseq_t unchangedsince; /* unchanged since modseq, or ULLONG_MAX */
    int silent;
    int seen;
    bit32 system_flags;
    /* private to index.c */
    bit32 user_flags[MAX_USER_FLAGS/32];
    time_t update_time;
    int usinguid;
    /* private to index_storeflag() */
    int last_msgno;
    int last_found;
};

/* values for operation */
enum {
    STORE_ADD = 1,
    STORE_REMOVE = 2,
    STORE_REPLACE = 3
};

struct searchsub {
    struct searchsub *next;
    struct searchargs *sub1;
    /*
     * If sub2 is null, then sub1 is NOT'ed.
     * Otherwise sub1 and sub2 are OR'ed.
     */
    struct searchargs *sub2;
};

enum {
    SEARCH_RECENT_SET =         (1<<0),
    SEARCH_RECENT_UNSET	=       (1<<1),
    SEARCH_SEEN_SET =           (1<<2),
    SEARCH_SEEN_UNSET =	        (1<<3)
/*    SEARCH_UNCACHEDHEADER =	(1<<4) -- obsolete */
};

/* Things that may be searched for */
struct searchargs {
    int flags;
    unsigned smaller, larger;
    time_t before, after;
    time_t sentbefore, sentafter;
    bit32 system_flags_set;
    bit32 system_flags_unset;
    bit32 user_flags_set[MAX_USER_FLAGS/32];
    bit32 user_flags_unset[MAX_USER_FLAGS/32];
    struct strlist *sequence;
    struct strlist *uidsequence;
    struct strlist *from;
    struct strlist *to;
    struct strlist *cc;
    struct strlist *bcc;
    struct strlist *subject;
    struct strlist *messageid;
    struct strlist *body;
    struct strlist *text;
    struct strlist *header_name, *header;
    struct searchsub *sublist;
    modseq_t modseq;

    bit32 cache_atleast;
};

/* Sort criterion */
struct sortcrit {
    unsigned key;		/* sort key */
    int flags;			/* key modifiers as defined below */
    union {			/* argument(s) to the sort key */
	struct {
	    char *entry;
	    char *attrib;
	} annot;
    } args;
};

/* Values for sort keys */
enum {
    SORT_SEQUENCE = 0,
    SORT_ARRIVAL,
    SORT_CC,
    SORT_DATE,
    SORT_FROM,
    SORT_SIZE,
    SORT_SUBJECT,
    SORT_TO,
    SORT_ANNOTATION,
    SORT_MODSEQ
    /* values > 255 are reserved for internal use */
};

/* Sort key modifier flag bits */
#define SORT_REVERSE		(1<<0)

/* Bitmask for status queries */
enum {
    STATUS_MESSAGES =	        (1<<0),
    STATUS_RECENT =		(1<<1),
    STATUS_UIDNEXT =		(1<<2),
    STATUS_UIDVALIDITY =	(1<<3),
    STATUS_UNSEEN =		(1<<4),
    STATUS_HIGHESTMODSEQ =	(1<<5)
};

enum {
    /* LIST selection options */
    LIST_SEL_SUBSCRIBED =	(1<<0),
    LIST_SEL_REMOTE =		(1<<1),
    LIST_SEL_RECURSIVEMATCH =	(1<<2),

    /* LIST return options */
    LIST_RET_SUBSCRIBED =	(1<<8),
    LIST_RET_CHILDREN =		(1<<9),

    /* other options */
    LIST_OPT_RLIST =		(1<<16),
    LIST_OPT_LSUB =		(1<<17),
    LIST_OPT_EXTENDED =		(1<<18)  /* Extended List command */
};
#define list_sel_opts (LIST_RET_SUBSCRIBED - 1)
#define list_ret_opts ((LIST_OPT_RLIST - 1) & ~list_sel_opts)

/* Name attributes that may be retuned by LIST */
enum {
    /* from RFC 3501 */
    MBOX_ATTRIBUTE_NOINFERIORS =	(1<<0),
    MBOX_ATTRIBUTE_NOSELECT =		(1<<1),
    MBOX_ATTRIBUTE_MARKED =		(1<<2),
    MBOX_ATTRIBUTE_UNMARKED =		(1<<3),

    /* from draft-ietf-imapext-list-extensions-18.txt */
    MBOX_ATTRIBUTE_NONEXISTENT =	(1<<4),
    MBOX_ATTRIBUTE_SUBSCRIBED =		(1<<5),
    MBOX_ATTRIBUTE_REMOTE =		(1<<6),
    MBOX_ATTRIBUTE_HASCHILDREN =	(1<<7),
    MBOX_ATTRIBUTE_HASNOCHILDREN =	(1<<8),
    MBOX_ATTRIBUTE_CHILDINFO_SUBSCRIBED = (1<<9)
};

extern struct protstream *imapd_out, *imapd_in;

extern void index_closemailbox(struct mailbox *mailbox);
extern void index_newmailbox(struct mailbox *mailbox, int examine_mode);
extern void index_operatemailbox(struct mailbox *mailbox);
extern void index_check(struct mailbox *mailbox, int usinguid,
			   int checkseen);
extern void index_checkseen(struct mailbox *mailbox, int quiet,
			       int usinguid, int oldexists);

extern int index_fetch(struct mailbox *mailbox, const char *sequence,
		       int usinguid, struct fetchargs *fetchargs,
		       int* fetchedsomething);
extern int index_store(struct mailbox *mailbox, char *sequence,
			  int usinguid, struct storeargs *storeargs,
			  char **flag, int nflags);
extern int index_search(struct mailbox *mailbox,
			struct searchargs *searchargs, int usinguid);
extern int find_thread_algorithm(char *arg);
extern int index_sort(struct mailbox *mailbox, struct sortcrit *sortcrit,
		      struct searchargs *searchargs, int usinguid);
extern int index_thread(struct mailbox *mailbox, int algorithm,
			struct searchargs *searchargs, int usinguid);
extern int index_copy(struct mailbox *mailbox, char *sequence,
		      int usinguid, char *name, char **copyuidp, int nolink);
extern int index_status(struct mailbox *mailbox, char *name,
			   int statusitems);

extern int index_getuids(struct mailbox *mailbox, unsigned lowuid);
extern int index_getstate(struct mailbox *mailbox);
extern int index_checkstate(struct mailbox *mailbox, unsigned indexdate,
			       unsigned seendate);

extern int index_finduid(unsigned uid);
extern int index_getuid(unsigned msgno);

extern mailbox_decideproc_t index_expungeuidlist;

/* See lib/charset.h for the definition of receiver. */
extern void index_getsearchtext(struct mailbox* mailbox,
                                index_search_text_receiver_t receiver,
                                void* rock);

#endif /* INCLUDED_IMAPD_H */
