/* imapd.h -- Common state for IMAP daemon
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

#ifndef INCLUDED_IMAPD_H
#define INCLUDED_IMAPD_H

#include "annotate.h"
#include "hash.h"
#include "mailbox.h"
#include "message.h"
#include "prot.h"
#include "strarray.h"
#include "search_expr.h"
#include "conversations.h"

/* Userid client has logged in as */
extern char *imapd_userid;

/* Authorization state for logged in userid */
extern struct auth_state *imapd_authstate;

/* Client capabilities (via ENABLE) */
extern unsigned imapd_client_capa;

struct octetinfo
{
    int start_octet;
    int octet_count;
};

struct section {
    char *name;
    struct octetinfo octetinfo;
    struct section *next;
};

/* List of HEADER.FIELDS[.NOT] fetch specifications */
struct fieldlist {
    char *section;		/* First part of BODY[x] value */
    strarray_t *fields;		/* Array of field-names */
    char *trail;		/* Last part of BODY[x] value */
    void *rock;
    struct fieldlist *next;
};

/* Items that may be fetched */
struct fetchargs {
    int fetchitems;		  /* Bitmask */
    struct section *binsections;  /* BINARY[x]<x> values */
    struct section *sizesections; /* BINARY.SIZE[x] values */
    struct section *bodysections; /* BODY[x]<x> values */
    struct fieldlist *fsections;  /* BODY[xHEADER.FIELDSx]<x> values */
    strarray_t headers;		  /* RFC822.HEADER.LINES */
    strarray_t headers_not;	  /* RFC822.HEADER.LINES.NOT */
    int start_octet;              /* start_octet for partial fetch */
    int octet_count;              /* octet_count for partial fetch, or 0 */
    modseq_t changedsince;        /* changed since modseq, or 0 */
    int vanished;                 /* report expunges since changedsince */
    const char *match_seq;
    const char *match_uid;        /* sequence match data for VANISHED */

    bit32 cache_atleast;          /* to do headers we need atleast this
				   * cache version */
    struct namespace *namespace; 
    const char *userid;
    strarray_t entries;		  /* for FETCH_ANNOTATION */
    strarray_t attribs;
    int isadmin;
    struct auth_state *authstate;
    hash_table *cidhash;          /* for XCONVFETCH */
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
    FETCH_MODSEQ =		(1<<13),
    FETCH_ANNOTATION =		(1<<14),
    FETCH_GUID   =		(1<<15),
    FETCH_SHA1   =		(1<<16),
    FETCH_FILESIZE =		(1<<17),
    FETCH_CID =			(1<<18),
    FETCH_FOLDER =		(1<<19),
    FETCH_UIDVALIDITY =		(1<<20)
};

enum {
    FETCH_FAST = (FETCH_FLAGS|FETCH_INTERNALDATE|FETCH_SIZE),
    FETCH_ALL = (FETCH_FLAGS|FETCH_INTERNALDATE|FETCH_SIZE|FETCH_ENVELOPE),
    FETCH_FULL = (FETCH_ALL|FETCH_BODY)
};

/* Arguments to Store functions */
struct storeargs {
    int operation;
    int usinguid;
    modseq_t unchangedsince; /* unchanged since modseq, or ULLONG_MAX */
    int silent;
    int seen;
    /* for STORE_*_FLAGS */
    uint32_t system_flags;
    /* Note that we must pass the user flags as names because the
     * lookup of user flag names must proceed under the index lock */
    strarray_t flags;
    /* for STORE_ANNOTATION */
    struct entryattlist *entryatts;
    struct namespace *namespace;
    int isadmin;
    const char *userid;
    struct auth_state *authstate;
    /* private to index.c */
    bit32 user_flags[MAX_USER_FLAGS/32];
    time_t update_time;
    /* private to index_storeflag() */
    unsigned last_msgno;
    unsigned last_found;
    /* returned to caller */
    struct seqset *modified;
};

/* values for operation */
enum {
    STORE_ADD_FLAGS = 1,
    STORE_REMOVE_FLAGS,
    STORE_REPLACE_FLAGS,
    STORE_ANNOTATION
};

struct searchannot {
    struct searchannot *next;	    /* gnb:TODO remove */
    char *entry;
    char *attrib;
    struct namespace *namespace;    /* gnb:TODO get this from searchargs */
    int isadmin;		    /* gnb:TODO get this from searchargs */
    const char *userid;		    /* gnb:TODO get this from searchargs */
    struct auth_state *auth_state;  /* gnb:TODO get this from searchargs */
    struct buf value;
};

/* Flags for searchargs.state */
enum {
    GETSEARCH_CHARSET_KEYWORD = 0x01,
    GETSEARCH_RETURN = 0x02,
    GETSEARCH_CHARSET_FIRST = 0x04,
};


/* Bitmasks for search return options */
enum {
    SEARCH_RETURN_MIN =		(1<<0),
    SEARCH_RETURN_MAX =		(1<<1),
    SEARCH_RETURN_ALL =		(1<<2),
    SEARCH_RETURN_COUNT =	(1<<3),
    SEARCH_RETURN_RELEVANCY =	(1<<4)
};

/* Things that may be searched for */
struct searchargs {
    struct search_expr *root;
    int charset;
    int state;
    /* used only during parsing */
    int fuzzy_depth;

    /* For ESEARCH & XCONVMULTISORT */
    const char *tag;
    int returnopts;
    struct namespace *namespace;
    const char *userid;
    struct auth_state *authstate;
    int isadmin;
};

/* Sort criterion */
struct sortcrit {
    unsigned key;		/* sort key */
    int flags;			/* key modifiers as defined below */
    union {			/* argument(s) to the sort key */
	struct {
	    char *entry;
	    char *userid;
	} annot;
	struct {
	    char *name;
	} flag;
    } args;
};

/* Values for sort keys */
enum {
    SORT_SEQUENCE = 0,
    SORT_ARRIVAL,	/* RFC 5256 */
    SORT_CC,		/* RFC 5256 */
    SORT_DATE,		/* RFC 5256 */
    SORT_DISPLAYFROM,	/* RFC 5957 */
    SORT_DISPLAYTO,	/* RFC 5957 */
    SORT_FROM,		/* RFC 5256 */
    SORT_SIZE,		/* RFC 5256 */
    SORT_SUBJECT,	/* RFC 5256 */
    SORT_TO,		/* RFC 5256 */
    SORT_ANNOTATION,	/* RFC 5257 */
    SORT_MODSEQ,	/* nonstandard */
    SORT_UID,		/* nonstandard */
    SORT_HASFLAG,	/* nonstandard */
    SORT_CONVMODSEQ,	/* nonstandard */
    SORT_CONVEXISTS,	/* nonstandard */
    SORT_CONVSIZE,	/* nonstandard */
    SORT_HASCONVFLAG,	/* nonstandard */
    SORT_FOLDER,	/* nonstandard */
    SORT_RELEVANCY	/* RFC 6203 */
    /* values > 255 are reserved for internal use */
};

/* Sort key modifier flag bits */
#define SORT_REVERSE		(1<<0)	    /* RFC 5256 */

/* Windowing arguments for the XCONVSORT command */
struct windowargs {
    int conversations;		/* whether to limit the results by
				   conversation id */
    uint32_t limit;		/* limit on how many messages to return,
				 * 0 means unlimited. */
    uint32_t position;		/* 1-based index into results of first
				 * message to return.  0 means not
				 * specified which is the same as 1.
				 * Mutually exclusive with @anchor */
    uint32_t anchor;		/* UID of a message used to locate the
				 * start of the window; 0 means not
				 * specified.  If the anchor is found,
				 * the first message reported will be
				 * the largest of 1 and the anchor minus
				 * @offset.  If specified but not found,
				 * an error will be returned.  Mutually
				 * exclusive with @position.*/
    char *anchorfolder;		/* internal mboxname of a folder to
				 * which the anchor applies; only used
				 * for XCONVMULTISORT. */
    uint32_t offset;
    int changedsince;		/* if 1, show messages a) added since @uidnext,
				 * b) removed since @modseq, or c) modified
				 * since @modseq */
    modseq_t modseq;
    uint32_t uidnext;
    uint32_t upto;		/* UID of a message used to terminate an
				 * XCONVUPDATES early, 0 means not
				 * specified.  */
};

struct snippetargs
{
    struct snippetargs *next;
    char *mboxname;		/* internal */
    uint32_t uidvalidity;
    struct {
	uint32_t *data;
	int count;
	int alloc;
    } uids;
};

/* Bitmask for status queries */
enum {
    STATUS_MESSAGES =		(1<<0),
    STATUS_RECENT =		(1<<1),
    STATUS_UIDNEXT =		(1<<2),
    STATUS_UIDVALIDITY =	(1<<3),
    STATUS_UNSEEN =		(1<<4),
    STATUS_HIGHESTMODSEQ =	(1<<5),
    STATUS_XCONVEXISTS =	(1<<6),
    STATUS_XCONVUNSEEN =	(1<<7),
    STATUS_XCONVMODSEQ =	(1<<8)
};

/* Arguments to List functions */
struct listargs {
    unsigned cmd;		/* Command variant */
    unsigned sel;		/* Selection options */
    unsigned ret;		/* Return options */
    const char *ref;		/* Reference name */
    strarray_t pat;		/* Mailbox pattern(s) */
    const char *scan;		/* SCAN content */
    hash_table server_table;	/* for proxying SCAN */
    unsigned statusitems;	/* for RETURN STATUS */
};

/* Value for List command variant */
enum {
    LIST_CMD_LIST = 0,
    LIST_CMD_LSUB,
    LIST_CMD_EXTENDED,
    LIST_CMD_XLIST,
};

/* Bitmask for List selection options */
enum {
    LIST_SEL_SUBSCRIBED =	(1<<0),
    LIST_SEL_REMOTE =		(1<<1),
    LIST_SEL_RECURSIVEMATCH =	(1<<2),
    LIST_SEL_SPECIALUSE =	(1<<3)
};

/* Bitmask for List return options */
enum {
    LIST_RET_SUBSCRIBED =	(1<<0),
    LIST_RET_CHILDREN =		(1<<1),
    LIST_RET_SPECIALUSE =	(1<<2),
    LIST_RET_STATUS =		(1<<3),
    LIST_RET_MYRIGHTS =		(1<<4)
};

/* Bitmask for List name attributes */
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

/* Bitmask for client capabilities */
enum {
    CAPA_CONDSTORE =	(1<<0),
    CAPA_QRESYNC =	(1<<1)
};

/* Bitmask for urlfetch params */
enum {
    URLFETCH_BODY =			(1<<0),
    URLFETCH_BINARY =			(1<<1),
    URLFETCH_BODYPARTSTRUCTURE =	(1<<2)
};

extern struct protstream *imapd_out, *imapd_in;

#endif /* INCLUDED_IMAPD_H */
