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
 *
 * $Id: imapd.h,v 1.72 2010/01/06 17:01:34 murch Exp $
 */

#ifndef INCLUDED_IMAPD_H
#define INCLUDED_IMAPD_H

#include "annotate.h"
#include "charset.h"
#include "hash.h"
#include "mailbox.h"
#include "prot.h"
#include "strarray.h"
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
    hash_table *cidhash;          /* for XCONVFETCH */
    struct namespace *namespace;  /* for the FOLDER fetchitem */
    const char *userid;
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
    FETCH_GUID   =    (1<<14),
    FETCH_SHA1   =    (1<<15),
    FETCH_FILESIZE =  (1<<16),
    FETCH_CID =			(1<<17),
    FETCH_FOLDER =		(1<<18),
    FETCH_UIDVALIDITY =		(1<<19)
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
    unsigned last_msgno;
    unsigned last_found;
    /* returned to caller */
    struct seqset *modified;
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

/* Bitmasks for search flags */
enum {
    SEARCH_RECENT_SET =         (1<<0),
    SEARCH_RECENT_UNSET	=       (1<<1),
    SEARCH_SEEN_SET =           (1<<2),
    SEARCH_SEEN_UNSET =	        (1<<3)
/*    SEARCH_UNCACHEDHEADER =	(1<<4) -- obsolete */
};

/* Bitmasks for search return options */
enum {
    SEARCH_RETURN_MIN =		(1<<0),
    SEARCH_RETURN_MAX =		(1<<1),
    SEARCH_RETURN_ALL =		(1<<2),
    SEARCH_RETURN_COUNT =	(1<<3)
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
    struct seqset *sequence;
    struct seqset *uidsequence;
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

    /* For ESEARCH */
    const char *tag;
    int returnopts;
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
    SORT_DISPLAYFROM,
    SORT_DISPLAYTO,
    SORT_FROM,
    SORT_SIZE,
    SORT_SUBJECT,
    SORT_TO,
    SORT_ANNOTATION,
    SORT_MODSEQ,
    SORT_UID
    /* values > 255 are reserved for internal use */
};

/* Sort key modifier flag bits */
#define SORT_REVERSE		(1<<0)

/* Windowing arguments for the XCONVSORT command */
struct windowargs {
    int conversations;		/* whether to limit the results by
				   conversation id */
    uint32_t limit;		/* limit on how many messages to return,
				 * 0 means unlimited. */
    uint32_t position;		/* 1-based index into results of first
				 * message to return.  0 means not
				 * specified which is the same as 1. */
    uint32_t anchor;		/* UID of a message used to locate the
				 * start of the window; 0 means not
				 * specified.  If the anchor is found,
				 * the first message reported will be
				 * the largest of 1 and the anchor minus
				 * @offset.  If not specified or not
				 * found, @position will be used instead. */
    int32_t offset;
    int until;			/* if 1, @anchor/@offset or @position
				 * marks the *end* of the window, if 0
				 * the start */
    int changedsince;		/* if 1, show messages a) added since @uidnext,
				 * b) removed since @modseq, or c) modified
				 * since @modseq */
    modseq_t modseq;
    uint32_t uidnext;
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
    LIST_RET_STATUS =		(1<<3)
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
    CAPA_QRESYNC = 	(1<<1)
};

/* Bitmask for urlfetch params */
enum {
    URLFETCH_BODY =			(1<<0),
    URLFETCH_BINARY =			(1<<1),
    URLFETCH_BODYPARTSTRUCTURE =	(1<<2)
};

extern struct protstream *imapd_out, *imapd_in;

#endif /* INCLUDED_IMAPD_H */
