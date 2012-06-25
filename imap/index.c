/* index.c -- Routines for dealing with the index file in the imapd
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
 * $Id: index.c,v 1.259 2010/06/28 12:04:53 brong Exp $
 */

#include <config.h>

#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <syslog.h>
#include <errno.h>
#include <ctype.h>
#include <stdlib.h>

#include "acl.h"
#include "annotate.h"
#include "append.h"
#include "assert.h"
#include "charset.h"
#include "conversations.h"
#include "dlist.h"
#include "exitcodes.h"
#include "hash.h"
#include "hashu64.h"
#include "imap_err.h"
#include "global.h"
#include "times.h"
#include "imapd.h"
#include "cyr_lock.h"
#include "lsort.h"
#include "mailbox.h"
#include "map.h"
#include "message.h"
#include "parseaddr.h"
#include "search_engines.h"
#include "seen.h"
#include "statuscache.h"
#include "strhash.h"
#include "stristr.h"
#include "util.h"
#include "ptrarray.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

#include "index.h"
#include "sync_log.h"

/* Forward declarations */
static void index_refresh(struct index_state *state);
static void index_tellexists(struct index_state *state);
static int index_lock(struct index_state *state);
static void index_unlock(struct index_state *state);

int index_writeseen(struct index_state *state);
void index_fetchmsg(struct index_state *state,
		    const char *msg_base, unsigned long msg_size,
		    unsigned offset, unsigned size,
		    unsigned start_octet, unsigned octet_count);
static int index_fetchsection(struct index_state *state, const char *resp,
			      const char *msg_base, unsigned long msg_size,
			      char *section,
			      const char *cachestr, unsigned size,
			      unsigned start_octet, unsigned octet_count);
static void index_fetchfsection(struct index_state *state,
				const char *msg_base, unsigned long msg_size,
				struct fieldlist *fsection,
				const char *cachestr,
				unsigned start_octet, unsigned octet_count);
static char *index_readheader(const char *msg_base, unsigned long msg_size,
			      unsigned offset, unsigned size);
static void index_fetchheader(struct index_state *state,
			      const char *msg_base, unsigned long msg_size,
			      unsigned size,
			      const strarray_t *headers,
			      const strarray_t *headers_not);
static void index_fetchcacheheader(struct index_state *state, struct index_record *record, 
				   const strarray_t *headers, unsigned start_octet, 
				   unsigned octet_count);
static void index_listflags(struct index_state *state);
static void index_fetchflags(struct index_state *state, uint32_t msgno);
static int index_search_evaluate(struct index_state *state,
				 struct searchargs *searchargs,
				 uint32_t msgno, struct mapfile *msgfile);
static int index_searchmsg(char *substr, comp_pat *pat,
			   struct mapfile *msgfile,
			   int skipheader, const char *cachestr);
static int index_searchheader(char *name, char *substr, comp_pat *pat,
			      struct mapfile *msgfile,
			      int size);
static int index_searchcacheheader(struct index_state *state, uint32_t msgno, char *name, char *substr,
				   comp_pat *pat);
static int _index_search(unsigned **msgno_list, struct index_state *state,
			 struct searchargs *searchargs,
			 modseq_t *highestmodseq);

static int index_copysetup(struct index_state *state, uint32_t msgno,
			   struct copyargs *copyargs, int is_same_user);
static int index_storeflag(struct index_state *state, uint32_t msgno,
			   struct storeargs *storeargs);
static int index_store_annotation(struct index_state *state, uint32_t msgno,
			   struct storeargs *storeargs);
static int index_fetchreply(struct index_state *state, uint32_t msgno,
			    const struct fetchargs *fetchargs);
static void index_printflags(struct index_state *state, uint32_t msgno,
			     int usinguid, int printmodseq);
static char *get_localpart_addr(const char *header);
static char *get_displayname(const char *header);
static char *index_extract_subject(const char *subj, size_t len, int *is_refwd);
static char *_index_extract_subject(char *s, int *is_refwd);
static void index_get_ids(MsgData *msgdata,
			  char *envtokens[], const char *headers, unsigned size);
static MsgData **index_msgdata_load(struct index_state *state, unsigned *msgno_list, int n,
				    struct sortcrit *sortcrit,
				    unsigned int anchor, int *found_anchor);
static void index_msgdata_free(MsgData **, unsigned int);

static int index_sort_compare(MsgData *md1, MsgData *md2,
			      struct sortcrit *call_data);
static int index_sort_compare_qsort(const void *v1, const void *v2);

static void *index_thread_getnext(Thread *thread);
static void index_thread_setnext(Thread *thread, Thread *next);
static int index_thread_compare(Thread *t1, Thread *t2,
				struct sortcrit *call_data);
static void index_thread_orderedsubj(struct index_state *state,
				     unsigned *msgno_list, unsigned int nmsg,
				     int usinguid);
static void index_thread_sort(Thread *root, struct sortcrit *sortcrit);
static void index_thread_print(struct index_state *state,
			       Thread *threads, int usinguid);
static void index_thread_ref(struct index_state *state,
			     unsigned *msgno_list, unsigned int nmsg,
			     int usinguid);

static struct seqset *_parse_sequence(struct index_state *state,
				      const char *sequence, int usinguid);
static void massage_header(char *hdr);

/* NOTE: Make sure these are listed in CAPABILITY_STRING */
static const struct thread_algorithm thread_algs[] = {
    { "ORDEREDSUBJECT", index_thread_orderedsubj },
    { "REFERENCES", index_thread_ref },
    { NULL, NULL }
};

static struct sortcrit *the_sortcrit;


/*
 * A mailbox is about to be closed.
 */
void index_close(struct index_state **stateptr)
{
    unsigned i;
    struct index_state *state = *stateptr;

    if (!state) return;

    free(state->userid);
    free(state->map);
    for (i = 0; i < MAX_USER_FLAGS; i++)
	free(state->flagname[i]);
    mailbox_close(&state->mailbox);
    free(state);

    *stateptr = NULL;
}

/*
 * A new mailbox has been selected, map it into memory and do the
 * initial CHECK.
 */
int index_open(const char *name, struct index_init *init,
	       struct index_state **stateptr)
{
    int r;
    struct index_state *state = xzmalloc(sizeof(struct index_state));

    if (init) {
	if (init->examine_mode) {
	    r = mailbox_open_irl(name, &state->mailbox);
	    if (r) goto fail;
	} else {
	    r = mailbox_open_iwl(name, &state->mailbox);
	    if (r) goto fail;
	}
	state->myrights = cyrus_acl_myrights(init->authstate,
					     state->mailbox->acl);
	if (init->examine_mode)
	    state->myrights &= ~ACL_READ_WRITE;

	state->authstate = init->authstate;
	state->userid = xstrdupnull(init->userid);

	state->internalseen = mailbox_internal_seen(state->mailbox,
						    state->userid);
	state->keepingseen = (state->myrights & ACL_SETSEEN);
	state->examining = init->examine_mode;

	state->out = init->out;
	state->qresync = init->qresync;
	state->want_expunged = init->want_expunged;
    }
    else {
	r = mailbox_open_iwl(name, &state->mailbox);
	if (r) goto fail;
    }

    /* initialise the index_state */
    index_refresh(state);

    /* have to get the vanished list while we're still locked */
    if (init)
	init->vanishedlist = index_vanished(state, &init->vanished);

    index_unlock(state);

    *stateptr = state;

    return 0;

fail:
    free(state->mailbox);
    free(state);
    return r;
}

int index_expunge(struct index_state *state, char *sequence,
		  int need_deleted)
{
    int r;
    uint32_t msgno;
    struct index_map *im;
    struct seqset *seq = NULL;
    int numexpunged = 0;

    r = index_lock(state);
    if (r) return r;

    /* XXX - earlier list if the sequence names UIDs that don't exist? */
    seq = _parse_sequence(state, sequence, 1);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];

	if (im->record.system_flags & FLAG_EXPUNGED)
	    continue; /* already expunged */

	if (need_deleted && !(im->record.system_flags & FLAG_DELETED))
	    continue; /* no \Deleted flag */

	/* if there is a sequence list, check it */
	if (sequence && !seqset_ismember(seq, im->record.uid))
	    continue; /* not in the list */

	if (!im->isseen)
	    state->numunseen--;

	if (im->isrecent)
	    state->numrecent--;

	/* set the flags */
	im->record.system_flags |= FLAG_DELETED | FLAG_EXPUNGED;
	numexpunged++;

	r = mailbox_rewrite_index_record(state->mailbox, &im->record);

	if (r) break;
    }

    seqset_free(seq);

    /* unlock before responding */
    index_unlock(state);

    if (!r && (numexpunged > 0)) {
	syslog(LOG_NOTICE, "Expunged %d messages from %s",
	       numexpunged, state->mailbox->name);
    }
    return r;
}

char *index_buildseen(struct index_state *state, const char *oldseenuids)
{
    struct seqset *outlist;
    uint32_t msgno;
    unsigned oldmax;
    struct index_map *im;
    char *out;

    outlist = seqset_init(0, SEQ_MERGE); 
    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	seqset_add(outlist, im->record.uid, im->isseen);
    }

    /* there may be future already seen UIDs that this process isn't
     * allowed to know about, but we can't blat them either!  This is
     * a massive pain... */
    oldmax = seq_lastnum(oldseenuids, NULL);
    if (oldmax > state->last_uid) {
	struct seqset *seq = seqset_parse(oldseenuids, NULL, oldmax);
	uint32_t uid;

	/* for each future UID, copy the state in the old seenuids */
	for (uid = state->last_uid + 1; uid <= oldmax; uid++)
	    seqset_add(outlist, uid, seqset_ismember(seq, uid));

	seqset_free(seq);
    }

    out = seqset_cstring(outlist);
    seqset_free(outlist);

    return out;
}

int index_writeseen(struct index_state *state)
{
    int r;
    struct seen *seendb = NULL;
    struct seendata oldsd = SEENDATA_INITIALIZER;
    struct seendata sd = SEENDATA_INITIALIZER;
    struct mailbox *mailbox = state->mailbox;

    if (!state->seen_dirty)
	return 0;

    state->seen_dirty = 0;

    /* only examining, can't write any changes */
    if (state->examining)
	return 0;

    /* already handled! Just update the header fields */
    if (state->internalseen) {
	mailbox_index_dirty(mailbox);
	mailbox->i.recenttime = time(0);
	if (mailbox->i.recentuid < state->last_uid)
	    mailbox->i.recentuid = state->last_uid;
	return 0;
    }

    r = seen_open(state->userid, SEEN_CREATE, &seendb);
    if (r) return r;

    r = seen_lockread(seendb, mailbox->uniqueid, &oldsd);
    if (r) {
	oldsd.lastread = 0;
	oldsd.lastuid = 0;
	oldsd.lastchange = 0;
	oldsd.seenuids = xstrdup("");
    }

    /* fields of interest... */
    sd.lastuid = oldsd.lastuid;
    sd.seenuids = index_buildseen(state, oldsd.seenuids);
    if (!sd.seenuids) sd.seenuids = xstrdup("");

    /* make comparison only catch some changes */
    sd.lastread = oldsd.lastread;
    sd.lastchange = oldsd.lastchange;

    /* update \Recent lowmark */
    if (sd.lastuid < state->last_uid)
	sd.lastuid = state->last_uid;

    /* only commit if interesting fields have changed */
    if (!seen_compare(&sd, &oldsd)) {
	sd.lastread = time(NULL);
	sd.lastchange = mailbox->i.last_appenddate;
	r = seen_write(seendb, mailbox->uniqueid, &sd);
    }

    seen_close(&seendb);

    seen_freedata(&oldsd);
    seen_freedata(&sd);

    return r;
}

/* caller must free the list with seqset_free() when done */
static struct seqset *_readseen(struct index_state *state, unsigned *recentuid)
{
    struct mailbox *mailbox = state->mailbox;
    struct seqset *seenlist = NULL;

    /* Obtain seen information */
    if (state->internalseen) {
	*recentuid = mailbox->i.recentuid;
    }
    else if (state->userid) {
	struct seen *seendb = NULL;
	struct seendata sd = SEENDATA_INITIALIZER;
	int r;

	r = seen_open(state->userid, SEEN_CREATE, &seendb);
	if (!r) r = seen_read(seendb, mailbox->uniqueid, &sd);
	seen_close(&seendb);

	/* handle no seen DB gracefully */
	if (r) {
	    *recentuid = mailbox->i.last_uid;
	    prot_printf(state->out, "* OK (seen state failure) %s: %s\r\n",
		   error_message(IMAP_NO_CHECKPRESERVE), error_message(r));
	    syslog(LOG_ERR, "Could not open seen state for %s (%s)",
		   state->userid, error_message(r));
	}
	else {
	    *recentuid = sd.lastuid;
	    seenlist = seqset_parse(sd.seenuids, NULL, *recentuid);
	    seen_freedata(&sd);
	}
    }
    else {
	*recentuid = mailbox->i.last_uid; /* nothing is recent! */
    }

    return seenlist;
}

void index_refresh(struct index_state *state)
{
    struct mailbox *mailbox = state->mailbox;
    uint32_t recno;
    uint32_t msgno = 1;
    uint32_t firstnotseen = 0;
    uint32_t numrecent = 0;
    uint32_t numunseen = 0;
    uint32_t recentuid;
    struct index_map *im;
    modseq_t delayed_modseq = 0;
    uint32_t need_records;
    struct seqset *seenlist;

    if (state->want_expunged) {
	/* could need the lot! */
	need_records = mailbox->i.num_records;
    }
    else if (state->num_records) {
	need_records = mailbox->i.num_records -
		       state->num_records + state->exists;
    }
    else {
	/* init case */
	need_records = mailbox->i.exists;
    }

    /* make sure we have space */
    if (need_records >= state->mapsize) {
	state->mapsize = (need_records | 0xff) + 1; /* round up 1-256 */
	state->map = xrealloc(state->map,
			      state->mapsize * sizeof(struct index_map));
    }

    seenlist = _readseen(state, &recentuid);

    /* already known records - flag updates */
    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	if (mailbox_read_index_record(mailbox, im->record.recno, &im->record))
	    continue; /* bogus read... should probably be fatal */

	/* ignore expunged messages */
	if (!state->want_expunged &&
	    (im->record.system_flags & FLAG_EXPUNGED)) {
	    /* http://www.rfc-editor.org/errata_search.php?rfc=5162
	     * Errata ID: 1809 - if there are expunged records we
	     * aren't telling about, need to make the highestmodseq
	     * be one lower so the client can safely resync */
	    if (!delayed_modseq || im->record.modseq < delayed_modseq)
		delayed_modseq = im->record.modseq - 1;
	    continue;
	}

	/* re-calculate seen flags */
	if (state->internalseen)
	    im->isseen = (im->record.system_flags & FLAG_SEEN) ? 1 : 0;
	else
	    im->isseen = seqset_ismember(seenlist, im->record.uid);

	/* track select values */
	if (!im->isseen) {
	    numunseen++;
	    if (!firstnotseen)
		firstnotseen = msgno;
	}
	if (im->isrecent) {
	    /* we don't need to dirty seen here, it's a refresh */
	    numrecent++;
	}
    }

    /* new records? */
    for (recno = state->num_records + 1; recno <= mailbox->i.num_records; recno++) {
	im = &state->map[msgno-1];
	if (mailbox_read_index_record(mailbox, recno, &im->record))
	    continue; /* bogus read... should probably be fatal */
	if (!state->want_expunged &&
	    (im->record.system_flags & FLAG_EXPUNGED))
	    continue;

	/* make sure we don't overflow the memory we mapped */
	if (msgno >= state->mapsize) {
	    char buf[2048];
	    sprintf(buf, "Exists wrong %u %u %u %u", msgno,
		    state->mapsize, mailbox->i.exists, mailbox->i.num_records);
	    fatal(buf, EC_IOERR);
	}

	/* calculate flags */
	if (state->internalseen)
	    im->isseen = (im->record.system_flags & FLAG_SEEN) ? 1 : 0;
	else
	    im->isseen = seqset_ismember(seenlist, im->record.uid);
	im->isrecent = (im->record.uid > recentuid) ? 1 : 0;

	/* track select values */
	if (!im->isseen) {
	    numunseen++;
	    if (!firstnotseen)
		firstnotseen = msgno;
	}
	if (im->isrecent) {
	    numrecent++;
	    state->seen_dirty = 1;
	}

	/* don't auto-tell */
	im->told_modseq = im->record.modseq;

	msgno++;
    }

    seqset_free(seenlist);

    /* update the header tracking data */
    state->oldexists = state->exists; /* we last knew about this many */
    state->exists = msgno - 1; /* we actually got this many */
    state->delayed_modseq = delayed_modseq;
    state->highestmodseq = mailbox->i.highestmodseq;
    state->last_uid = mailbox->i.last_uid;
    state->num_records = mailbox->i.num_records;
    state->firstnotseen = firstnotseen;
    state->numunseen = numunseen;
    state->numrecent = numrecent;
}

modseq_t index_highestmodseq(struct index_state *state)
{
    if (state->delayed_modseq)
	return state->delayed_modseq;
    return state->highestmodseq;
}

void index_select(struct index_state *state, struct index_init *init)
{
    index_tellexists(state);

    /* always print flags */
    index_checkflags(state, 1, 1);

    if (state->firstnotseen)
	prot_printf(state->out, "* OK [UNSEEN %u] Ok\r\n", 
		    state->firstnotseen);
    prot_printf(state->out, "* OK [UIDVALIDITY %u] Ok\r\n",
		state->mailbox->i.uidvalidity);
    prot_printf(state->out, "* OK [UIDNEXT %lu] Ok\r\n",
		state->last_uid + 1);
    prot_printf(state->out, "* OK [HIGHESTMODSEQ " MODSEQ_FMT "] Ok\r\n",
		state->highestmodseq);
    prot_printf(state->out, "* OK [URLMECH INTERNAL] Ok\r\n");

    /*
     * RFC5257.  Note that we must report a maximum size for annotations
     * but we don't enforce any such limit, so pick a "large" number.
     */
    prot_printf(state->out, "* OK [ANNOTATIONS %u] Ok\r\n", 64*1024);

    if (init->vanishedlist) {
	char *vanished;
	const char *sequence = NULL;
	struct seqset *seq = NULL;
	struct index_map *im;
	uint32_t msgno;

	/* QRESYNC response:
	 * UID FETCH seq FLAGS (CHANGEDSINCE modseq VANISHED)
	  */

	vanished = seqset_cstring(init->vanishedlist);
	if (vanished) {
	    prot_printf(state->out, "* VANISHED (EARLIER) %s\r\n", vanished);
	    free(vanished);
	}

	sequence = init->vanished.sequence;
	if (sequence) seq = _parse_sequence(state, sequence, 1);
	for (msgno = 1; msgno <= state->exists; msgno++) {
	    im = &state->map[msgno-1];
	    if (sequence && !seqset_ismember(seq, im->record.uid))
		continue;
	    if (im->record.modseq <= init->vanished.modseq)
		continue;
	    index_printflags(state, msgno, 1, 0);
	}
	seqset_free(seq);
    }
}

/*
 * Check for and report updates
 */
int index_check(struct index_state *state, int usinguid, int printuid)
{
    struct mailbox *mailbox = state->mailbox;
    int r;

    r = mailbox_lock_index(mailbox, LOCK_EXCLUSIVE);

    /* Check for deleted mailbox  */
    if (r == IMAP_MAILBOX_NONEXISTENT) {
	/* Mailbox has been (re)moved */
	if (config_getswitch(IMAPOPT_DISCONNECT_ON_VANISHED_MAILBOX)) {
	    syslog(LOG_WARNING,
		   "Mailbox %s has been (re)moved out from under client",
		   mailbox->name);
	    fatal("Mailbox has been (re)moved", EC_IOERR);
	}

	if (state->exists && state->qresync) {
	    /* XXX - is it OK to just expand to entire possible range? */
	    prot_printf(state->out, "* VANISHED 1:%lu\r\n", state->last_uid);
	}
	else {
	    int exists;
	    for (exists = state->exists; exists > 0; exists--) {
		prot_printf(state->out, "* 1 EXPUNGE\r\n");
	    }
	}

	state->exists = 0;
	return IMAP_MAILBOX_NONEXISTENT;
    }

    if (r) return r;

    /* if highestmodseq has changed, read updates */
    if (state->highestmodseq != mailbox->i.highestmodseq)
	index_refresh(state);

    index_tellchanges(state, usinguid, printuid, 0);

#if TOIMSP
    if (state->firstnotseen) {
	toimsp(mailbox->name, mailbox->i.uidvalidity, "SEENsnn", state->userid,
	       0, mailbox->i.recenttime, 0);
    }
    else {
	toimsp(mailbox->name, mailbox->i.uidvalidity, "SEENsnn", state->userid,
	       mailbox->last_uid, mailbox->i.recenttime, 0);
    }
#endif

    index_unlock(state);

    return r;
}

/*
 * Perform UID FETCH (VANISHED) on a sequence.
 */
struct seqset *index_vanished(struct index_state *state,
			      struct vanished_params *params)
{
    struct mailbox *mailbox = state->mailbox;
    struct index_record record;
    struct seqset *outlist;
    struct seqset *seq;
    uint32_t recno;

    /* check uidvalidity match */
    if (params->uidvalidity_is_max) {
	if (params->uidvalidity < mailbox->i.uidvalidity) return NULL;
    }
    else {
	if (params->uidvalidity != mailbox->i.uidvalidity) return NULL;
    }

    /* No recently expunged messages */
    if (params->modseq >= state->highestmodseq) return NULL;

    outlist = seqset_init(0, SEQ_SPARSE);
    seq = _parse_sequence(state, params->sequence, 1);

    /* XXX - use match_seq and match_uid */

    if (params->modseq >= mailbox->i.deletedmodseq) {
	/* all records are significant */
	/* List only expunged UIDs with MODSEQ > requested */
	for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	    if (mailbox_read_index_record(mailbox, recno, &record))
		continue;
	    if (!(record.system_flags & FLAG_EXPUNGED))
		continue;
	    if (record.modseq <= params->modseq)
		continue;
	    if (!params->sequence || seqset_ismember(seq, record.uid))
		seqset_add(outlist, record.uid, 1);
	}
    }
    else {
	unsigned prevuid = 0;
	struct seqset *msgnolist;
	struct seqset *uidlist;
	uint32_t msgno;
	unsigned uid;

	syslog(LOG_NOTICE, "inefficient qresync ("
	       MODSEQ_FMT " > " MODSEQ_FMT ") %s",
	       mailbox->i.deletedmodseq, params->modseq,
	       mailbox->name);

	recno = 1;

	/* use the sequence to uid mapping provided by the client to
	 * skip over any initial matches - see RFC 5162 section 3.1 */
	if (params->match_seq && params->match_uid) {
	    msgnolist = _parse_sequence(state, params->match_seq, 0);
	    uidlist = _parse_sequence(state, params->match_uid, 1);
	    while ((msgno = seqset_getnext(msgnolist)) != 0) {
		uid = seqset_getnext(uidlist);
		/* first non-match, we'll start here */
		if (state->map[msgno-1].record.uid != uid)
		    break;
		/* ok, they matched - so we can start at the recno and UID
		 * first past the match */
		prevuid = uid;
		recno = state->map[msgno-1].record.recno + 1;
	    }
	    seqset_free(msgnolist);
	    seqset_free(uidlist);
	}

	/* possible efficiency improvement - use "seq_getnext" on seq
	 * to avoid incrementing through every single number for prevuid.
	 * Only really an issue if there's a giant block of thousands of
	 * expunged messages.  Only likely to be seen in the wild if
	 * last_uid winds up being bumped up a few million by a bug... */

	/* for the rest of the mailbox, we're just going to have to assume
	 * every record in the requested range which DOESN'T exist has been
	 * expunged, so build a complete sequence */
	for (; recno <= mailbox->i.num_records; recno++) {
	    if (mailbox_read_index_record(mailbox, recno, &record))
		continue;
	    if (record.system_flags & FLAG_EXPUNGED)
		continue;
	    while (++prevuid < record.uid) {
		if (!params->sequence || seqset_ismember(seq, prevuid))
		    seqset_add(outlist, prevuid, 1);
	    }
	    prevuid = record.uid;
	}

	/* include the space past the final record up to last_uid as well */
	while (++prevuid <= mailbox->i.last_uid) {
	    if (!params->sequence || seqset_ismember(seq, prevuid))
		seqset_add(outlist, prevuid, 1);
	}
    }

    seqset_free(seq);

    return outlist;
}

static int _fetch_setseen(struct index_state *state, uint32_t msgno)
{
    struct index_map *im = &state->map[msgno-1];
    int r;

    /* already seen */
    if (im->isseen)
	return 0;

    /* no rights to change it */
    if (!(state->myrights & ACL_SETSEEN))
	return 0;

    /* store in the record if it's internal seen */
    if (state->internalseen)
	im->record.system_flags |= FLAG_SEEN;

    /* need to bump modseq anyway, so always rewrite it */
    r = mailbox_rewrite_index_record(state->mailbox, &im->record);
    if (r) return r;

    /* track changes internally */
    state->numunseen--;
    state->seen_dirty = 1;
    im->isseen = 1;

    /* RFC2060 says:
     * The \Seen flag is implicitly set; if this causes
     * the flags to change they SHOULD be included as part
     * of the FETCH responses.   This is handled later by
     * always including flags if the modseq has changed.
     */

    return 0;
}

/* seq can be NULL - means "ALL" */
void index_fetchresponses(struct index_state *state,
			  struct seqset *seq,
			  int usinguid,
			  const struct fetchargs *fetchargs,
			  int *fetchedsomething)
{
    uint32_t msgno, start, end;
    uint32_t checkval;
    struct index_map *im;
    int fetched = 0;
    annotate_db_t *annot_db = NULL;

    /* Keep an open reference on the per-mailbox db to avoid
     * doing too many slow database opens during the fetch */
    if ((fetchargs->fetchitems & FETCH_ANNOTATION))
	annotate_getdb(state->mailbox->name, &annot_db);

    start = 1;
    end = state->exists;

    /* compress the search range down if a sequence was given */
    if (seq) {
	unsigned first = seqset_first(seq);
	unsigned last = seqset_last(seq);

	if (usinguid) {
	    if (first > 1)
		start = index_finduid(state, first);
	    if (first == last)
		end = start;
	    else if (last < state->last_uid)
		end = index_finduid(state, last);
	}
	else {
	    start = first;
	    end = last;
	}
    }

    /* make sure we didn't go outside the range! */
    if (start < 1) start = 1;
    if (end > state->exists) end = state->exists;

    for (msgno = start; msgno <= end; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->record.uid : msgno;
	if (seq && !seqset_ismember(seq, checkval))
	    continue;
	if (index_fetchreply(state, msgno, fetchargs))
	    break;
	fetched = 1;
    }

    if (fetchedsomething) *fetchedsomething = fetched;
    annotate_putdb(&annot_db);
}

/*
 * Perform a FETCH-related command on a sequence.
 * Fetchedsomething argument is 0 if nothing was fetched, 1 if something was
 * fetched.  (A fetch command that fetches nothing is not a valid fetch
 * command.)
 */
int index_fetch(struct index_state *state,
		const char *sequence,
		int usinguid,
		const struct fetchargs *fetchargs,
		int *fetchedsomething)
{
    struct seqset *seq;
    struct seqset *vanishedlist = NULL;
    struct index_map *im;
    unsigned checkval;
    uint32_t msgno;
    int r;

    r = index_lock(state);
    if (r) return r;

    seq = _parse_sequence(state, sequence, usinguid);

    /* set the \Seen flag if necessary - while we still have the lock */
    if (fetchargs->fetchitems & FETCH_SETSEEN && !state->examining) {
	for (msgno = 1; msgno <= state->exists; msgno++) {
	    im = &state->map[msgno-1];
	    checkval = usinguid ? im->record.uid : msgno;
	    if (!seqset_ismember(seq, checkval))
		continue;
	    r = _fetch_setseen(state, msgno);   
	    if (r) break;
	}
    }

    if (fetchargs->vanished) {
	struct vanished_params v;
	v.sequence = sequence;;
	v.uidvalidity = state->mailbox->i.uidvalidity;
	v.modseq = fetchargs->changedsince;
	v.match_seq = fetchargs->match_seq;
	v.match_uid = fetchargs->match_uid;
	/* XXX - return error unless usinguid? */
	vanishedlist = index_vanished(state, &v);
    }

    index_unlock(state);

    index_checkflags(state, 1, 0);

    if (vanishedlist && vanishedlist->len) {
	char *vanished = seqset_cstring(vanishedlist);
	prot_printf(state->out, "* VANISHED (EARLIER) %s\r\n", vanished);
	free(vanished);
    }

    seqset_free(vanishedlist);

    index_fetchresponses(state, seq, usinguid, fetchargs, fetchedsomething);

    seqset_free(seq);

    index_tellchanges(state, usinguid, usinguid, 0);

    return r;
}

/*
 * Perform a STORE command on a sequence
 */
int index_store(struct index_state *state, char *sequence,
		struct storeargs *storeargs)
{
    struct mailbox *mailbox = state->mailbox;
    int i, r = 0;
    uint32_t msgno;
    unsigned checkval;
    int userflag;
    struct seqset *seq;
    struct index_map *im;
    const strarray_t *flags = &storeargs->flags;

    /* First pass at checking permission */
    if ((storeargs->seen && !(state->myrights & ACL_SETSEEN)) ||
	((storeargs->system_flags & FLAG_DELETED) &&
	 !(state->myrights & ACL_DELETEMSG)) ||
	(((storeargs->system_flags & ~FLAG_DELETED) || flags->count) &&
	 !(state->myrights & ACL_WRITE))) {
	return IMAP_PERMISSION_DENIED;
    }

    r = index_lock(state);
    if (r) return r;

    seq = _parse_sequence(state, sequence, storeargs->usinguid);

    for (i = 0; i < flags->count ; i++) {
	r = mailbox_user_flag(mailbox, flags->data[i], &userflag, 1);
	if (r) goto out;
	storeargs->user_flags[userflag/32] |= 1<<(userflag&31);
    }

    storeargs->update_time = time((time_t *)0);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = storeargs->usinguid ? im->record.uid : msgno;
	if (!seqset_ismember(seq, checkval))
	    continue;

	/* if it's expunged already, skip it now */
	if (im->record.system_flags & FLAG_EXPUNGED)
	    continue;

	/* if it's changed already, skip it now */
	if (im->record.modseq > storeargs->unchangedsince) {
	    if (!storeargs->modified) {
		unsigned int maxval = (storeargs->usinguid ?
					state->last_uid : state->exists);
		storeargs->modified = seqset_init(maxval, SEQ_SPARSE);
	    }
	    seqset_add(storeargs->modified,
		       (storeargs->usinguid ? im->record.uid : msgno),
		       /*ismember*/1);
	    continue;
	}

	switch (storeargs->operation) {
	case STORE_ADD_FLAGS:
	case STORE_REMOVE_FLAGS:
	case STORE_REPLACE_FLAGS:
	    r = index_storeflag(state, msgno, storeargs);
	    break;

	case STORE_ANNOTATION:
	    r = index_store_annotation(state, msgno, storeargs);
	    break;

	default:
	    r = IMAP_INTERNAL;
	    break;
	}
	if (r) goto out;
    }

out:
    if (storeargs->operation == STORE_ANNOTATION && r)
	annotate_state_abort(&state->mailbox->annot_state);
    seqset_free(seq);
    index_unlock(state);
    index_tellchanges(state, storeargs->usinguid, storeargs->usinguid,
		      (storeargs->unchangedsince != ~0ULL));

    return r;
}


static void prefetch_messages(struct index_state *state,
			      struct seqset *seq,
			      int usinguid)
{
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im;
    unsigned checkval;
    uint32_t msgno;
    char *fname;
    int fd;

    syslog(LOG_ERR, "Prefetching initial parts of messages\n");

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->record.uid : msgno;
	if (!seqset_ismember(seq, checkval))
	    continue;

	fname = mailbox_message_fname(mailbox, im->record.uid);
	if (!fname)
	    continue;

	fd = open(fname, O_RDONLY, 0);
	if (fd < 0)
	    continue;

	posix_fadvise(fd, 0, 16384, POSIX_FADV_WILLNEED);
	close(fd);
    }
}


/*
 * Perform the XRUNANNOTATOR command which runs the
 * annotator callout for each message in the given sequence.
 */
int index_run_annotator(struct index_state *state,
			const char *sequence, int usinguid,
			struct namespace *namespace, int isadmin)
{
    struct mailbox *mailbox = state->mailbox;
    struct seqset *seq = NULL;
    struct index_map *im;
    unsigned checkval;
    uint32_t msgno;
    struct appendstate as;
    int r = 0;

    /* We do the acl check here rather than in append_setup_mbox()
     * to account for the EXAMINE command where state->myrights has
     * fewer rights than the ACL actually grants */
    if (!(state->myrights & (ACL_WRITE|ACL_ANNOTATEMSG)))
	return IMAP_PERMISSION_DENIED;

    if (!config_getstring(IMAPOPT_ANNOTATION_CALLOUT))
	return 0;

    r = index_lock(state);
    if (r) return r;

    mailbox_ref(state->mailbox);
    r = append_setup_mbox(&as, state->mailbox,
			  state->userid, state->authstate,
			  0, NULL, namespace, isadmin);
    if (r) goto out;

    seq = _parse_sequence(state, sequence, usinguid);
    if (!seq) goto out;

    prefetch_messages(state, seq, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->record.uid : msgno;
	if (!seqset_ismember(seq, checkval))
	    continue;

	/* if it's expunged already, skip it now */
	if (im->record.system_flags & FLAG_EXPUNGED)
	    continue;

	r = append_run_annotator(&as, &im->record);
	if (r) goto out;

	r = mailbox_rewrite_index_record(mailbox, &im->record);
	if (r) goto out;
    }

out:
    if (!r) {
	/* There's a delicate dance involved in shutting all
	 * this down without double-unlocking the mailbox; the
	 * trick is to give append_commit() a non-NULL mailbox**
	 * to avoid it calling mailbox_close() too early. */
	struct mailbox *mailbox = NULL;
	append_commit(&as, &mailbox);
	/* it turns out that index_unlock() really needs to be
	 * called with a locked mailbox, if the seen data is dirty */
	index_unlock(state);
	mailbox_close(&mailbox);
    }
    else {
	/* append abort unlocks the mailbox */
	append_abort(&as);
    }
    seqset_free(seq);
    index_tellchanges(state, usinguid, usinguid, 1);
    return r;
}

static int index_scan_work(const char *s, unsigned long len,
			   const char *match, unsigned long min)
{
    while (len > min) {
        if (!strncasecmp(s, match, min)) return(1);
        s++;
        len--;
    }
    return(0);
}

/*
 * Guts of the SCAN command, lifted from _index_search()
 *
 * Returns 1 if we get a hit, otherwise returns 0.
 */
int index_scan(struct index_state *state, const char *contents)
{
    unsigned *msgno_list;
    uint32_t msgno;
    int n = 0;
    int listindex;
    int listcount;
    struct searchargs searchargs;
    struct strlist strlist;
    unsigned long length;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im;

    if (!(contents && contents[0])) return(0);

    if (index_check(state, 0, 0))
	return 0;

    if (state->exists <= 0) return 0;

    length = strlen(contents);

    memset(&searchargs, 0, sizeof(struct searchargs));
    searchargs.text = &strlist;

    /* Use US-ASCII to emulate fgrep */
    strlist.s = charset_convert(contents, charset_lookupname("US-ASCII"),
				charset_flags);
    strlist.p = charset_compilepat(strlist.s);
    strlist.next = NULL;

    msgno_list = (unsigned *) xmalloc(state->exists * sizeof(unsigned));

    listcount = search_prefilter_messages(msgno_list, state, &searchargs);

    for (listindex = 0; !n && listindex < listcount; listindex++) {
	struct mapfile msgfile = MAPFILE_INITIALIZER;
	msgno = msgno_list[listindex];
	im = &state->map[msgno-1];

	if (mailbox_map_message(mailbox, im->record.uid,
				&msgfile.base, &msgfile.size))
	    continue;

	n += index_scan_work(msgfile.base, msgfile.size, contents, length);

	mailbox_unmap_message(mailbox, im->record.uid,
			      &msgfile.base, &msgfile.size);
    }

    free(strlist.s);
    free(strlist.p);
    free(msgno_list);

    return n;
}

/*
 * Guts of the SEARCH command.
 * 
 * Returns message numbers in an array.  This function is used by
 * SEARCH, SORT and THREAD.
 */
static int _index_search(unsigned **msgno_list, struct index_state *state,
			 struct searchargs *searchargs,
			 modseq_t *highestmodseq)
{
    uint32_t msgno;
    int n = 0;
    int listindex, min;
    int listcount;
    struct index_map *im;

    if (state->exists <= 0) return 0;

    *msgno_list = (unsigned *) xmalloc(state->exists * sizeof(unsigned));

    /* OK, so I'm being a bit clever here. We fill the msgno list with
       a list of message IDs returned by the search engine. Then we
       scan through the list and store matching message IDs back into the
       list. This is OK because we only overwrite message IDs that we've
       already looked at. */
    listcount = search_prefilter_messages(*msgno_list, state, searchargs);

    if (searchargs->returnopts == SEARCH_RETURN_MAX) {
	/* If we only want MAX, then skip forward search,
	   and do complete reverse search */
	listindex = listcount;
	min = 0;
    } else {
	/* Otherwise use forward search, potentially skipping reverse search */
	listindex = 0;
	min = listcount;
    }

    /* Forward search.  Used for everything other than MAX-only */
    for (; listindex < listcount; listindex++) {
	msgno = (*msgno_list)[listindex];
	im = &state->map[msgno-1];

	/* expunged messages hardly ever match */
	if (!state->want_expunged && (im->record.system_flags & FLAG_EXPUNGED))
	    continue;

	if (index_search_evaluate(state, searchargs, msgno, NULL)) {
	    (*msgno_list)[n++] = msgno;
	    if (highestmodseq && im->record.modseq > *highestmodseq) {
		*highestmodseq = im->record.modseq;
	    }

	    /* See if we should short-circuit
	       (we want MIN, but NOT COUNT or ALL) */
	    if ((searchargs->returnopts & SEARCH_RETURN_MIN) &&
		!(searchargs->returnopts & SEARCH_RETURN_COUNT) &&
		!(searchargs->returnopts & SEARCH_RETURN_ALL)) {

		if (searchargs->returnopts & SEARCH_RETURN_MAX) {
		    /* If we want MAX, setup for reverse search */
		    min = listindex;
		}
		/* We're done */
		listindex = listcount;
		if (highestmodseq)
		    *highestmodseq = im->record.modseq;
	    }
	}
    }

    /* Reverse search.  Stops at previously found MIN (if any) */
    for (listindex = listcount; listindex > min; listindex--) {
	msgno = (*msgno_list)[listindex-1];
	im = &state->map[msgno-1];

	/* expunged messages hardly ever match */
	if (!state->want_expunged && (im->record.system_flags & FLAG_EXPUNGED))
	    continue;

	if (index_search_evaluate(state, searchargs, msgno, NULL)) {
	    (*msgno_list)[n++] = msgno;
	    if (highestmodseq && im->record.modseq > *highestmodseq) {
		*highestmodseq = im->record.modseq;
	    }
	    /* We only care about MAX, so we're done on first match */
	    listindex = 0;
	}
    }

    /* if we didn't find any matches, free msgno_list */
    if (!n && *msgno_list) {
	free(*msgno_list);
	*msgno_list = NULL;
    }

    return n;
}

unsigned index_getuid(struct index_state *state, uint32_t msgno) {
  return state->map[msgno-1].record.uid;
}

/* 'uid_list' is malloc'd string representing the hits from searchargs;
   returns number of hits */
int index_getuidsequence(struct index_state *state,
			 struct searchargs *searchargs,
			 unsigned **uid_list)
{
    unsigned *msgno_list;
    int i, n;

    n = _index_search(&msgno_list, state, searchargs, NULL);
    if (n == 0) {
	*uid_list = NULL;
	return 0;
    }

    *uid_list = msgno_list;

    /* filthy in-place replacement */
    for (i = 0; i < n; i++)
	(*uid_list)[i] = index_getuid(state, msgno_list[i]);

    return n;
}

static int index_lock(struct index_state *state)
{
    int r = mailbox_lock_index(state->mailbox, LOCK_EXCLUSIVE);
    if (r) return r;

    /* if highestmodseq has changed, read updates */
    if (state->highestmodseq != state->mailbox->i.highestmodseq)
	index_refresh(state);

    return 0;
}

int index_status(struct index_state *state, struct statusdata *sdata)
{
    int items = STATUS_MESSAGES | STATUS_UIDNEXT | STATUS_UIDVALIDITY |
		STATUS_HIGHESTMODSEQ | STATUS_RECENT | STATUS_UNSEEN;
    statuscache_fill(sdata, state->userid, state->mailbox, items,
		     state->numrecent, state->numunseen);
    return 0;
}

static void index_unlock(struct index_state *state)
{
    /* XXX - errors */

    index_writeseen(state);

    /* grab the latest modseq */
    state->highestmodseq = state->mailbox->i.highestmodseq;

    if (config_getswitch(IMAPOPT_STATUSCACHE)) {
	struct statusdata sdata;
	index_status(state, &sdata);
	/* RECENT is zero for everyone else because we wrote a new
	 * recentuid! */
	sdata.recent = 0;
	mailbox_unlock_index(state->mailbox, &sdata);
    }
    else
	mailbox_unlock_index(state->mailbox, NULL);
}

/*
 * Performs a SEARCH command.
 * This is a wrapper around _index_search() which simply prints the results.
 */
int index_search(struct index_state *state, struct searchargs *searchargs,
		 int usinguid)
{
    unsigned *list = NULL;
    int i, n;
    modseq_t highestmodseq = 0;

    /* update the index */
    if (index_check(state, 0, 0))
	return 0;

    /* now do the search */
    n = _index_search(&list, state, searchargs, 
		      searchargs->modseq ? &highestmodseq : NULL);

    /* replace the values now */
    if (usinguid)
	for (i = 0; i < n; i++)
	    list[i] = state->map[list[i]-1].record.uid;

    if (searchargs->returnopts) {
	prot_printf(state->out, "* ESEARCH");
	if (searchargs->tag) {
	    prot_printf(state->out, " (TAG \"%s\")", searchargs->tag);
	}
	if (n) {
	    if (usinguid) prot_printf(state->out, " UID");
	    if (searchargs->returnopts & SEARCH_RETURN_MIN)
		prot_printf(state->out, " MIN %u", list[0]);
	    if (searchargs->returnopts & SEARCH_RETURN_MAX)
		prot_printf(state->out, " MAX %u", list[n-1]);
	    if (highestmodseq)
		prot_printf(state->out, " MODSEQ " MODSEQ_FMT, highestmodseq);
	    if (searchargs->returnopts & SEARCH_RETURN_ALL) {
		struct seqset *seq;
		char *str;

		/* Create a sequence-set */
		seq = seqset_init(0, SEQ_SPARSE);
		for (i = 0; i < n; i++)
		    seqset_add(seq, list[i], 1);

		if (seq->len) {
		    str = seqset_cstring(seq);
		    prot_printf(state->out, " ALL %s", str);
		    free(str);
		}

		seqset_free(seq);
	    }
	}
	if (searchargs->returnopts & SEARCH_RETURN_COUNT) {
	    prot_printf(state->out, " COUNT %u", n);
	}
    }
    else {
	prot_printf(state->out, "* SEARCH");

	for (i = 0; i < n; i++)
	    prot_printf(state->out, " %u", list[i]);

	if (highestmodseq)
	    prot_printf(state->out, " (MODSEQ " MODSEQ_FMT ")", highestmodseq);
    }

    if (n) free(list);

    prot_printf(state->out, "\r\n");

    return n;
}

/*
 * Performs a SORT command
 */
int index_sort(struct index_state *state, struct sortcrit *sortcrit,
	       struct searchargs *searchargs, int usinguid)
{
    unsigned *msgno_list;
    MsgData **msgdata = NULL;
    int mi;
    int nmsg;
    modseq_t highestmodseq = 0;
    int i, modseq = 0;

    /* update the index */
    if (index_check(state, 0, 0))
	return 0;

    if (searchargs->modseq) modseq = 1;
    else {
	for (i = 0; sortcrit[i].key != SORT_SEQUENCE; i++) {
	    if (sortcrit[i].key == SORT_MODSEQ) {
		modseq = 1;
		break;
	    }
	}
    }

    /* Search for messages based on the given criteria */
    nmsg = _index_search(&msgno_list, state, searchargs,
			 modseq ? &highestmodseq : NULL);

    prot_printf(state->out, "* SORT");

    if (nmsg) {
	/* Create/load the msgdata array */
	msgdata = index_msgdata_load(state, msgno_list, nmsg, sortcrit, 0, NULL);
	free(msgno_list);

	/* Sort the messages based on the given criteria */
	the_sortcrit = sortcrit;
	qsort(msgdata, nmsg, sizeof(MsgData *), index_sort_compare_qsort);

	/* Output the sorted messages */
	for (mi = 0 ; mi < nmsg ; mi++) {
	    MsgData *msg = msgdata[mi];
	    unsigned no = usinguid ? state->map[msg->msgno-1].record.uid
				   : msg->msgno;
	    prot_printf(state->out, " %u", no);
	}

	/* free the msgdata array */
	index_msgdata_free(msgdata, nmsg);
    }

    if (highestmodseq)
	prot_printf(state->out, " (MODSEQ " MODSEQ_FMT ")", highestmodseq);

    prot_printf(state->out, "\r\n");

    return nmsg;
}

static int is_mutable_sort(struct sortcrit *sortcrit)
{
    int i;

    if (!sortcrit) return 0;

    for (i = 0; sortcrit[i].key; i++) {
	switch (sortcrit[i].key) {
	    /* these are the mutable fields */
	    case SORT_ANNOTATION:
	    case SORT_MODSEQ:
	    case SORT_HASFLAG:
	    case SORT_CONVMODSEQ:
	    case SORT_CONVEXISTS:
	    case SORT_HASCONVFLAG:
		return 1;
	    default:
		break;
	}
    }

    return 0;
}

static int is_mutable_search(struct searchargs *searchargs)
{
    int i;
    struct searchsub *sub;

    if (!searchargs) return 0;

    /* flags are mutable */
    if (searchargs->system_flags_set)
	return 1;
    if (searchargs->system_flags_unset)
	return 1;
    for (i = 0; i < MAX_USER_FLAGS/32; i++) {
	if (searchargs->user_flags_set[i])
	    return 1;
	if (searchargs->user_flags_unset[i])
	    return 1;
    }
    if (searchargs->convflags)
	return 1;

    /* searches by per-user fields are mutable */
    if (searchargs->flags & SEARCH_MUTABLEFLAGS)
	return 1;

    /* modseq is mutable */
    if (searchargs->modseq)
	return 1;
    if (searchargs->convmodseq)
	return 1;

    /* annotations are mutable */
    if (searchargs->annotations)
	return 1;

    /* if any sub expression is mutable, this is mutable */
    for (sub = searchargs->sublist; sub; sub = sub->next) {
	if (is_mutable_search(sub->sub1))
	    return 1;
	if (is_mutable_search(sub->sub2))
	    return 1;
    }

    /* NOTE: older than 'N' days will be a mutable search of course,
     * but that fact isn't available down here - we only know the
     * date range itself, and that isn't mutable.  So if you need
     * immutable results, you'll need to maintain a fixed date range
     * up in the higher level */

    return 0;
}

/* This function will return a TRUE value if anything in the
 * sort or search criteria returns a MUTABLE ordering, i.e.
 * the user can take actions which will change the order in
 * which the results are returned.  For example, the base
 * case of UID sort and all messages is NOT mutable */
static int is_mutable_ordering(struct sortcrit *sortcrit,
			       struct searchargs *searchargs)
{
    if (is_mutable_sort(sortcrit))
	return 1;
    if (is_mutable_search(searchargs))
	return 1;
    return 0;
}

/*
 * Analyse @searchargs to discover how countable the results are
 * going to be.  By "countable" we mean "predictable from stored
 * state, without searching every message".  Currently that means
 *
 * in message mode:
 *    - total number of messages
 *    - number unseen messages
 *    - number seen messages (by inference)
 *    - number recent messages
 *    - number unrecent messages (by inference)
 * in conversation mode:
 *    - total number of conversations
 *    - number of conversations with unseen messages
 *    - number of conversations with no unseen messages (by inference)
 *
 * Returns a mask of SEARCH_* constants (e.g. SEARCH_SEEN_SET)
 * describing which countable attributes are specified by @searchargs.
 * The special value SEARCH_UNCOUNTED means that at least one uncounted
 * attribute was found.  Mask values with more than one bit set are
 * effectively uncountable.  A mask value of zero means that the search
 * program is empty, which is countable.
 */

#define SEARCH_NOT		(1<<29)
#define SEARCH_UNCOUNTED	(1<<30)
static unsigned int search_countability(const struct searchargs *searchargs)
{
    int i;
    unsigned int mask = 0;
    const struct searchsub *sub;

    if (!searchargs)
	return 0;

    /*
     * TODO: for SEARCH_SEEN_SET, SEARCH_SEEN_UNSET this is only correct
     * if the user is looking at his own mailbox.
     */
    mask |= (searchargs->flags & SEARCH_COUNTEDFLAGS);
    if ((searchargs->flags & ~SEARCH_COUNTEDFLAGS))
	mask |= SEARCH_UNCOUNTED;

    /* time and size based searches are not counted */
    if (searchargs->smaller || searchargs->larger)
	mask |= SEARCH_UNCOUNTED;
    if (searchargs->before || searchargs->after)
	mask |= SEARCH_UNCOUNTED;
    if (searchargs->sentbefore || searchargs->sentafter)
	mask |= SEARCH_UNCOUNTED;

    /* flags are not counted */
    if (searchargs->system_flags_set)
	mask |= SEARCH_UNCOUNTED;
    if (searchargs->system_flags_unset)
	mask |= SEARCH_UNCOUNTED;
    for (i = 0; i < MAX_USER_FLAGS/32; i++) {
	if (searchargs->user_flags_set[i])
	    mask |= SEARCH_UNCOUNTED;
	if (searchargs->user_flags_unset[i])
	    mask |= SEARCH_UNCOUNTED;
    }
    if (searchargs->convflags)
	mask |= SEARCH_UNCOUNTED;

    /* sequences are not counted, because the sequence might
     * run off the end of the mailbox or might include expunged
     * messages */
    if (searchargs->sequence || searchargs->uidsequence)
	mask |= SEARCH_UNCOUNTED;

    /* searches on body or headers are not counted */
    if (searchargs->from ||
        searchargs->to ||
        searchargs->cc ||
        searchargs->bcc ||
        searchargs->subject ||
        searchargs->messageid ||
        searchargs->body ||
        searchargs->text ||
        searchargs->header_name ||
        searchargs->header)
	mask |= SEARCH_UNCOUNTED;

    /* classify sub expressions too */
    for (sub = searchargs->sublist; sub; sub = sub->next) {
	mask |= search_countability(sub->sub1);
	mask |= search_countability(sub->sub2);
	if (!sub->sub2)
	    mask ^= SEARCH_NOT;
    }

    /* modseq is not counted */
    if (searchargs->modseq)
	mask |= SEARCH_UNCOUNTED;
    if (searchargs->convmodseq)
	mask |= SEARCH_UNCOUNTED;

    /* annotations are not counted */
    if (searchargs->annotations)
	mask |= SEARCH_UNCOUNTED;

    return mask;
}

#define UNPREDICTABLE	    (-1)
static int search_predict_total(struct index_state *state,
				struct conversations_state *cstate,
			        const struct searchargs *searchargs,
				int conversations,
				modseq_t *xconvmodseqp)
{
    uint32_t convexists = 0;
    uint32_t convunseen = 0;

    /* always grab xconvmodseq, so we report a growing
     * highestmodseq to all callers */
    if (conversations)
	conversation_getstatus(cstate, state->mailbox->name,
			       xconvmodseqp, &convexists, &convunseen);

    switch (search_countability(searchargs)) {
    case 0:
	return (conversations ? convexists : state->exists);
    /* we don't try to optimise searches on \Recent */
    case SEARCH_SEEN_SET:
    case SEARCH_SEEN_UNSET|SEARCH_NOT:
	assert(state->exists >= state->numunseen);
	return state->exists - state->numunseen;
    case SEARCH_SEEN_UNSET:
    case SEARCH_SEEN_SET|SEARCH_NOT:
	return state->numunseen;
    case SEARCH_CONVSEEN_SET:
    case SEARCH_CONVSEEN_UNSET|SEARCH_NOT:
	assert(convexists >= convunseen);
	return convexists - convunseen;
    case SEARCH_CONVSEEN_UNSET:
    case SEARCH_CONVSEEN_SET|SEARCH_NOT:
	return convunseen;
    default:
	return UNPREDICTABLE;
    }
}

/*
 * Performs a XCONVSORT command
 */
int index_convsort(struct index_state *state,
		   struct sortcrit *sortcrit,
		   struct searchargs *searchargs,
		   const struct windowargs *windowargs)
{
    MsgData **msgdata = NULL;
    unsigned int mi;
    modseq_t xconvmodseq = 0;
    int i;
    hashu64_table seen_cids = HASHU64_TABLE_INITIALIZER;
    uint32_t pos = 0;
    int found_anchor = 0;
    uint32_t anchor_pos = 0;
    uint32_t first_pos = 0;
    unsigned int ninwindow = 0;
    ptrarray_t results = PTRARRAY_INITIALIZER;
    int total = 0;
    int r = 0;
    struct conversations_state *cstate = NULL;

    assert(windowargs);
    assert(!windowargs->changedsince);
    assert(!windowargs->upto);

    cstate = conversations_get_mbox(state->mailbox->name);
    if (!cstate)
	return IMAP_INTERNAL;

    total = search_predict_total(state, cstate, searchargs,
				windowargs->conversations,
				&xconvmodseq);
    if (!total)
	goto out;

    construct_hashu64_table(&seen_cids, state->exists/4, 0);

    /* Create/load the msgdata array.
     * load data for ALL messages always */
    msgdata = index_msgdata_load(state, NULL, state->exists, sortcrit,
			         windowargs->anchor, &found_anchor);
    if (windowargs->anchor && !found_anchor) {
	r = IMAP_ANCHOR_NOT_FOUND;
	goto out;
    }

    /* Sort the messages based on the given criteria */
    the_sortcrit = sortcrit;
    qsort(msgdata, state->exists, sizeof(MsgData *), index_sort_compare_qsort);

    /* One pass through the message list */
    for (mi = 0 ; mi < state->exists ; mi++) {
	MsgData *msg = msgdata[mi];
	struct index_record *record = &state->map[msg->msgno-1].record;

	assert(!(record->system_flags & FLAG_EXPUNGED));

	/* run the search program against all messages */
	if (!index_search_evaluate(state, searchargs, msg->msgno, NULL))
	    continue;

	/* figure out whether this message is an exemplar */
	if (windowargs->conversations) {
	    /* in conversations mode => only the first message seen
	     * with each unique CID is an exemplar */
	    if (hashu64_lookup(record->cid, &seen_cids))
		continue;
	    hashu64_insert(record->cid, (void *)1, &seen_cids);
	}
	/* else not in conversations mode => all messages are exemplars */

	pos++;

	if (!anchor_pos &&
	    windowargs->anchor == record->uid) {
	    /* we've found the anchor's position, rejoice! */
	    anchor_pos = pos;
	}

	if (windowargs->anchor) {
	    if (!anchor_pos)
		continue;
	    if (pos < anchor_pos + windowargs->offset)
		continue;
	}
	else if (windowargs->position) {
	    if (pos < windowargs->position)
		continue;
	}
	if (windowargs->limit &&
	    ++ninwindow > windowargs->limit) {
	    if (total == UNPREDICTABLE) {
		/* the total was not predictable, so we need to keep
		 * going over the whole list to count it */
		continue;
	    }
	    break;
	}

	if (!first_pos)
	    first_pos = pos;
	ptrarray_push(&results, record);
    }

    if (total == UNPREDICTABLE) {
	/* the total was not predictable prima facie */
	total = pos;
    }

    if (windowargs->anchor && !anchor_pos) {
	/* the anchor was present but not an exemplar */
	assert(results.count == 0);
	r = IMAP_ANCHOR_NOT_FOUND;
	goto out;
    }

    /* Print the resulting list */

    /* Yes, we could use a seqset here, but apparently the most common
     * sort order seen in the field is reverse date, which is basically
     * the worst case for seqset.  So we don't bother */
    if (results.count) {
	prot_printf(state->out, "* SORT");  /* uids */
	for (i = 0 ; i < results.count ; i++) {
	    struct index_record *record = results.data[i];
	    prot_printf(state->out, " %u", record->uid);
	}
	prot_printf(state->out, "\r\n");
    }

out:
    if (!r) {
	if (first_pos)
	    prot_printf(state->out, "* OK [POSITION %u]\r\n", first_pos);

	prot_printf(state->out, "* OK [HIGHESTMODSEQ " MODSEQ_FMT "]\r\n",
		    MAX(xconvmodseq, state->mailbox->i.highestmodseq));
	prot_printf(state->out, "* OK [UIDVALIDITY %u]\r\n",
		    state->mailbox->i.uidvalidity);
	prot_printf(state->out, "* OK [UIDNEXT %u]\r\n",
		    state->mailbox->i.last_uid + 1);
	prot_printf(state->out, "* OK [TOTAL %u]\r\n",
		    total);
    }

    /* free all our temporary data */
    index_msgdata_free(msgdata, state->exists);
    ptrarray_fini(&results);
    free_hashu64_table(&seen_cids, NULL);

    return r;
}

static modseq_t get_modseq_of(struct index_record *record,
			      struct conversations_state *cstate)
{
    modseq_t modseq = 0;

    if (cstate) {
	conversation_get_modseq(cstate, record->cid, &modseq);
	/* TODO: error handling dammit */
    } else {
	modseq = record->modseq;
    }
    return modseq;
}

/*
 * Performs a XCONVUPDATES command
 */
int index_convupdates(struct index_state *state,
		      struct sortcrit *sortcrit,
		      struct searchargs *searchargs,
		      const struct windowargs *windowargs)
{
    MsgData **msgdata = NULL;
    modseq_t xconvmodseq = 0;
    unsigned int mi;
    int i;
    hashu64_table seen_cids = HASHU64_TABLE_INITIALIZER;
    hashu64_table old_seen_cids = HASHU64_TABLE_INITIALIZER;
    int32_t pos = 0;
    uint32_t upto_pos = 0;
    ptrarray_t added = PTRARRAY_INITIALIZER;
    ptrarray_t removed = PTRARRAY_INITIALIZER;
    ptrarray_t changed = PTRARRAY_INITIALIZER;
    int total = 0;
    struct conversations_state *cstate = NULL;
    int search_is_mutable = is_mutable_ordering(sortcrit, searchargs);
    int r = 0;

    assert(windowargs);
    assert(windowargs->changedsince);
    assert(windowargs->offset == 0);
    assert(!windowargs->position);

    cstate = conversations_get_mbox(state->mailbox->name);
    if (!cstate)
	return IMAP_INTERNAL;

    total = search_predict_total(state, cstate, searchargs,
				windowargs->conversations,
				&xconvmodseq);
    if (!total)
	goto out;

    construct_hashu64_table(&seen_cids, state->exists/4, 0);
    construct_hashu64_table(&old_seen_cids, state->exists/4, 0);

    /* Create/load the msgdata array
     * initial list - load data for ALL messages always */
    msgdata = index_msgdata_load(state, NULL, state->exists, sortcrit, 0, NULL);

    /* Sort the messages based on the given criteria */
    the_sortcrit = sortcrit;
    qsort(msgdata, state->exists, sizeof(MsgData *), index_sort_compare_qsort);

    /* Discover exemplars */
    for (mi = 0 ; mi < state->exists ; mi++) {
	MsgData *msg = msgdata[mi];
	struct index_record *record = &state->map[msg->msgno-1].record;
	int was_old_exemplar = 0;
	int is_new_exemplar = 0;
	int is_deleted = 0;
	int is_new = 0;
	int was_deleted = 0;
	int is_changed = 0;
	int in_search = 0;

	in_search = index_search_evaluate(state, searchargs, msg->msgno, NULL);
	is_deleted = !!(record->system_flags & FLAG_EXPUNGED);
	is_new = (record->uid >= windowargs->uidnext);
	is_changed = (record->modseq > windowargs->modseq);
	was_deleted = is_deleted && !is_changed;

	/* is this message a current exemplar? */
	if (!is_deleted &&
	    in_search &&
	    (!windowargs->conversations || !hashu64_lookup(record->cid, &seen_cids))) {
	    is_new_exemplar = 1;
	    pos++;
	    if (windowargs->conversations)
		hashu64_insert(record->cid, (void *)1, &seen_cids);
	}

	/* optimisation for when the total is
	 * not known but we've hit 'upto' */
	if (upto_pos)
	    continue;

	/* was this message an old exemplar, or in the case of mutable
	 * searches, possible an old exemplar? */
	if (!is_new &&
	    !was_deleted &&
	    (in_search || search_is_mutable) &&
	    (!windowargs->conversations || !hashu64_lookup(record->cid, &old_seen_cids))) {
	    was_old_exemplar = 1;
	    if (windowargs->conversations)
		hashu64_insert(record->cid, (void *)1, &old_seen_cids);
	}

	if (was_old_exemplar && !is_new_exemplar) {
	    ptrarray_push(&removed, record);
	} else if (!was_old_exemplar && is_new_exemplar) {
	    msg->msgno = pos;   /* hacky: reuse ->msgno for pos */
	    ptrarray_push(&added, msg);
	} else if (was_old_exemplar && is_new_exemplar) {
	    modseq_t modseq = get_modseq_of(record,
				windowargs->conversations ? cstate : NULL);
	    if (modseq > windowargs->modseq) {
		ptrarray_push(&changed, record);
		if (search_is_mutable) {
		    /* is the search is mutable, we're in a whole world of
		     * uncertainty about the client's state, so we just
		     * report the exemplar in all three lists and let the
		     * client sort it out. */
		    ptrarray_push(&removed, record);
		    msg->msgno = pos;   /* hacky: reuse ->msgno for pos */
		    ptrarray_push(&added, msg);
		}
	    }
	}

	/* if this is the last message the client cares about ('upto')
	 * then we can break early...unless its a mutable search or
	 * we need to keep going to calculate an accurate total */
	if (!search_is_mutable &&
	    !upto_pos &&
	    msg->uid == windowargs->anchor) {
	    if (total != UNPREDICTABLE)
		break;
	    upto_pos = pos;
	}
    }

    /* unlike 'anchor', the case of not finding 'upto' is not an error */

    if (total == UNPREDICTABLE) {
	/* the total was not predictable prima facie */
	total = pos;
    }

    /* Print the resulting lists */

    if (added.count) {
	prot_printf(state->out, "* ADDED"); /* (uid pos) tuples */
	for (i = 0 ; i < added.count ; i++) {
	    MsgData *msg = added.data[i];
	    prot_printf(state->out, " (%u %u)",
			msg->uid, msg->msgno);
	}
	prot_printf(state->out, "\r\n");
    }

    if (removed.count) {
	prot_printf(state->out, "* REMOVED");	/* uids */
	for (i = 0 ; i < removed.count ; i++) {
	    struct index_record *record = removed.data[i];
	    prot_printf(state->out, " %u", record->uid);
	}
	prot_printf(state->out, "\r\n");
    }

    if (changed.count) {
	prot_printf(state->out, "* CHANGED");	/* cids or uids */
	for (i = 0 ; i < changed.count ; i++) {
	    struct index_record *record = changed.data[i];
	    if (windowargs->conversations)
		prot_printf(state->out, " %s",
			conversation_id_encode(record->cid));
	    else
		prot_printf(state->out, " %u", record->uid);
	}
	prot_printf(state->out, "\r\n");
    }

out:
    if (!r) {
	prot_printf(state->out, "* OK [HIGHESTMODSEQ " MODSEQ_FMT "]\r\n",
		    MAX(xconvmodseq, state->mailbox->i.highestmodseq));
	prot_printf(state->out, "* OK [UIDVALIDITY %u]\r\n",
		    state->mailbox->i.uidvalidity);
	prot_printf(state->out, "* OK [UIDNEXT %u]\r\n",
		    state->mailbox->i.last_uid + 1);
	prot_printf(state->out, "* OK [TOTAL %u]\r\n",
		    total);
    }

    /* free all our temporary data */
    index_msgdata_free(msgdata, state->exists);
    ptrarray_fini(&added);
    ptrarray_fini(&removed);
    ptrarray_fini(&changed);
    free_hashu64_table(&seen_cids, NULL);
    free_hashu64_table(&old_seen_cids, NULL);

    return r;
}

/*
 * Performs a THREAD command
 */
int index_thread(struct index_state *state, int algorithm,
		 struct searchargs *searchargs, int usinguid)
{
    unsigned *msgno_list;
    int nmsg;
    clock_t start;
    modseq_t highestmodseq = 0;

    /* update the index */
    if (index_check(state, 0, 0))
	return 0;
    
    if(CONFIG_TIMING_VERBOSE)
	start = clock();

    /* Search for messages based on the given criteria */
    nmsg = _index_search(&msgno_list, state, searchargs,
			 searchargs->modseq ? &highestmodseq : NULL);

    if (nmsg) {
	/* Thread messages using given algorithm */
	(*thread_algs[algorithm].threader)(state, msgno_list, nmsg, usinguid);

	free(msgno_list);

	if (highestmodseq)
	    prot_printf(state->out, " (MODSEQ " MODSEQ_FMT ")", highestmodseq);
    }

    /* print an empty untagged response */
    else
	index_thread_print(state, NULL, usinguid);

    prot_printf(state->out, "\r\n");

    if (CONFIG_TIMING_VERBOSE) {
	/* debug */
	syslog(LOG_DEBUG, "THREAD %s processing time: %d msg in %f sec",
	       thread_algs[algorithm].alg_name, nmsg,
	       (clock() - start) / (double) CLOCKS_PER_SEC);
    }

    return nmsg;
}

/*
 * Performs a COPY command
 */
int
index_copy(struct index_state *state,
	   char *sequence, 
	   int usinguid,
	   char *name, 
	   char **copyuidp,
	   int nolink,
	   struct namespace *namespace,
	   int isadmin,
	   int ismove)
{
    static struct copyargs copyargs;
    int i;
    quota_t qdiffs[QUOTA_NUMRESOURCES] = QUOTA_DIFFS_INITIALIZER;
    quota_t *qptr = NULL;
    int r;
    struct appendstate appendstate;
    uint32_t msgno, checkval;
    long docopyuid;
    struct seqset *seq;
    struct mailbox *mailbox = state->mailbox;
    struct mailbox *destmailbox = NULL;
    struct index_map *im;
    int is_same_user;

    *copyuidp = NULL;

    copyargs.nummsg = 0;

    is_same_user = mboxname_same_userid(mailbox->name, name);
    if (is_same_user < 0)
	return is_same_user;

    r = index_check(state, usinguid, usinguid);
    if (r) return r;

    seq = _parse_sequence(state, sequence, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->record.uid : msgno;
	if (!seqset_ismember(seq, checkval))
	    continue;
	index_copysetup(state, msgno, &copyargs, is_same_user);
    }

    seqset_free(seq);

    if (copyargs.nummsg == 0) return IMAP_NO_NOSUCHMSG;

    r = mailbox_open_iwl(name, &destmailbox);
    if (r) return r;

    /* not moving or different quota root - need to check quota */
    if (!ismove || strcmpsafe(mailbox->quotaroot, destmailbox->quotaroot)) {
	for (i = 0; i < copyargs.nummsg; i++)
	    qdiffs[QUOTA_STORAGE] += copyargs.copymsg[i].size;
	qdiffs[QUOTA_MESSAGE] = copyargs.nummsg;
	qptr = qdiffs;
    }

    r = append_setup_mbox(&appendstate, destmailbox, state->userid,
			  state->authstate, ACL_INSERT,
			  qptr, namespace, isadmin);
    if (r) return r;

    docopyuid = (appendstate.myrights & ACL_READ);

    r = append_copy(mailbox, &appendstate, copyargs.nummsg,
		    copyargs.copymsg, nolink);
    if (!r) {
	r = append_commit(&appendstate, &destmailbox);
    }

    if (!r && (docopyuid || ismove)) {
	char *source;
	struct seqset *seq;
	unsigned uidvalidity = destmailbox->i.uidvalidity;

	seq = seqset_init(0, SEQ_SPARSE);

	for (i = 0; i < copyargs.nummsg; i++)
	    seqset_add(seq, copyargs.copymsg[i].uid, 1);

	source = seqset_cstring(seq);

	/* remove the source messages */
	if (ismove)
	    r = index_expunge(state, source, 0);

	if (docopyuid) {
	    *copyuidp = xmalloc(strlen(source) + 50);

	    if (appendstate.nummsg == 1)
		sprintf(*copyuidp, "%u %s %u", uidvalidity, source,
			appendstate.baseuid);
	    else
		sprintf(*copyuidp, "%u %s %u:%u", uidvalidity, source,
			appendstate.baseuid,
			appendstate.baseuid + appendstate.nummsg - 1);
	}

	free(source);
	seqset_free(seq);
    }

    /* we log the first name to get GUID-copy magic */
    if (!r)
	sync_log_mailbox_double(mailbox->name, name);

    mailbox_close(&destmailbox);

    return r;
}

/*
 * Helper function to multiappend a message to remote mailbox
 */
static int index_appendremote(struct index_state *state, uint32_t msgno, 
			      struct protstream *pout)
{
    struct mailbox *mailbox = state->mailbox;
    const char *msg_base = 0;
    size_t msg_size = 0;
    unsigned flag, flagmask;
    char datebuf[RFC3501_DATETIME_MAX+1];
    char sepchar = '(';
    struct index_map *im = &state->map[msgno-1];

    /* Open the message file */
    if (mailbox_map_message(mailbox, im->record.uid, &msg_base, &msg_size)) 
	return IMAP_NO_MSGGONE;

    /* start the individual append */
    prot_printf(pout, " ");

    /* add system flags */
    if (im->record.system_flags & FLAG_ANSWERED) {
	prot_printf(pout, "%c\\Answered", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_FLAGGED) {
	prot_printf(pout, "%c\\Flagged", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_DRAFT) {
	prot_printf(pout, "%c\\Draft", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_DELETED) {
	prot_printf(pout, "%c\\Deleted", sepchar);
	sepchar = ' ';
    }
    if (im->isseen) {
	prot_printf(pout, "%c\\Seen", sepchar);
	sepchar = ' ';
    }

    /* add user flags */
    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	if ((flag & 31) == 0) {
	    flagmask = im->record.user_flags[flag/32];
	}
	if (state->flagname[flag] && (flagmask & (1<<(flag & 31)))) {
	    prot_printf(pout, "%c%s", sepchar, state->flagname[flag]);
	    sepchar = ' ';
	}
    }

    /* add internal date */
    time_to_rfc3501(im->record.internaldate, datebuf, sizeof(datebuf));
    prot_printf(pout, ") \"%s\" ", datebuf);

    /* message literal */
    index_fetchmsg(state, msg_base, msg_size, 0, im->record.size, 0, 0);

    /* close the message file */
    if (msg_base) 
	mailbox_unmap_message(mailbox, im->record.uid, &msg_base, &msg_size);

    return 0;
}

/*
 * Performs a COPY command from a local mailbox to a remote mailbox
 */
int index_copy_remote(struct index_state *state, char *sequence, 
		      int usinguid, struct protstream *pout)
{
    uint32_t msgno, checkval;
    struct seqset *seq;
    struct index_map *im;
    int r;

    r = index_check(state, usinguid, usinguid);
    if (r) return r;

    seq = _parse_sequence(state, sequence, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->record.uid : msgno;
	if (!seqset_ismember(seq, checkval))
	    continue;
	index_appendremote(state, msgno, pout);
    }

    seqset_free(seq);

    return 0;
}

/*
 * Returns the msgno of the message with UID 'uid'.
 * If no message with UID 'uid', returns the message with
 * the higest UID not greater than 'uid'.
 */
unsigned index_finduid(struct index_state *state, unsigned uid)
{
    unsigned low = 1;
    unsigned high = state->exists;
    unsigned mid;
    unsigned miduid;

    while (low <= high) {
	mid = (high - low)/2 + low;
	miduid = index_getuid(state, mid);
	if (miduid == uid)
	    return mid;
	else if (miduid > uid)
	    high = mid - 1;
	else
	    low = mid + 1;
    }
    return high;
}

/* Helper function to determine domain of data */
enum {
    DOMAIN_7BIT = 0,
    DOMAIN_8BIT,
    DOMAIN_BINARY
};

static int data_domain(const char *p, size_t n)
{
    while (n--) {
	if (!*p) return DOMAIN_BINARY;
	if (*p & 0x80) return DOMAIN_8BIT;
	p++;
    }
 
    return DOMAIN_7BIT;
}

/*
 * Helper function to fetch data from a message file.  Writes a
 * quoted-string or literal containing data from 'msg_base', which is
 * of size 'msg_size', starting at 'offset' and containing 'size'
 * octets.  If 'octet_count' is nonzero, the data is
 * further constrained by 'start_octet' and 'octet_count' as per the
 * IMAP command PARTIAL.
 */
void index_fetchmsg(struct index_state *state, const char *msg_base,
		    unsigned long msg_size, unsigned offset,
		    unsigned size,     /* this is the correct size for a news message after
					  having LF translated to CRLF */
		    unsigned start_octet, unsigned octet_count)
{
    unsigned n, domain;

    /* If no data, output NIL */
    if (!msg_base) {
	prot_printf(state->out, "NIL");
	return;
    }

    /* partial fetch: adjust 'size' */
    if (octet_count) {
	if (size <= start_octet) {
	    size = 0;
	}
	else {
	    size -= start_octet;
	}
	if (size > octet_count) size = octet_count;
    }

    /* If zero-length data, output empty quoted string */
    if (size == 0) {
	prot_printf(state->out, "\"\"");
	return;
    }

    /* Seek over PARTIAL constraint */
    offset += start_octet;
    n = size;
    if (offset + size > msg_size) {
	if (msg_size > offset) {
	    n = msg_size - offset;
	}
	else {
	    prot_printf(state->out, "\"\"");
	    return;
	}
    }

    /* Get domain of the data */
    domain = data_domain(msg_base + offset, n);

    if (domain == DOMAIN_BINARY) {
	/* Write size of literal8 */
	prot_printf(state->out, "~{%u}\r\n", size);
    } else {
	/* Write size of literal */
	prot_printf(state->out, "{%u}\r\n", size);
    }

    /* Non-text literal -- tell the protstream about it */
    if (domain != DOMAIN_7BIT) prot_data_boundary(state->out);

    prot_write(state->out, msg_base + offset, n);
    while (n++ < size) {
	/* File too short, resynch client.
	 *
	 * This can only happen if the reported size of the part
	 * is incorrect and would push us past EOF.
	 */
	(void)prot_putc(' ', state->out);
    }

    /* End of non-text literal -- tell the protstream about it */
    if (domain != DOMAIN_7BIT) prot_data_boundary(state->out);
}

/*
 * Helper function to fetch a body section
 */
static int index_fetchsection(struct index_state *state, const char *resp,
			      const char *msg_base, unsigned long msg_size,
			      char *section, const char *cachestr, unsigned size,
			      unsigned start_octet, unsigned octet_count)
{
    const char *p;
    int32_t skip = 0;
    int fetchmime = 0;
    unsigned offset = 0;
    char *decbuf = NULL;

    p = section;

    /* Special-case BODY[] */
    if (*p == ']') {
	if (strstr(resp, "BINARY.SIZE")) {
	    prot_printf(state->out, "%s%u", resp, size);
	} else {
	    prot_printf(state->out, "%s", resp);
	    index_fetchmsg(state, msg_base, msg_size, 0, size,
			   start_octet, octet_count);
	}
	return 0;
    }

    while (*p != ']' && *p != 'M') {
	int num_parts = CACHE_ITEM_BIT32(cachestr);
	int r;

	/* Generate the actual part number */
	r = parseint32(p, &p, &skip);
	if (*p == '.') p++;

	/* Handle .0, .HEADER, and .TEXT */
	if (r || skip == 0) {
	    skip = 0;
	    /* We don't have any digits, so its a string */
	    switch (*p) {
	    case 'H':
		p += 6;
		fetchmime++;	/* .HEADER maps internally to .0.MIME */
		break;

	    case 'T':
		p += 4;
		break;		/* .TEXT maps internally to .0 */

	    default:
		fetchmime++;	/* .0 maps internally to .0.MIME */
		break;
	    }
	} 

	/* section number too large */
	if (skip >= num_parts) goto badpart;

	if (*p != ']' && *p != 'M') {
	    /* We are NOT at the end of a part specification, so there's
	     * a subpart being requested.  Find the subpart in the tree. */

	    /* Skip the headers for this part, along with the number of
	     * sub parts */
	    cachestr += num_parts * 5 * 4 + CACHE_ITEM_SIZE_SKIP;

	    /* Skip to the correct part */
	    while (--skip) {
		if (CACHE_ITEM_BIT32(cachestr) > 0) {
		    /* Skip each part at this level */
		    skip += CACHE_ITEM_BIT32(cachestr)-1;
		    cachestr += CACHE_ITEM_BIT32(cachestr) * 5 * 4;
		}
		cachestr += CACHE_ITEM_SIZE_SKIP;
	    }
	}
    }

    if (*p == 'M') fetchmime++;

    cachestr += skip * 5 * 4 + CACHE_ITEM_SIZE_SKIP + (fetchmime ? 0 : 2 * 4);
    
    if (CACHE_ITEM_BIT32(cachestr + CACHE_ITEM_SIZE_SKIP) == (bit32) -1)
	goto badpart;

    offset = CACHE_ITEM_BIT32(cachestr);
    size = CACHE_ITEM_BIT32(cachestr + CACHE_ITEM_SIZE_SKIP);

    if (msg_base && (p = strstr(resp, "BINARY"))) {
	/* BINARY or BINARY.SIZE */
	int encoding = CACHE_ITEM_BIT32(cachestr + 2 * 4) & 0xff;
	size_t newsize;

	/* check that the offset isn't corrupt */
	if (offset + size > msg_size) {
	    syslog(LOG_ERR, "invalid part offset in %s", state->mailbox->name);
	    return IMAP_IOERROR;
	}

	msg_base = charset_decode_mimebody(msg_base + offset, size, encoding,
					   &decbuf, &newsize);

	if (!msg_base) {
	    /* failed to decode */
	    if (decbuf) free(decbuf);
	    return IMAP_NO_UNKNOWN_CTE;
	}
	else if (p[6] == '.') {
	    /* BINARY.SIZE */
	    prot_printf(state->out, "%s%zd", resp, newsize);
	    if (decbuf) free(decbuf);
	    return 0;
	}
	else {
	    /* BINARY */
	    offset = 0;
	    size = newsize;
	    msg_size = newsize;
	}
    }

    /* Output body part */
    prot_printf(state->out, "%s", resp);
    index_fetchmsg(state, msg_base, msg_size, offset, size,
		   start_octet, octet_count);

    if (decbuf) free(decbuf);
    return 0;

 badpart:
    if (strstr(resp, "BINARY.SIZE"))
	prot_printf(state->out, "%s0", resp);
    else
	prot_printf(state->out, "%sNIL", resp);
    return 0;
}

/*
 * Helper function to fetch a HEADER.FIELDS[.NOT] body section
 */
static void index_fetchfsection(struct index_state *state,
				const char *msg_base,
				unsigned long msg_size,
				struct fieldlist *fsection,
				const char *cachestr,
				unsigned start_octet, unsigned octet_count)
{
    const char *p;
    int32_t skip = 0;
    int fields_not = 0;
    unsigned crlf_start = 0;
    unsigned crlf_size = 2;
    char *buf;
    unsigned size;
    int r;

    /* If no data, output null quoted string */
    if (!msg_base) {
	prot_printf(state->out, "\"\"");
	return;
    }

    p = fsection->section;

    while (*p != 'H') {
	int num_parts = CACHE_ITEM_BIT32(cachestr);

	r = parseint32(p, &p, &skip);
	if (*p == '.') p++;

	/* section number too large */
	if (r || skip == 0 || skip >= num_parts) goto badpart;

	cachestr += num_parts * 5 * 4 + CACHE_ITEM_SIZE_SKIP;
	while (--skip) {
	    if (CACHE_ITEM_BIT32(cachestr) > 0) {
		skip += CACHE_ITEM_BIT32(cachestr)-1;
		cachestr += CACHE_ITEM_BIT32(cachestr) * 5 * 4;
	    }
	    cachestr += CACHE_ITEM_SIZE_SKIP;
	}
    }

    /* leaf object */
    if (0 == CACHE_ITEM_BIT32(cachestr)) goto badpart;

    cachestr += 4;

    if (CACHE_ITEM_BIT32(cachestr+CACHE_ITEM_SIZE_SKIP) == (bit32) -1)
	goto badpart;
	
    if (p[13]) fields_not++;	/* Check for "." after "HEADER.FIELDS" */

    buf = index_readheader(msg_base, msg_size, 
			   CACHE_ITEM_BIT32(cachestr),
			   CACHE_ITEM_BIT32(cachestr+CACHE_ITEM_SIZE_SKIP));

    if (fields_not) {
	message_pruneheader(buf, 0, fsection->fields);
    }
    else {
	message_pruneheader(buf, fsection->fields, 0);
    }
    size = strlen(buf);

    /* partial fetch: adjust 'size' */
    if (octet_count) {
	if (size <= start_octet) {
	    crlf_start = start_octet - size;
	    size = 0;
	    start_octet = 0;
	    if (crlf_size <= crlf_start) {
		crlf_size = 0;
	    }
	    else {
		crlf_size -= crlf_start;
	    }
	}
	else {
	    size -= start_octet;
	}
	if (size > octet_count) {
	    size = octet_count;
	    crlf_size = 0;
	}
	else if (size + crlf_size > octet_count) {
	    crlf_size = octet_count - size;
	}
    }

    /* If no data, output null quoted string */
    if (size + crlf_size == 0) {
	prot_printf(state->out, "\"\"");
	return;
    }

    /* Write literal */
    prot_printf(state->out, "{%u}\r\n", size + crlf_size);
    prot_write(state->out, buf + start_octet, size);
    prot_write(state->out, "\r\n" + crlf_start, crlf_size);

    return;

 badpart:
    prot_printf(state->out, "NIL");
}

/*
 * Helper function to read a header section into a static buffer
 */
static char *index_readheader(const char *msg_base, unsigned long msg_size,
			      unsigned offset, unsigned size)
{
    static char *buf;
    static unsigned bufsize;

    if (offset + size > msg_size) {
	/* Message file is too short, truncate request */
	if (offset < msg_size) {
	    size = msg_size - offset;
	}
	else {
	    size = 0;
	}
    }

    if (bufsize < size+2) {
	bufsize = size+100;
	buf = xrealloc(buf, bufsize);
    }

    msg_base += offset;

    memcpy(buf, msg_base, size);
    buf[size] = '\0';

    return buf;
}

/*
 * Handle a FETCH RFC822.HEADER.LINES or RFC822.HEADER.LINES.NOT
 * that can't use the cacheheaders in cyrus.cache
 */
static void index_fetchheader(struct index_state *state,
			      const char *msg_base,
			      unsigned long msg_size,
			      unsigned size,
			      const strarray_t *headers,
			      const strarray_t *headers_not)
{
    char *buf;

    /* If no data, output null quoted string */
    if (!msg_base) {
	prot_printf(state->out, "\"\"");
	return;
    }

    buf = index_readheader(msg_base, msg_size, 0, size);

    message_pruneheader(buf, headers, headers_not);

    size = strlen(buf);
    prot_printf(state->out, "{%u}\r\n%s\r\n", size+2, buf);
}

/*
 * Handle a FETCH RFC822.HEADER.LINES that can use the
 * cacheheaders in cyrus.cache
 */
static void
index_fetchcacheheader(struct index_state *state, struct index_record *record,
		       const strarray_t *headers, unsigned start_octet,
		       unsigned octet_count)
{
    static char *buf;
    static unsigned bufsize;
    unsigned size;
    unsigned crlf_start = 0;
    unsigned crlf_size = 2;
    struct mailbox *mailbox = state->mailbox;

    if (mailbox_cacherecord(mailbox, record)) {
	/* bogus cache record */
	prot_printf(state->out, "\"\"");
	return;
    }

    size = cacheitem_size(record, CACHE_HEADERS);
    if (bufsize < size+2) {
	bufsize = size+100;
	buf = xrealloc(buf, bufsize);
    }

    memcpy(buf, cacheitem_base(record, CACHE_HEADERS), size);
    buf[size] = '\0';

    message_pruneheader(buf, headers, 0);
    size = strlen(buf);

    /* partial fetch: adjust 'size' */
    if (octet_count) {
	if (size <= start_octet) {
	    crlf_start = start_octet - size;
	    size = 0;
	    start_octet = 0;
	    if (crlf_size <= crlf_start) {
		crlf_size = 0;
	    }
	    else {
		crlf_size -= crlf_start;
	    }
	}
	else {
	    size -= start_octet;
	}
	if (size > octet_count) {
	    size = octet_count;
	    crlf_size = 0;
	}
	else if (size + crlf_size > octet_count) {
	    crlf_size = octet_count - size;
	}
    }
	
    if (size + crlf_size == 0) {
	prot_printf(state->out, "\"\"");
    }
    else {
	prot_printf(state->out, "{%u}\r\n", size + crlf_size);
	prot_write(state->out, buf + start_octet, size);
	prot_write(state->out, "\r\n" + crlf_start, crlf_size);
    }
}

/*
 * Send a * FLAGS response.
 */
static void index_listflags(struct index_state *state)
{
    unsigned i;
    int cancreate = 0;
    char sepchar = '(';

    prot_printf(state->out, "* FLAGS (\\Answered \\Flagged \\Draft \\Deleted \\Seen");
    for (i = 0; i < MAX_USER_FLAGS; i++) {
	if (state->flagname[i]) {
	    prot_printf(state->out, " %s", state->flagname[i]);
	}
	else cancreate++;
    }
    prot_printf(state->out, ")\r\n* OK [PERMANENTFLAGS ");
    if (!state->examining) {
	if (state->myrights & ACL_WRITE) {
	    prot_printf(state->out, "%c\\Answered \\Flagged \\Draft", sepchar);
	    sepchar = ' ';
	}
	if (state->myrights & ACL_DELETEMSG) {
	    prot_printf(state->out, "%c\\Deleted", sepchar);
	    sepchar = ' ';
	}
	if (state->myrights & ACL_SETSEEN) {
	    prot_printf(state->out, "%c\\Seen", sepchar);
	    sepchar = ' ';
	}
	if (state->myrights & ACL_WRITE) {
	    for (i = 0; i < MAX_USER_FLAGS; i++) {
		if (state->flagname[i]) {
		    prot_printf(state->out, " %s", state->flagname[i]);
		}
	    }
	    if (cancreate) {
		prot_printf(state->out, " \\*");
	    }
	}
    }
    if (sepchar == '(') prot_printf(state->out, "(");
    prot_printf(state->out, ")] Ok\r\n");
}

void index_checkflags(struct index_state *state, int print, int dirty)
{
    struct mailbox *mailbox = state->mailbox;
    unsigned i;

    for (i = 0; i < MAX_USER_FLAGS; i++) {
	/* both empty */
	if (!mailbox->flagname[i] && !state->flagname[i])
	    continue;

	/* both same */
	if (mailbox->flagname[i] && state->flagname[i] &&
	    !strcmp(mailbox->flagname[i], state->flagname[i]))
	    continue;

	/* ok, got something to change! */
	if (state->flagname[i])
	    free(state->flagname[i]);
	if (mailbox->flagname[i])
	    state->flagname[i] = xstrdup(mailbox->flagname[i]);
	else
	    state->flagname[i] = NULL;

	dirty = 1;
    }

    if (dirty && print)
	index_listflags(state);
}

static void index_tellexpunge(struct index_state *state)
{
    unsigned oldmsgno;
    uint32_t msgno = 1;
    struct seqset *vanishedlist;
    struct index_map *im;
    unsigned exists = state->exists;

    vanishedlist = seqset_init(0, SEQ_SPARSE);

    for (oldmsgno = 1; oldmsgno <= exists; oldmsgno++) {
	im = &state->map[oldmsgno-1];

	/* inform about expunges */
	if (im->record.system_flags & FLAG_EXPUNGED) {
	    state->exists--;
	    /* they never knew about this one, skip */
	    if (msgno > state->oldexists)
		continue;
	    state->oldexists--;
	    if (state->qresync)
		seqset_add(vanishedlist, im->record.uid, 1);
	    else
		prot_printf(state->out, "* %u EXPUNGE\r\n", msgno);
	    continue;
	}

	/* copy back if necessary (after first expunge) */
	if (msgno < oldmsgno)
	    state->map[msgno-1] = *im;

	msgno++;
    }

    /* report all vanished if we're doing it this way */
    if (vanishedlist->len) {
	char *vanished = seqset_cstring(vanishedlist);
	prot_printf(state->out, "* VANISHED %s\r\n", vanished);
	free(vanished);
    }
    seqset_free(vanishedlist);

    /* highestmodseq can now come forward to real-time */
    state->highestmodseq = state->mailbox->i.highestmodseq;
}

static void index_tellexists(struct index_state *state)
{
    prot_printf(state->out, "* %u EXISTS\r\n", state->exists);
    prot_printf(state->out, "* %u RECENT\r\n", state->numrecent);
    state->oldexists = state->exists;
}

void index_tellchanges(struct index_state *state, int canexpunge,
		       int printuid, int printmodseq)
{
    uint32_t msgno;
    struct index_map *im;

    if (canexpunge) index_tellexpunge(state);

    if (state->oldexists != state->exists) index_tellexists(state);

    index_checkflags(state, 1, 0);

    /* print any changed message flags */
    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];

	/* we don't report flag updates if it's been expunged */
	if (im->record.system_flags & FLAG_EXPUNGED)
	    continue;

	/* report if it's changed since last told */
	if (im->record.modseq > im->told_modseq)
	    index_printflags(state, msgno, printuid, printmodseq);
    }
}

struct fetch_annotation_rock {
    struct protstream *pout;
    const char *sep;
};

static void fetch_annotation_response(const char *mboxname
					__attribute__((unused)),
				      uint32_t uid
					__attribute__((unused)),
				      const char *entry,
				      struct attvaluelist *attvalues,
				      void *rock)
{
    char sep2 = '(';
    struct attvaluelist *l;
    struct fetch_annotation_rock *frock = rock;

    prot_printf(frock->pout, "%s", frock->sep);
    prot_printastring(frock->pout, entry);
    prot_putc(' ', frock->pout);

    for (l = attvalues ; l ; l = l->next) {
	prot_putc(sep2, frock->pout);
	sep2 = ' ';
	prot_printastring(frock->pout, l->attrib);
	prot_putc(' ', frock->pout);
	prot_printmap(frock->pout, l->value.s, l->value.len);
    }
    prot_putc(')', frock->pout);

    frock->sep = " ";
}

/*
 * Helper function to send FETCH data for the ANNOTATION
 * fetch item.
 */
static int index_fetchannotations(struct index_state *state,
				  uint32_t msgno,
				  const struct fetchargs *fetchargs)
{
    annotate_state_t *astate = NULL;
    struct fetch_annotation_rock rock;
    int r = 0;

    r = mailbox_get_annotate_state(state->mailbox,
			           state->map[msgno-1].record.uid,
				   &astate);
    if (r) return r;
    annotate_state_set_auth(astate, fetchargs->isadmin,
			    fetchargs->userid, fetchargs->authstate);

    memset(&rock, 0, sizeof(rock));
    rock.pout = state->out;
    rock.sep = "";

    r = annotate_state_fetch(astate,
			     &fetchargs->entries, &fetchargs->attribs,
			     fetch_annotation_response, &rock,
			     0);

    return r;
}

/*
 * Helper function to send * FETCH (FLAGS data.
 * Does not send the terminating close paren or CRLF.
 * Also sends preceeding * FLAGS if necessary.
 */
static void index_fetchflags(struct index_state *state,
			     uint32_t msgno)
{
    int sepchar = '(';
    unsigned flag;
    bit32 flagmask = 0;
    struct index_map *im = &state->map[msgno-1];

    prot_printf(state->out, "* %u FETCH (FLAGS ", msgno);

    if (im->isrecent) {
	prot_printf(state->out, "%c\\Recent", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_ANSWERED) {
	prot_printf(state->out, "%c\\Answered", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_FLAGGED) {
	prot_printf(state->out, "%c\\Flagged", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_DRAFT) {
	prot_printf(state->out, "%c\\Draft", sepchar);
	sepchar = ' ';
    }
    if (im->record.system_flags & FLAG_DELETED) {
	prot_printf(state->out, "%c\\Deleted", sepchar);
	sepchar = ' ';
    }
    if (im->isseen) {
	prot_printf(state->out, "%c\\Seen", sepchar);
	sepchar = ' ';
    }
    for (flag = 0; flag < VECTOR_SIZE(state->flagname); flag++) {
	if ((flag & 31) == 0) {
	    flagmask = im->record.user_flags[flag/32];
	}
	if (state->flagname[flag] && (flagmask & (1<<(flag & 31)))) {
	    prot_printf(state->out, "%c%s", sepchar, state->flagname[flag]);
	    sepchar = ' ';
	}
    }
    if (sepchar == '(') (void)prot_putc('(', state->out);
    (void)prot_putc(')', state->out);
    im->told_modseq = im->record.modseq;
}

static void index_printflags(struct index_state *state,
			     uint32_t msgno, int usinguid,
			     int printmodseq)
{
    struct index_map *im = &state->map[msgno-1];

    index_fetchflags(state, msgno);
    /* http://www.rfc-editor.org/errata_search.php?rfc=5162
     * Errata ID: 1807 - MUST send UID and MODSEQ to all
     * untagged FETCH unsolicited responses */
    if (usinguid || state->qresync)
	prot_printf(state->out, " UID %u", im->record.uid);
    if (printmodseq || state->qresync)
	prot_printf(state->out, " MODSEQ (" MODSEQ_FMT ")", im->record.modseq);
    prot_printf(state->out, ")\r\n");
}

/*
 * Helper function to send requested * FETCH data for a message
 */
static int index_fetchreply(struct index_state *state, uint32_t msgno,
			    const struct fetchargs *fetchargs)
{
    struct mailbox *mailbox = state->mailbox;
    int fetchitems = fetchargs->fetchitems;
    const char *msg_base = NULL;
    size_t msg_size = 0;
    struct octetinfo *oi = NULL;
    int sepchar = '(';
    int started = 0;
    struct section *section;
    struct fieldlist *fsection;
    char respbuf[100];
    int r = 0;
    struct index_map *im = &state->map[msgno-1];

    /* Check against the CID list filter */
    if (fetchargs->cidhash) {
	const char *key = conversation_id_encode(im->record.cid);
	if (!hash_lookup(key, fetchargs->cidhash))
	    return 0;
    }

    /* Check the modseq against changedsince */
    if (fetchargs->changedsince &&
	im->record.modseq <= fetchargs->changedsince) {
	return 0;
    }

    /* Open the message file if we're going to need it */
    if ((fetchitems & (FETCH_HEADER|FETCH_TEXT|FETCH_SHA1|FETCH_RFC822)) ||
	fetchargs->cache_atleast > im->record.cache_version || 
	fetchargs->binsections || fetchargs->sizesections ||
	fetchargs->bodysections) {
	if (mailbox_map_message(mailbox, im->record.uid, &msg_base, &msg_size)) {
	    prot_printf(state->out, "* OK ");
	    prot_printf(state->out, error_message(IMAP_NO_MSGGONE), msgno);
	    prot_printf(state->out, "\r\n");
	    return 0;
	}
    }

    /* display flags if asked _OR_ if they've changed */
    if (fetchitems & FETCH_FLAGS || im->told_modseq < im->record.modseq) {
	index_fetchflags(state, msgno);
	sepchar = ' ';
    }
    else if ((fetchitems & ~FETCH_SETSEEN) ||  fetchargs->fsections ||
	     fetchargs->headers.count || fetchargs->headers_not.count) {
	/* these fetch items will always succeed, so start the response */
	prot_printf(state->out, "* %u FETCH ", msgno);
	started = 1;
    }
    if (fetchitems & FETCH_UID) {
	prot_printf(state->out, "%cUID %u", sepchar, im->record.uid);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_GUID) {
	prot_printf(state->out, "%cDIGEST.SHA1 %s", sepchar,
		    message_guid_encode(&im->record.guid));
	sepchar = ' ';
    }

    if (fetchitems & FETCH_INTERNALDATE) {
	time_t msgdate = im->record.internaldate;
	char datebuf[RFC3501_DATETIME_MAX+1];

	time_to_rfc3501(msgdate, datebuf, sizeof(datebuf));

	prot_printf(state->out, "%cINTERNALDATE \"%s\"",
		    sepchar, datebuf);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_MODSEQ) {
	prot_printf(state->out, "%cMODSEQ (" MODSEQ_FMT ")",
		    sepchar, im->record.modseq);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_SIZE) {
	prot_printf(state->out, "%cRFC822.SIZE %u", 
		    sepchar, im->record.size);
	sepchar = ' ';
    }
    if ((fetchitems & FETCH_ANNOTATION)) {
	prot_printf(state->out, "%cANNOTATION (", sepchar);
	r = index_fetchannotations(state, msgno, fetchargs);
	r = 0;
	prot_printf(state->out, ")");
	sepchar = ' ';
    }
    if (fetchitems & FETCH_FILESIZE) {
	if (!msg_base) {
	    char *fname = mailbox_message_fname(mailbox, im->record.uid);
	    struct stat sbuf;
	    /* Find the size of the message file */
	    if (stat(fname, &sbuf) == -1)
		syslog(LOG_ERR, "IOERROR: stat on %s: %m", fname);
	    else
		msg_size = sbuf.st_size;
	}
	prot_printf(state->out, "%cRFC822.FILESIZE %lu", sepchar,
		    (long unsigned)msg_size);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_SHA1) {
	struct message_guid tmpguid;
	message_guid_generate(&tmpguid, msg_base, msg_size);
	prot_printf(state->out, "%cRFC822.SHA1 %s", sepchar, message_guid_encode(&tmpguid));
	sepchar = ' ';
    }
    if ((fetchitems & FETCH_CID) &&
	config_getswitch(IMAPOPT_CONVERSATIONS)) {
	struct buf buf = BUF_INITIALIZER;
	if (!im->record.cid)
	    buf_appendcstr(&buf, "NIL");
	else
	    buf_printf(&buf, CONV_FMT, im->record.cid);
	prot_printf(state->out, "%cCID %s", sepchar, buf_cstring(&buf));
	buf_free(&buf);
	sepchar = ' ';
    }
    if ((fetchitems & FETCH_FOLDER)) {
	struct namespace *ns = fetchargs->namespace;
	char mboxname[MAX_MAILBOX_PATH+1];
	r = ns->mboxname_toexternal(ns, state->mailbox->name,
				    fetchargs->userid, mboxname);
	if (!r) {
	    prot_printf(state->out, "%cFOLDER ", sepchar);
	    prot_printastring(state->out, mboxname);
	    sepchar = ' ';
	}
	r = 0;
    }
    if ((fetchitems & FETCH_UIDVALIDITY)) {
	prot_printf(state->out, "%cUIDVALIDITY %u", sepchar,
		    state->mailbox->i.uidvalidity);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_ENVELOPE) {
        if (!mailbox_cacherecord(mailbox, &im->record)) {
	    prot_printf(state->out, "%cENVELOPE ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&im->record, CACHE_ENVELOPE));
	}
    }
    if (fetchitems & FETCH_BODYSTRUCTURE) {
        if (!mailbox_cacherecord(mailbox, &im->record)) {
	    prot_printf(state->out, "%cBODYSTRUCTURE ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&im->record, CACHE_BODYSTRUCTURE));
	}
    }
    if (fetchitems & FETCH_BODY) {
        if (!mailbox_cacherecord(mailbox, &im->record)) {
	    prot_printf(state->out, "%cBODY ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&im->record, CACHE_BODY));
	}
    }

    if (fetchitems & FETCH_HEADER) {
	prot_printf(state->out, "%cRFC822.HEADER ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, msg_base, msg_size, 0,
		       im->record.header_size,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->start_octet : 0,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->octet_count : 0);
    }
    else if (fetchargs->headers.count || fetchargs->headers_not.count) {
	prot_printf(state->out, "%cRFC822.HEADER ", sepchar);
	sepchar = ' ';
	if (fetchargs->cache_atleast > im->record.cache_version) {
	    index_fetchheader(state, msg_base, msg_size,
			      im->record.header_size,
			      &fetchargs->headers, &fetchargs->headers_not);
	} else {
	    index_fetchcacheheader(state, &im->record, &fetchargs->headers, 0, 0);
	}
    }

    if (fetchitems & FETCH_TEXT) {
	prot_printf(state->out, "%cRFC822.TEXT ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, msg_base, msg_size,
		       im->record.header_size, im->record.size - im->record.header_size,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->start_octet : 0,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->octet_count : 0);
    }
    if (fetchitems & FETCH_RFC822) {
	prot_printf(state->out, "%cRFC822 ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, msg_base, msg_size, 0, im->record.size,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->start_octet : 0,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->octet_count : 0);
    }
    for (fsection = fetchargs->fsections; fsection; fsection = fsection->next) {
	int i;
	prot_printf(state->out, "%cBODY[%s ", sepchar, fsection->section);
	sepchar = '(';
	for (i = 0 ; i < fsection->fields->count ; i++) {
	    (void)prot_putc(sepchar, state->out);
	    sepchar = ' ';
	    prot_printastring(state->out, fsection->fields->data[i]);
	}
	(void)prot_putc(')', state->out);
	sepchar = ' ';

	oi = (struct octetinfo *)fsection->rock;

	prot_printf(state->out, "%s ", fsection->trail);

	if (fetchargs->cache_atleast > im->record.cache_version) {
	    if (!mailbox_cacherecord(mailbox, &im->record))
		index_fetchfsection(state, msg_base, msg_size,
				    fsection,
				    cacheitem_base(&im->record, CACHE_SECTION),
				    (fetchitems & FETCH_IS_PARTIAL) ?
				      fetchargs->start_octet : oi->start_octet,
				    (fetchitems & FETCH_IS_PARTIAL) ?
				      fetchargs->octet_count : oi->octet_count);
	    else
		prot_printf(state->out, "NIL");
	    
	}
	else {
	    index_fetchcacheheader(state, &im->record, fsection->fields,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				     fetchargs->start_octet : oi->start_octet,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				     fetchargs->octet_count : oi->octet_count);
	}
    }
    for (section = fetchargs->bodysections; section; section = section->next) {
	respbuf[0] = 0;
	if (sepchar == '(' && !started) {
	    /* we haven't output a fetch item yet, so start the response */
	    snprintf(respbuf, sizeof(respbuf), "* %u FETCH ", msgno);
	}
	snprintf(respbuf+strlen(respbuf), sizeof(respbuf)-strlen(respbuf),
		 "%cBODY[%s ", sepchar, section->name);

	oi = &section->octetinfo;

	if (!mailbox_cacherecord(mailbox, &im->record)) {
	    r = index_fetchsection(state, respbuf,
				   msg_base, msg_size,
				   section->name, cacheitem_base(&im->record, CACHE_SECTION),
				   im->record.size,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				    fetchargs->start_octet : oi->start_octet,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				    fetchargs->octet_count : oi->octet_count);
	    if (!r) sepchar = ' ';
	}
    }
    for (section = fetchargs->binsections; section; section = section->next) {
	respbuf[0] = 0;
	if (sepchar == '(' && !started) {
	    /* we haven't output a fetch item yet, so start the response */
	    snprintf(respbuf, sizeof(respbuf), "* %u FETCH ", msgno);
	}
	snprintf(respbuf+strlen(respbuf), sizeof(respbuf)-strlen(respbuf),
		 "%cBINARY[%s ", sepchar, section->name);

	if (!mailbox_cacherecord(mailbox, &im->record)) {
	    oi = &section->octetinfo;
	    r = index_fetchsection(state, respbuf,
				   msg_base, msg_size,
				   section->name, cacheitem_base(&im->record, CACHE_SECTION),
				   im->record.size,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				    fetchargs->start_octet : oi->start_octet,
				   (fetchitems & FETCH_IS_PARTIAL) ?
				    fetchargs->octet_count : oi->octet_count);
	    if (!r) sepchar = ' ';
	}
    }
    for (section = fetchargs->sizesections; section; section = section->next) {
	respbuf[0] = 0;
	if (sepchar == '(' && !started) {
	    /* we haven't output a fetch item yet, so start the response */
	    snprintf(respbuf, sizeof(respbuf), "* %u FETCH ", msgno);
	}
	snprintf(respbuf+strlen(respbuf), sizeof(respbuf)-strlen(respbuf),
		 "%cBINARY.SIZE[%s ", sepchar, section->name);

        if (!mailbox_cacherecord(mailbox, &im->record)) {
	    r = index_fetchsection(state, respbuf,
				   msg_base, msg_size,
				   section->name, cacheitem_base(&im->record, CACHE_SECTION),
				   im->record.size,
				   fetchargs->start_octet, fetchargs->octet_count);
	    if (!r) sepchar = ' ';
	}
    }
    if (sepchar != '(') {
	/* finsh the response if we have one */
	prot_printf(state->out, ")\r\n");
    }
    if (msg_base) 
	mailbox_unmap_message(mailbox, im->record.uid, &msg_base, &msg_size);

    return r;
}

/*
 * Fetch the text data associated with an IMAP URL.
 *
 * If outsize is NULL, the data will be output as a literal (URLFETCH),
 * otherwise just the data will be output (CATENATE), and its size returned
 * in *outsize.
 *
 * This is an amalgamation of index_fetchreply(), index_fetchsection()
 * and index_fetchmsg().
 */
int index_urlfetch(struct index_state *state, uint32_t msgno,
		   unsigned params, const char *section,
		   unsigned long start_octet, unsigned long octet_count,
		   struct protstream *pout, unsigned long *outsize)
{
    const char *data, *msg_base = 0;
    size_t msg_size = 0;
    const char *cacheitem;
    int fetchmime = 0, domain = DOMAIN_7BIT;
    size_t size;
    int32_t skip = 0;
    int n, r = 0;
    char *decbuf = NULL;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    if (outsize) *outsize = 0;

    r = mailbox_cacherecord(mailbox, &im->record);
    if (r) return r;

    /* Open the message file */
    if (mailbox_map_message(mailbox, im->record.uid, &msg_base, &msg_size))
	return IMAP_NO_MSGGONE;

    data = msg_base;
    size = im->record.size;

    if (size > msg_size) size = msg_size;

    cacheitem = cacheitem_base(&im->record, CACHE_SECTION);

    /* Special-case BODY[] */
    if (!section || !*section) {
	/* whole message, no further parsing */
    }
    else {
	const char *p = ucase((char *) section);

	while (*p && *p != 'M') {
	    int num_parts = CACHE_ITEM_BIT32(cacheitem);

	    /* Generate the actual part number */
	    r = parseint32(p, &p, &skip);
	    if (*p == '.') p++;

	    /* Handle .0, .HEADER, and .TEXT */
	    if (r || skip == 0) {
		skip = 0;
		/* We don't have any digits, so its a string */
		switch (*p) {
		case 'H':
		    p += 6;
		    fetchmime++;  /* .HEADER maps internally to .0.MIME */
		    break;

		case 'T':
		    p += 4;
		    break;	  /* .TEXT maps internally to .0 */

		default:
		    fetchmime++;  /* .0 maps internally to .0.MIME */
		    break;
		}
	    }

	    /* section number too large */
	    if (skip >= num_parts) {
		r = IMAP_BADURL;
		goto done;
	    }

	    if (*p && *p != 'M') {
		/* We are NOT at the end of a part specification, so there's
		 * a subpart being requested.  Find the subpart in the tree. */

		/* Skip the headers for this part, along with the number of
		 * sub parts */
		cacheitem += num_parts * 5 * 4 + CACHE_ITEM_SIZE_SKIP;

		/* Skip to the correct part */
		while (--skip) {
		    if (CACHE_ITEM_BIT32(cacheitem) > 0) {
			/* Skip each part at this level */
			skip += CACHE_ITEM_BIT32(cacheitem)-1;
			cacheitem += CACHE_ITEM_BIT32(cacheitem) * 5 * 4;
		    }
		    cacheitem += CACHE_ITEM_SIZE_SKIP;
		}
	    }
	}

	if (*p == 'M') fetchmime++;

	cacheitem += skip * 5 * 4 + CACHE_ITEM_SIZE_SKIP +
	    (fetchmime ? 0 : 2 * 4);
    
	if (CACHE_ITEM_BIT32(cacheitem + CACHE_ITEM_SIZE_SKIP) == (bit32) -1) {
	    r = IMAP_BADURL;
	    goto done;
	}

	data += CACHE_ITEM_BIT32(cacheitem);
	size = CACHE_ITEM_BIT32(cacheitem + CACHE_ITEM_SIZE_SKIP);
    }

    /* Handle extended URLFETCH parameters */
    if (params & URLFETCH_BODYPARTSTRUCTURE) {
	prot_printf(pout, " (BODYPARTSTRUCTURE");
	/* XXX Calculate body part structure */
	prot_printf(pout, " NIL");
	prot_printf(pout, ")");
    }

    if (params & URLFETCH_BODY) {
	prot_printf(pout, " (BODY");
    }
    else if (params & URLFETCH_BINARY) {
	int encoding = CACHE_ITEM_BIT32(cacheitem + 2 * 4) & 0xff;

	prot_printf(pout, " (BINARY");

	data = charset_decode_mimebody(data, size, encoding,
				       &decbuf, &size);
	if (!data) {
	    /* failed to decode */
	    prot_printf(pout, " NIL)");
	    r = 0;
	    goto done;
	}
    }

    /* Handle PARTIAL request */
    n = octet_count ? octet_count : size;

    /* Sanity check the requested size */
    if (start_octet + n > size) n = size - start_octet;

    if (outsize) {
	/* Return size (CATENATE) */
	*outsize = n;
    } else {
	domain = data_domain(data + start_octet, n);

	if (domain == DOMAIN_BINARY) {
	    /* Write size of literal8 */
	    prot_printf(pout, " ~{%u}\r\n", n);
	} else {
	    /* Write size of literal */
	    prot_printf(pout, " {%u}\r\n", n);
	}
    }

    /* Non-text literal -- tell the protstream about it */
    if (domain != DOMAIN_7BIT) prot_data_boundary(pout);

    prot_write(pout, data + start_octet, n);

    /* End of non-text literal -- tell the protstream about it */
    if (domain != DOMAIN_7BIT) prot_data_boundary(pout);

    /* Complete extended URLFETCH response */
    if (params & (URLFETCH_BODY | URLFETCH_BINARY)) prot_printf(pout, ")");

    r = 0;

  done:
    /* Close the message file */
    mailbox_unmap_message(mailbox, im->record.uid, &msg_base, &msg_size);

    if (decbuf) free(decbuf);
    return r;
}

/*
 * Helper function to perform a STORE command for flags.
 */
static int index_storeflag(struct index_state *state, uint32_t msgno,
			   struct storeargs *storeargs)
{
    bit32 old, new;
    unsigned i;
    int dirty = 0;
    modseq_t oldmodseq;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];
    int r;

    oldmodseq = im->record.modseq;

    /* Change \Seen flag */
    if (state->myrights & ACL_SETSEEN) {
	old = im->isseen ? 1 : 0;
	new = old;
	if (storeargs->operation == STORE_REPLACE_FLAGS)
	    new = storeargs->seen ? 1 : 0;
	else if (storeargs->seen)
	    new = (storeargs->operation == STORE_ADD_FLAGS) ? 1 : 0;

	if (new != old) {
	    state->numunseen += (old - new);
	    im->isseen = new;
	    state->seen_dirty = 1;
	    dirty++;
	}
    }

    old = im->record.system_flags;
    new = storeargs->system_flags;

    if (storeargs->operation == STORE_REPLACE_FLAGS) {
	if (!(state->myrights & ACL_WRITE)) {
	    /* ACL_DELETE handled in index_store() */
	    if ((old & FLAG_DELETED) != (new & FLAG_DELETED)) {
		dirty++;
	        im->record.system_flags = (old & ~FLAG_DELETED) | (new & FLAG_DELETED);
	    }
	}
	else {
	    if (!(state->myrights & ACL_DELETEMSG)) {
		if ((old & ~FLAG_DELETED) != (new & ~FLAG_DELETED)) {
		    dirty++;
		    im->record.system_flags = (old & FLAG_DELETED) | (new & ~FLAG_DELETED);
		}
	    }
	    else {
		if (old != new) {
		    dirty++;
		    im->record.system_flags = new;
		}
	    }
	    for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
		if (im->record.user_flags[i] != storeargs->user_flags[i]) {
		    dirty++;
		    im->record.user_flags[i] = storeargs->user_flags[i];
		}
	    }
	}
    }
    else if (storeargs->operation == STORE_ADD_FLAGS) {
	if (~old & new) {
	    dirty++;
	    im->record.system_flags = old | new;
	}
	for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	    if (~im->record.user_flags[i] & storeargs->user_flags[i]) {
		dirty++;
		im->record.user_flags[i] |= storeargs->user_flags[i];
	    }
	}
    }
    else { /* STORE_REMOVE_FLAGS */
	if (old & new) {
	    dirty++;
	    im->record.system_flags &= ~storeargs->system_flags;
	}
	for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	    if (im->record.user_flags[i] & storeargs->user_flags[i]) {
		dirty++;
		im->record.user_flags[i] &= ~storeargs->user_flags[i];
	    }
	}
    }

    /* rfc4551:
     * 3.8.  Additional Quality-of-Implementation Issues
     *
     * Server implementations should follow the following rule, which
     * applies to any successfully completed STORE/UID STORE (with and
     * without UNCHANGEDSINCE modifier), as well as to a FETCH command that
     * implicitly sets \Seen flag:
     *
     *    Adding the flag when it is already present or removing when it is
     *    not present SHOULD NOT change the mod-sequence.
     *
     * This will prevent spurious client synchronization requests.
     */
    if (!dirty) return 0;

    if (state->internalseen) {
	/* set the seen flag */
	if (im->isseen)
	    im->record.system_flags |= FLAG_SEEN;
	else
	    im->record.system_flags &= ~FLAG_SEEN;
    }

    r = mailbox_rewrite_index_record(mailbox, &im->record);
    if (r) return r;

    /* if it's silent and unchanged, update the seen value, but
     * not if qresync is enabled - RFC 4551 says that the MODSEQ
     * must always been told, and we prefer just to tell flags
     * as well in this case, it's simpler and not much more
     * bandwidth */
    if (!state->qresync && storeargs->silent && im->told_modseq == oldmodseq)
	im->told_modseq = im->record.modseq;

    return 0;
}

/*
 * Helper function to perform a STORE command for annotations
 */
static int index_store_annotation(struct index_state *state,
				  uint32_t msgno,
				  struct storeargs *storeargs)
{
    modseq_t oldmodseq;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];
    annotate_state_t *astate = NULL;
    int r;

    oldmodseq = im->record.modseq;

    r = mailbox_get_annotate_state(state->mailbox, im->record.uid, &astate);
    if (r) goto out;
    annotate_state_set_auth(astate, storeargs->isadmin,
			    storeargs->userid, storeargs->authstate);
    r = annotate_state_store(astate, storeargs->entryatts);
    if (r) goto out;

    /* It would be nice if the annotate layer told us whether it
     * actually made a change to the database, but it doesn't, so
     * we have to assume the message is dirty */

    r = mailbox_rewrite_index_record(mailbox, &im->record);
    if (r) goto out;

    /* if it's silent and unchanged, update the seen value */
    if (!state->qresync && storeargs->silent && im->told_modseq == oldmodseq)
	im->told_modseq = im->record.modseq;

out:
    return r;
}


int _search_searchbuf(char *s, comp_pat *p, struct buf *b)
{
    if (!b->len)
	return 0;

    return charset_searchstring(s, p, b->s, b->len, charset_flags);
}

struct search_annot_rock {
    int result;
    const struct buf *match;
};

static int _search_annot_match(const struct buf *match,
			       const struct buf *value)
{
    /* These cases are not explicitly defined in RFC5257 */

    /* NIL matches NIL and nothing else */
    if (match->s == NULL)
	return (value->s == NULL);
    if (value->s == NULL)
	return 0;

    /* empty matches empty and nothing else */
    if (match->len == 0)
	return (value->len == 0);
    if (value->len == 0)
	return 0;

    /* RFC5257 seems to define a simple CONTAINS style search */
    return !!memmem(value->s, value->len,
		    match->s, match->len);
}

static void _search_annot_callback(const char *mboxname
				    __attribute__((unused)),
				   uint32_t uid
				    __attribute__((unused)),
				   const char *entry
				    __attribute__((unused)),
				   struct attvaluelist *attvalues,
				   void *rock)
{
    struct search_annot_rock *sarock = rock;
    struct attvaluelist *l;

    for (l = attvalues ; l ; l = l->next) {
	if (_search_annot_match(sarock->match, &l->value))
	    sarock->result = 1;
    }
}

static int _search_annotation(struct index_state *state,
			      uint32_t msgno,
			      struct searchannot *sa)
{
    strarray_t entries = STRARRAY_INITIALIZER;
    strarray_t attribs = STRARRAY_INITIALIZER;
    annotate_state_t *astate = NULL;
    struct search_annot_rock rock;
    int r;

    strarray_append(&entries, sa->entry);
    strarray_append(&attribs, sa->attrib);

    r = mailbox_get_annotate_state(state->mailbox,
			           state->map[msgno-1].record.uid,
				   &astate);
    if (r) goto out;
    annotate_state_set_auth(astate, sa->isadmin,
			    sa->userid, sa->auth_state);

    memset(&rock, 0, sizeof(rock));
    rock.match = &sa->value;

    r = annotate_state_fetch(astate,
			     &entries, &attribs,
			     _search_annot_callback, &rock,
			     0);
    if (r >= 0)
	r = rock.result;

out:
    strarray_fini(&entries);
    strarray_fini(&attribs);
    return r;
}

/*
 * Evaluate a searchargs structure on a msgno
 *
 * Note: msgfile argument must be 0 if msg is not mapped in.
 */
static int index_search_evaluate(struct index_state *state,
				 struct searchargs *searchargs,
				 uint32_t msgno,
				 struct mapfile *msgfile)
{
    unsigned i;
    struct strlist *l, *h;
    struct searchsub *s;
    struct seqset *seq;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];
    conversation_t *conv = NULL;
    struct searchannot *sa;
    struct mapfile localmap = MAPFILE_INITIALIZER;
    int retval = 0;

    if (!msgfile) msgfile = &localmap;

    if ((searchargs->flags & SEARCH_RECENT_SET) && !im->isrecent)
	goto zero;
    if ((searchargs->flags & SEARCH_RECENT_UNSET) && im->isrecent)
	goto zero;
    if ((searchargs->flags & SEARCH_SEEN_SET) && !im->isseen)
	goto zero;
    if ((searchargs->flags & SEARCH_SEEN_UNSET) && im->isseen)
	goto zero;

    if (searchargs->smaller && im->record.size >= searchargs->smaller)
	goto zero;
    if (searchargs->larger && im->record.size <= searchargs->larger)
	goto zero;

    if (searchargs->after && im->record.internaldate < searchargs->after)
	goto zero;
    if (searchargs->before && im->record.internaldate >= searchargs->before)
	goto zero;
    if (searchargs->sentafter && im->record.sentdate < searchargs->sentafter)
	goto zero;
    if (searchargs->sentbefore && im->record.sentdate >= searchargs->sentbefore)
	goto zero;

    if (searchargs->modseq && im->record.modseq < searchargs->modseq)
	goto zero;

    if (~im->record.system_flags & searchargs->system_flags_set)
	goto zero;
    if (im->record.system_flags & searchargs->system_flags_unset)
	goto zero;

    for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	if (~im->record.user_flags[i] & searchargs->user_flags_set[i])
	    goto zero;
	if (im->record.user_flags[i] & searchargs->user_flags_unset[i])
	    goto zero;
    }

    for (seq = searchargs->sequence; seq; seq = seq->nextseq) {
	if (!seqset_ismember(seq, msgno)) goto zero;
    }
    for (seq = searchargs->uidsequence; seq; seq = seq->nextseq) {
	if (!seqset_ismember(seq, im->record.uid)) goto zero;
    }

    if (searchargs->from || searchargs->to || searchargs->cc ||
	searchargs->bcc || searchargs->subject || searchargs->messageid) {

	if (mailbox_cacherecord(mailbox, &im->record))
	    goto zero;

	if (searchargs->messageid) {
	    char *tmpenv;
	    char *envtokens[NUMENVTOKENS];
	    char *msgid;
	    int msgidlen;

	    /* must be long enough to actually HAVE some contents */
	    if (cacheitem_size(&im->record, CACHE_ENVELOPE) <= 2)
		goto zero;

	    /* get msgid out of the envelope */

	    /* get a working copy; strip outer ()'s */
	    /* +1 -> skip the leading paren */
	    /* -2 -> don't include the size of the outer parens */
	    tmpenv = xstrndup(cacheitem_base(&im->record, CACHE_ENVELOPE) + 1, 
			      cacheitem_size(&im->record, CACHE_ENVELOPE) - 2);
	    parse_cached_envelope(tmpenv, envtokens, VECTOR_SIZE(envtokens));

	    if (!envtokens[ENV_MSGID]) {
		/* free stuff */
		free(tmpenv);
		goto zero;
	    }

	    msgid = lcase(envtokens[ENV_MSGID]);
	    msgidlen = strlen(msgid);
	    for (l = searchargs->messageid; l; l = l->next) {
		if (!charset_searchstring(l->s, l->p, msgid, msgidlen, charset_flags))
		    break;
	    }

	    /* free stuff */
	    free(tmpenv);

	    if (l) goto zero;
	}

	for (l = searchargs->from; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&im->record, CACHE_FROM)))
		goto zero;
	}

	for (l = searchargs->to; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&im->record, CACHE_TO)))
		goto zero;
	}

	for (l = searchargs->cc; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&im->record, CACHE_CC)))
		goto zero;
	}

	for (l = searchargs->bcc; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&im->record, CACHE_BCC)))
		goto zero;
	}

	for (l = searchargs->subject; l; l = l->next) {
	    if ((cacheitem_size(&im->record, CACHE_SUBJECT) == 3 && 
		!strncmp(cacheitem_base(&im->record, CACHE_SUBJECT), "NIL", 3)) ||
		!_search_searchbuf(l->s, l->p, cacheitem_buf(&im->record, CACHE_SUBJECT)))
		goto zero;
	}
    }

    for (sa = searchargs->annotations ; sa ; sa = sa->next) {
	if (!_search_annotation(state, msgno, sa))
	    goto zero;
    }

    for (s = searchargs->sublist; s; s = s->next) {
	if (index_search_evaluate(state, s->sub1, msgno, msgfile)) {
	    if (!s->sub2) goto zero;
	}
	else {
	    if (s->sub2 &&
		!index_search_evaluate(state, s->sub2, msgno, msgfile))
	      goto zero;
	}
    }

    if (searchargs->body || searchargs->text ||
	searchargs->cache_atleast > im->record.cache_version) {
	if (!msgfile->size) { /* Map the message in if we haven't before */
	    if (mailbox_map_message(mailbox, im->record.uid,
				    &msgfile->base, &msgfile->size)) {
		goto zero;
	    }
	}

	h = searchargs->header_name;
	for (l = searchargs->header; l; (l = l->next), (h = h->next)) {
	    if (!index_searchheader(h->s, l->s, l->p, msgfile,
				    im->record.header_size)) goto zero;
	}

	if (mailbox_cacherecord(mailbox, &im->record))
	    goto zero;

	for (l = searchargs->body; l; l = l->next) {
	    if (!index_searchmsg(l->s, l->p, msgfile, 1,
				 cacheitem_base(&im->record, CACHE_SECTION))) goto zero;
	}
	for (l = searchargs->text; l; l = l->next) {
	    if (!index_searchmsg(l->s, l->p, msgfile, 0,
				 cacheitem_base(&im->record, CACHE_SECTION))) goto zero;
	}
    }
    else if (searchargs->header_name) {
	h = searchargs->header_name;
	for (l = searchargs->header; l; (l = l->next), (h = h->next)) {
	    if (!index_searchcacheheader(state, msgno, h->s, l->s, l->p))
		goto zero;
	}
    }

    if (searchargs->convmodseq || searchargs->convflags ||
	searchargs->flags & (SEARCH_CONVSEEN_SET | SEARCH_CONVSEEN_UNSET)) {
	struct conversations_state *cstate = conversations_get_mbox(state->mailbox->name);
	if (!cstate) goto zero;
	if (conversation_load(cstate, im->record.cid, &conv))
	    goto zero;
	if (!conv) conv = conversation_new(cstate);

	/* got a conversation, let's check it */
	if (searchargs->convmodseq && conv->modseq < searchargs->convmodseq)
	    goto zero;

	if ((searchargs->flags & SEARCH_CONVSEEN_SET) && conv->unseen)
	    goto zero;

	if ((searchargs->flags & SEARCH_CONVSEEN_UNSET) && !conv->unseen)
	    goto zero;

	for (l = searchargs->convflags; l; l = l->next) {
	    int idx = strarray_find_case(cstate->counted_flags, l->s, 0);
	    if (idx < 0)
		goto zero;
	    if (!conv->counts[idx])
		goto zero;
	}
    }

    retval = 1;

zero:

    /* free conversation data */
    conversation_free(conv);

    /* unmap if we mapped it */
    if (localmap.size) {
	mailbox_unmap_message(mailbox, im->record.uid,
			      &localmap.base, &localmap.size);
    }

    return retval;
}

/*
 * Search part of a message for a substring.
 * Keep this in sync with index_getsearchtextmsg!
 */
static int index_searchmsg(char *substr,
			   comp_pat *pat,
			   struct mapfile *msgfile,
			   int skipheader,
			   const char *cachestr)
{
    int partsleft = 1;
    int subparts;
    unsigned long start;
    int len, charset, encoding;
    char *p;
    
    /* Won't find anything in a truncated file */
    if (msgfile->size == 0) return 0;

    while (partsleft--) {
	subparts = CACHE_ITEM_BIT32(cachestr);
	cachestr += 4;
	if (subparts) {
	    partsleft += subparts-1;

	    if (skipheader) {
		skipheader = 0; /* Only skip top-level message header */
	    }
	    else {
		len = CACHE_ITEM_BIT32(cachestr + CACHE_ITEM_SIZE_SKIP);
		if (len > 0) {
		    p = index_readheader(msgfile->base, msgfile->size,
					 CACHE_ITEM_BIT32(cachestr),
					 len);
		    if (p) {
			if (charset_search_mimeheader(substr, pat, p, charset_flags))
			    return 1;
		    }
		}
	    }
	    cachestr += 5*4;

	    while (--subparts) {
		start = CACHE_ITEM_BIT32(cachestr+2*4);
		len = CACHE_ITEM_BIT32(cachestr+3*4);
		charset = CACHE_ITEM_BIT32(cachestr+4*4) >> 16;
		encoding = CACHE_ITEM_BIT32(cachestr+4*4) & 0xff;

		if (start < msgfile->size && len > 0 &&
		    charset >= 0 && charset < 0xffff) {
		    if (charset_searchfile(substr, pat,
					   msgfile->base + start,
					   len, charset, encoding, charset_flags)) return 1;
		}
		cachestr += 5*4;
	    }
	}
    }

    return 0;
}
    
/*
 * Search named header of a message for a substring
 */
static int index_searchheader(char *name,
			      char *substr,
			      comp_pat *pat,
			      struct mapfile *msgfile,
			      int size)
{
    char *p;
    strarray_t header = STRARRAY_INITIALIZER;

    strarray_append(&header, name);

    p = index_readheader(msgfile->base, msgfile->size, 0, size);
    message_pruneheader(p, &header, 0);
    strarray_fini(&header);

    if (!*p) return 0;		/* Header not present, fail */
    if (!*substr) return 1;	/* Only checking existence, succeed */

    return charset_search_mimeheader(substr, pat, strchr(p, ':') + 1, charset_flags);
}

/*
 * Search named cached header of a message for a substring
 */
static int index_searchcacheheader(struct index_state *state, uint32_t msgno,
				   char *name, char *substr, comp_pat *pat)
{
    strarray_t header = STRARRAY_INITIALIZER;
    static char *buf;
    static unsigned bufsize;
    unsigned size;
    int r;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    r = mailbox_cacherecord(mailbox, &im->record);
    if (r) return 0;

    size = cacheitem_size(&im->record, CACHE_HEADERS);
    if (!size) return 0;	/* No cached headers, fail */
    
    if (bufsize < size+2) {
	bufsize = size+100;
	buf = xrealloc(buf, bufsize);
    }

    /* Copy this item to the buffer */
    memcpy(buf, cacheitem_base(&im->record, CACHE_HEADERS), size);
    buf[size] = '\0';

    strarray_append(&header, name);
    message_pruneheader(buf, &header, 0);
    strarray_fini(&header);

    if (!*buf) return 0;	/* Header not present, fail */
    if (!*substr) return 1;	/* Only checking existence, succeed */

    return charset_search_mimeheader(substr, pat, strchr(buf, ':') + 1, charset_flags);
}


/* This code was cribbed from index_searchmsg. Instead of checking for matches,
   we call charset_extractfile to send the entire text out to 'receiver'.
   Keep this in sync with index_searchmsg! */
static void index_getsearchtextmsg(struct index_state *state,
				   int uid,
				   index_search_text_receiver_t receiver,
				   void *rock,
				   char const *cachestr) {
    struct mapfile msgfile = MAPFILE_INITIALIZER;
    int partsleft = 1;
    int subparts;
    unsigned long start;
    int len, charset, encoding;
    int partcount = 0;
    char *p, *q;
    struct mailbox *mailbox = state->mailbox;
  
    if (mailbox_map_message(mailbox, uid, &msgfile.base, &msgfile.size))
	return;

    /* Won't find anything in a truncated file */
    if (msgfile.size > 0) {
	while (partsleft--) {
	    subparts = CACHE_ITEM_BIT32(cachestr);
	    cachestr += 4;
	    if (subparts) {
		partsleft += subparts-1;

		partcount++;

		len = CACHE_ITEM_BIT32(cachestr+4);
		if (len > 0) {
		    p = index_readheader(msgfile.base, msgfile.size,
					 CACHE_ITEM_BIT32(cachestr),
					 len);
		    if (p) {
			/* push search normalised here */
			q = charset_decode_mimeheader(p, charset_flags);
			if (partcount == 1) {
			    receiver(uid, SEARCHINDEX_PART_HEADERS,
				     SEARCHINDEX_CMD_STUFFPART, q, strlen(q), rock);
			    receiver(uid, SEARCHINDEX_PART_BODY,
				     SEARCHINDEX_CMD_BEGINPART, NULL, 0, rock);
			} else {
			    receiver(uid, SEARCHINDEX_PART_BODY,
				 SEARCHINDEX_CMD_APPENDPART, q, strlen(q), rock);
			}
			free(q);
		    }
		}
		cachestr += 5*4;

		while (--subparts) {
		    start = CACHE_ITEM_BIT32(cachestr+2*4);
		    len = CACHE_ITEM_BIT32(cachestr+3*4);
		    charset = CACHE_ITEM_BIT32(cachestr+4*4) >> 16;
		    encoding = CACHE_ITEM_BIT32(cachestr+4*4) & 0xff;

		    if (start < msgfile.size && len > 0) {
		      charset_extractfile(receiver, rock, uid,
					  msgfile.base + start,
					  len, charset, encoding, charset_flags);
		    }
		    cachestr += 5*4;
		}
	    }
	}

	receiver(uid, SEARCHINDEX_PART_BODY,
		 SEARCHINDEX_CMD_ENDPART, NULL, 0, rock);
    }

    mailbox_unmap_message(mailbox, uid, &msgfile.base, &msgfile.size);
}

void index_getsearchtext_single(struct index_state *state, uint32_t msgno,
				index_search_text_receiver_t receiver,
				void *rock) {
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];
    int utf8 = charset_lookupname("utf-8");

    assert(utf8 >= 0);

    if (mailbox_cacherecord(mailbox, &im->record))
	return;

    index_getsearchtextmsg(state, im->record.uid, receiver, rock,
	     cacheitem_base(&im->record, CACHE_SECTION));

    charset_extractitem(receiver, rock, im->record.uid,
			cacheitem_base(&im->record, CACHE_FROM),
			cacheitem_size(&im->record, CACHE_FROM),
			utf8, ENCODING_NONE, charset_flags,
			SEARCHINDEX_PART_FROM,
			SEARCHINDEX_CMD_STUFFPART);

    charset_extractitem(receiver, rock, im->record.uid,
			cacheitem_base(&im->record, CACHE_TO),
			cacheitem_size(&im->record, CACHE_TO),
			utf8, ENCODING_NONE, charset_flags,
			SEARCHINDEX_PART_TO,
			SEARCHINDEX_CMD_STUFFPART);

    charset_extractitem(receiver, rock, im->record.uid,
			cacheitem_base(&im->record, CACHE_CC),
			cacheitem_size(&im->record, CACHE_CC),
			utf8, ENCODING_NONE, charset_flags,
			SEARCHINDEX_PART_CC,
			SEARCHINDEX_CMD_STUFFPART);

    charset_extractitem(receiver, rock, im->record.uid,
			cacheitem_base(&im->record, CACHE_BCC),
			cacheitem_size(&im->record, CACHE_BCC),
			utf8, ENCODING_NONE, charset_flags,
			SEARCHINDEX_PART_BCC,
			SEARCHINDEX_CMD_STUFFPART);

    charset_extractitem(receiver, rock, im->record.uid,
			cacheitem_base(&im->record, CACHE_SUBJECT),
			cacheitem_size(&im->record, CACHE_SUBJECT),
			utf8, ENCODING_NONE, charset_flags,
			SEARCHINDEX_PART_SUBJECT,
			SEARCHINDEX_CMD_STUFFPART);
}

void index_getsearchtext(struct index_state *state,
			 index_search_text_receiver_t receiver,
			 void *rock)
{
    uint32_t msgno;

    /* Send the converted text of every message out to the receiver. */
    for (msgno = 1; msgno <= state->exists; msgno++)
	index_getsearchtext_single(state, msgno, receiver, rock);
}

/*
 * Helper function to set up arguments to append_copy()
 */
#define COPYARGSGROW 30
static int index_copysetup(struct index_state *state, uint32_t msgno,
			   struct copyargs *copyargs, int is_same_user)
{
    int flag = 0;
    int userflag;
    bit32 flagmask = 0;
    int r;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    r = mailbox_cacherecord(mailbox, &im->record);
    if (r) return r;

    if (copyargs->nummsg == copyargs->msgalloc) {
	copyargs->msgalloc += COPYARGSGROW;
	copyargs->copymsg = (struct copymsg *)
	  xrealloc((char *)copyargs->copymsg,
		   copyargs->msgalloc * sizeof(struct copymsg));
    }

    copyargs->copymsg[copyargs->nummsg].uid = im->record.uid;
    copyargs->copymsg[copyargs->nummsg].internaldate = im->record.internaldate;
    copyargs->copymsg[copyargs->nummsg].sentdate = im->record.sentdate;
    copyargs->copymsg[copyargs->nummsg].gmtime = im->record.gmtime;
    copyargs->copymsg[copyargs->nummsg].size = im->record.size;
    copyargs->copymsg[copyargs->nummsg].header_size = im->record.header_size;
    copyargs->copymsg[copyargs->nummsg].content_lines = im->record.content_lines;
    copyargs->copymsg[copyargs->nummsg].cache_version = im->record.cache_version;
    copyargs->copymsg[copyargs->nummsg].cache_crc = im->record.cache_crc;
    copyargs->copymsg[copyargs->nummsg].crec = im->record.crec;

    message_guid_copy(&copyargs->copymsg[copyargs->nummsg].guid,
		      &im->record.guid);

    copyargs->copymsg[copyargs->nummsg].system_flags = im->record.system_flags;
    for (userflag = 0; userflag < MAX_USER_FLAGS; userflag++) {
	if ((userflag & 31) == 0) {
	    flagmask = im->record.user_flags[userflag/32];
	}
	if (mailbox->flagname[userflag] && (flagmask & (1<<(userflag&31)))) {
	    copyargs->copymsg[copyargs->nummsg].flag[flag++] =
		mailbox->flagname[userflag];
	}
    }
    copyargs->copymsg[copyargs->nummsg].flag[flag] = 0;

    /* grab seen from our state - it's different for different users */
    copyargs->copymsg[copyargs->nummsg].seen = im->isseen;

    /* CIDs are per-user, so we can reuse the cid if we're copying
     * between mailboxes owned by the same user.  Otherwise we need
     * to zap the cid and let append_copy() recalculate it. */
    copyargs->copymsg[copyargs->nummsg].cid =
		    (is_same_user ? im->record.cid : NULLCONVERSATION);

    copyargs->nummsg++;

    return 0;
}

/*
 * Creates a list, and optionally also an array of pointers to, of msgdata.
 *
 * We fill these structs with the processed info that will be needed
 * by the specified sort criteria.
 */
static MsgData **index_msgdata_load(struct index_state *state,
				    unsigned *msgno_list, int n,
				    struct sortcrit *sortcrit,
				    unsigned int anchor, int *found_anchor)
{
    MsgData **ptrs, *md, *cur;
    int i, j;
    char *tmpenv;
    char *envtokens[NUMENVTOKENS];
    int did_cache, did_env, did_conv;
    int label;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im;
    struct conversations_state *cstate = NULL;
    conversation_t *conv = NULL;

    if (!n) return NULL;

    /* create an array of MsgData */
    ptrs = (MsgData **) xzmalloc(n * sizeof(MsgData *) + n * sizeof(MsgData));
    md = (MsgData *)(ptrs + n);

    if (found_anchor)
	*found_anchor = 0;

    for (i = 0 ; i < n ; i++) {
	cur = &md[i];
	ptrs[i] = cur;
	/* set msgno */
	cur->msgno = (msgno_list ? msgno_list[i] : (unsigned)(i+1));
	im = &state->map[cur->msgno-1];
	cur->uid = im->record.uid;
	if (found_anchor && im->record.uid == anchor)
	    *found_anchor = 1;

	did_cache = did_env = did_conv = 0;
	tmpenv = NULL;
	conv = NULL; /* XXX: use a hash to avoid re-reading? */

	for (j = 0; sortcrit[j].key; j++) {
	    label = sortcrit[j].key;

	    if ((label == SORT_CC || label == SORT_DATE ||
		 label == SORT_FROM || label == SORT_SUBJECT ||
		 label == SORT_TO || label == LOAD_IDS ||
		 label == SORT_DISPLAYFROM || label == SORT_DISPLAYTO) &&
		!did_cache) {

		/* fetch cached info */
		if (mailbox_cacherecord(mailbox, &im->record))
		    continue; /* can't do this with a broken cache */

		did_cache++;
	    }

	    if ((label == LOAD_IDS) && !did_env) {
		/* no point if we don't have enough data */
		if (cacheitem_size(&im->record, CACHE_ENVELOPE) <= 2)
		    continue;

		/* make a working copy of envelope -- strip outer ()'s */
		/* +1 -> skip the leading paren */
		/* -2 -> don't include the size of the outer parens */
		tmpenv = xstrndup(cacheitem_base(&im->record, CACHE_ENVELOPE) + 1, 
				  cacheitem_size(&im->record, CACHE_ENVELOPE) - 2);

		/* parse envelope into tokens */
		parse_cached_envelope(tmpenv, envtokens,
				      VECTOR_SIZE(envtokens));

		did_env++;
	    }

	    if ((label == SORT_HASCONVFLAG || label == SORT_CONVMODSEQ ||
		label == SORT_CONVEXISTS) && !did_conv) {
		if (!cstate) cstate = conversations_get_mbox(state->mailbox->name);
		assert(cstate);
		if (conversation_load(cstate, im->record.cid, &conv))
		    continue;
		did_conv++;
	    }

	    switch (label) {
	    case SORT_CC:
		cur->cc = get_localpart_addr(cacheitem_base(&im->record, CACHE_CC));
		break;
	    case SORT_DATE:
		cur->date = im->record.gmtime;
		/* fall through */
	    case SORT_ARRIVAL:
		cur->internaldate = im->record.internaldate;
		break;
	    case SORT_FROM:
		cur->from = get_localpart_addr(cacheitem_base(&im->record, CACHE_FROM));
		break;
	    case SORT_MODSEQ:
		cur->modseq = im->record.modseq;
		break;
	    case SORT_SIZE:
		cur->size = im->record.size;
		break;
	    case SORT_SUBJECT:
		cur->xsubj = index_extract_subject(cacheitem_base(&im->record, CACHE_SUBJECT),
						   cacheitem_size(&im->record, CACHE_SUBJECT),
						   &cur->is_refwd);
		cur->xsubj_hash = strhash(cur->xsubj);
		break;
	    case SORT_TO:
		cur->to = get_localpart_addr(cacheitem_base(&im->record, CACHE_TO));
		break;
 	    case SORT_ANNOTATION: {
		struct buf value = BUF_INITIALIZER;

		annotatemore_msg_lookup(state->mailbox->name,
					im->record.uid,
					sortcrit[j].args.annot.entry,
					sortcrit[j].args.annot.userid,
					&value);

		/* buf_release() never returns NULL, so if the lookup
		 * fails for any reason we just get an empty string here */
		strarray_appendm(&cur->annot, buf_release(&value));
 		break;
	    }
	    case LOAD_IDS:
		index_get_ids(cur, envtokens, cacheitem_base(&im->record, CACHE_HEADERS),
					      cacheitem_size(&im->record, CACHE_HEADERS));
		break;
	    case SORT_DISPLAYFROM:
		cur->displayfrom = get_displayname(
				   cacheitem_base(&im->record, CACHE_FROM));
		break;
	    case SORT_DISPLAYTO:
		cur->displayto = get_displayname(
				 cacheitem_base(&im->record, CACHE_TO));
		break;
	    case SORT_HASFLAG: {
		const char *name = sortcrit[j].args.flag.name;
		if (mailbox_record_hasflag(mailbox, &im->record, name))
		    cur->hasflag |= (1<<j);
		break;
	    }
	    case SORT_HASCONVFLAG: {
		const char *name = sortcrit[j].args.flag.name;
		int idx = strarray_find_case(cstate->counted_flags, name, 0);
		/* flag exists in the conversation at all */
		if (idx >= 0 && conv->counts[idx] > 0 && j < 31)
		    cur->hasconvflag |= (1<<j);
		break;
	    }
	    case SORT_CONVEXISTS:
		cur->convexists = conv->exists;
		break;
	    case SORT_CONVMODSEQ:
		cur->convmodseq = conv->modseq;
		break;
	    }
	}

	free(tmpenv);
	conversation_free(conv);
    }

    return ptrs;
}

static char *get_localpart_addr(const char *header)
{
    struct address *addr = NULL;
    char *ret = NULL;

    parseaddr_list(header, &addr);
    if (!addr) return NULL;

    if (addr->mailbox)
	ret = xstrdup(addr->mailbox);

    parseaddr_free(addr);

    return ret;
}

/*
 * Get the 'display-name' of an address from a header
 */
static char *get_displayname(const char *header)
{
    struct address *addr = NULL;
    char *ret = NULL;
    char *p;

    parseaddr_list(header, &addr);
    if (!addr) return NULL;

    if (addr->name && addr->name[0]) {
	/* pure RFC5255 compatible "searchform" conversion */
	ret = charset_utf8_to_searchform(addr->name, /*flags*/0);
    }
    else if (addr->domain && addr->mailbox) {
	ret = strconcat(addr->mailbox, "@", addr->domain, (char *)NULL);
	/* gotta uppercase mailbox/domain */
	for (p = ret; *p; p++)
	    *p = toupper(*p);
    }
    else if (addr->mailbox) {
	ret = xstrdup(addr->mailbox);
	/* gotta uppercase mailbox/domain */
	for (p = ret; *p; p++)
	    *p = toupper(*p);
    }

    parseaddr_free(addr);

    return ret;
}

/*
 * Extract base subject from subject header
 *
 * This is a wrapper around _index_extract_subject() which preps the
 * subj NSTRING and checks for Netscape "[Fwd: ]".
 */
static char *index_extract_subject(const char *subj, size_t len, int *is_refwd)
{
    char *rawbuf, *buf, *s, *base;

    /* parse the subj NSTRING and make a working copy */
    if (!strcmp(subj, "NIL")) {		       	/* NIL? */
	return xstrdup("");			/* yes, return empty */
    } else if (*subj == '"') {			/* quoted? */
	rawbuf = xstrndup(subj + 1, len - 2);	/* yes, strip quotes */
    } else {
	s = strchr(subj, '}') + 3;		/* literal, skip { }\r\n */
	rawbuf = xstrndup(s, len - (s - subj));
    }

    buf = charset_parse_mimeheader(rawbuf);
    free(rawbuf);

    for (s = buf;;) {
	base = _index_extract_subject(s, is_refwd);

	/* If we have a Netscape "[Fwd: ...]", extract the contents */
	if (!strncasecmp(base, "[fwd:", 5) &&
	    base[strlen(base) - 1]  == ']') {

	    /* inc refwd counter */
	    *is_refwd += 1;

	    /* trim "]" */
	    base[strlen(base) - 1] = '\0';

	    /* trim "[fwd:" */
	    s = base + 5;
	}
	else /* otherwise, we're done */
	    break;
    }

    base = xstrdup(base);

    free(buf);

    for (s = base; *s; s++) {
	*s = toupper(*s);
    }

    return base;
}

/*
 * Guts if subject extraction.
 *
 * Takes a subject string and returns a pointer to the base.
 */
static char *_index_extract_subject(char *s, int *is_refwd)
{
    char *base, *x;

    /* trim trailer
     *
     * start at the end of the string and work towards the front,
     * resetting the end of the string as we go.
     */
    for (x = s + strlen(s) - 1; x >= s;) {
	if (Uisspace(*x)) {                             /* whitespace? */
	    *x = '\0';					/* yes, trim it */
	    x--;					/* skip past it */
	}
	else if (x - s >= 4 &&
		 !strncasecmp(x-4, "(fwd)", 5)) {	/* "(fwd)"? */
	    *(x-4) = '\0';				/* yes, trim it */
	    x -= 5;					/* skip past it */
	    *is_refwd += 1;				/* inc refwd counter */
	}
	else
	    break;					/* we're done */
    }

    /* trim leader
     *
     * start at the head of the string and work towards the end,
     * skipping over stuff we don't care about.
     */
    for (base = s; base;) {
	if (Uisspace(*base)) base++;			/* whitespace? */

	/* possible refwd */
	else if ((!strncasecmp(base, "re", 2) &&	/* "re"? */
		  (x = base + 2)) ||			/* yes, skip past it */
		 (!strncasecmp(base, "fwd", 3) &&	/* "fwd"? */
		  (x = base + 3)) ||			/* yes, skip past it */
		 (!strncasecmp(base, "fw", 2) &&	/* "fw"? */
		  (x = base + 2))) {			/* yes, skip past it */
	    int count = 0;				/* init counter */
	    
	    while (Uisspace(*x)) x++;			/* skip whitespace */

	    if (*x == '[') {				/* start of blob? */
		for (x++; x;) {				/* yes, get count */
		    if (!*x) {				/* end of subj, quit */
			x = NULL;
			break;
		    }
		    else if (*x == ']') {		/* end of blob, done */
			break;
					/* if we have a digit, and we're still
					   counting, keep building the count */
		    } else if (cyrus_isdigit((int) *x) && count != -1) {
			count = count * 10 + *x - '0';
			if (count < 0) {                /* overflow */
			    count = -1; /* abort counting */
			}
		    } else {				/* no digit, */
			count = -1;			/*  abort counting */
		    }
		    x++;
		}

		if (x)					/* end of blob? */
		    x++;				/* yes, skip past it */
		else
		    break;				/* no, we're done */
	    }

	    while (Uisspace(*x)) x++;                   /* skip whitespace */

	    if (*x == ':') {				/* ending colon? */
		base = x + 1;				/* yes, skip past it */
		*is_refwd += (count > 0 ? count : 1);	/* inc refwd counter
							   by count or 1 */
	    }
	    else
		break;					/* no, we're done */
	}

#if 0 /* do nested blobs - wait for decision on this */
	else if (*base == '[') {			/* start of blob? */
	    int count = 1;				/* yes, */
	    x = base + 1;				/*  find end of blob */
	    while (count) {				/* find matching ']' */
		if (!*x) {				/* end of subj, quit */
		    x = NULL;
		    break;
		}
		else if (*x == '[')			/* new open */
		    count++;				/* inc counter */
		else if (*x == ']')			/* close */
		    count--;				/* dec counter */
		x++;
	    }

	    if (!x)					/* blob didn't close */
		break;					/*  so quit */

	    else if (*x)				/* end of subj? */
		base = x;				/* no, skip blob */
#else
	else if (*base == '[' &&			/* start of blob? */
		 (x = strpbrk(base+1, "[]")) &&		/* yes, end of blob */
		 *x == ']') {				/*  (w/o nesting)? */

	    if (*(x+1))					/* yes, end of subj? */
		base = x + 1;				/* no, skip blob */
#endif
	    else
		break;					/* yes, return blob */
	}
	else
	    break;					/* we're done */
    }

    return base;
}

/* Get message-id, and references/in-reply-to */

void index_get_ids(MsgData *msgdata, char *envtokens[], const char *headers,
		   unsigned size)
{
    static struct buf buf;
    strarray_t refhdr = STRARRAY_INITIALIZER;
    char *refstr, *ref, *in_reply_to;

    buf_reset(&buf);

    /* get msgid */
    msgdata->msgid = find_msgid(envtokens[ENV_MSGID], NULL);
     /* if we don't have one, create one */
    if (!msgdata->msgid) {
	buf_printf(&buf, "<Empty-ID: %u>", msgdata->msgno);
	msgdata->msgid = xstrdup(buf.s);
	buf_reset(&buf);
    }

    /* Copy headers to the buffer */
    buf_appendmap(&buf, headers, size);
    buf_cstring(&buf);

    /* grab the References header */
    strarray_append(&refhdr, "references");
    message_pruneheader(buf.s, &refhdr, 0);
    strarray_fini(&refhdr);

    if (buf.s) {
	/* allocate some space for refs */
	/* find references */
	refstr = buf.s;
	massage_header(refstr);
	while ((ref = find_msgid(refstr, &refstr)) != NULL)
	    strarray_appendm(&msgdata->ref, ref);
    }

    /* if we have no references, try in-reply-to */
    if (!msgdata->ref.count) {
	/* get in-reply-to id */
	in_reply_to = find_msgid(envtokens[ENV_INREPLYTO], NULL);
	/* if we have an in-reply-to id, make it the ref */
	if (in_reply_to)
	    strarray_append(&msgdata->ref, in_reply_to);
    }
}

/*
 * Function for comparing two integers.
 */
static int numcmp(modseq_t n1, modseq_t n2)
{
    return ((n1 < n2) ? -1 : (n1 > n2) ? 1 : 0);
}

/*
 * Comparison function for sorting message lists.
 */
static int index_sort_compare(MsgData *md1, MsgData *md2,
			      struct sortcrit *sortcrit)
{
    int reverse, ret = 0, i = 0, ann = 0;

    do {
	/* determine sort order from reverse flag bit */
	reverse = sortcrit[i].flags & SORT_REVERSE;

	switch (sortcrit[i].key) {
	case SORT_SEQUENCE:
	    ret = numcmp(md1->msgno, md2->msgno);
	    break;
	case SORT_ARRIVAL:
	    ret = numcmp(md1->internaldate, md2->internaldate);
	    break;
	case SORT_CC:
	    ret = strcmpsafe(md1->cc, md2->cc);
	    break;
	case SORT_DATE: {
	    time_t d1 = md1->date ? md1->date : md1->internaldate;
	    time_t d2 = md2->date ? md2->date : md2->internaldate;
	    ret = numcmp(d1, d2);
	    break;
	}
	case SORT_FROM:
	    ret = strcmpsafe(md1->from, md2->from);
	    break;
	case SORT_SIZE:
	    ret = numcmp(md1->size, md2->size);
	    break;
	case SORT_SUBJECT:
	    ret = strcmpsafe(md1->xsubj, md2->xsubj);
	    break;
	case SORT_TO:
	    ret = strcmpsafe(md1->to, md2->to);
	    break;
	case SORT_ANNOTATION:
	    ret = strcmpsafe(md1->annot.data[ann], md2->annot.data[ann]);
	    ann++;
	    break;
	case SORT_MODSEQ:
	    ret = numcmp(md1->modseq, md2->modseq);
	    break;
	case SORT_DISPLAYFROM:
	    ret = strcmpsafe(md1->displayfrom, md2->displayfrom);
	    break;
	case SORT_DISPLAYTO:
	    ret = strcmpsafe(md1->displayto, md2->displayto);
	    break;
	case SORT_UID:
	    ret = numcmp(md1->uid, md2->uid);
	    break;
	case SORT_CONVMODSEQ:
	    ret = numcmp(md1->convmodseq, md2->convmodseq);
	    break;
	case SORT_CONVEXISTS:
	    ret = numcmp(md1->convexists, md2->convexists);
	    break;
	case SORT_HASFLAG:
	    if (i < 31)
		ret = numcmp(md1->hasflag & (1<<i),
			     md2->hasflag & (1<<i));
	    break;
	case SORT_HASCONVFLAG:
	    if (i < 31)
		ret = numcmp(md1->hasconvflag & (1<<i),
			     md2->hasconvflag & (1<<i));
	    break;
	}
    } while (!ret && sortcrit[i++].key != SORT_SEQUENCE);

    return (reverse ? -ret : ret);
}

static int index_sort_compare_qsort(const void *v1, const void *v2)
{
    MsgData *md1 = *(MsgData **)v1;
    MsgData *md2 = *(MsgData **)v2;

    return index_sort_compare(md1, md2, the_sortcrit);
}

/*
 * Free an array of MsgData* as built by index_msgdata_load()
 */
static void index_msgdata_free(MsgData **msgdata, unsigned int n)
{
    unsigned int i;

    for (i = 0 ; i < n ; i++) {
	MsgData *md = msgdata[i];

	free(md->cc);
	free(md->from);
	free(md->to);
	free(md->displayfrom);
	free(md->displayto);
	free(md->xsubj);
	free(md->msgid);
	strarray_fini(&md->ref);
	strarray_fini(&md->annot);
    }
    free(msgdata);
}

/*
 * Getnext function for sorting thread lists.
 */
static void *index_thread_getnext(Thread *thread)
{
    return thread->next;
}

/*
 * Setnext function for sorting thread lists.
 */
static void index_thread_setnext(Thread *thread, Thread *next)
{
    thread->next = next;
}

/*
 * Comparison function for sorting threads.
 */
static int index_thread_compare(Thread *t1, Thread *t2,
				struct sortcrit *call_data)
{
    MsgData *md1, *md2;

    /* if the container is empty, use the first child's container */
    md1 = t1->msgdata ? t1->msgdata : t1->child->msgdata;
    md2 = t2->msgdata ? t2->msgdata : t2->child->msgdata;
    return index_sort_compare(md1, md2, call_data);
}

/*
 * Sort a list of threads.
 */
static void index_thread_sort(Thread *root, struct sortcrit *sortcrit)
{
    Thread *child;

    /* sort the grandchildren */
    child = root->child;
    while (child) {
	/* if the child has children, sort them */
	if (child->child)
	    index_thread_sort(child, sortcrit);
	child = child->next;
    }

    /* sort the children */
    root->child = lsort(root->child,
			(void * (*)(void*)) index_thread_getnext,
			(void (*)(void*,void*)) index_thread_setnext,
			(int (*)(void*,void*,void*)) index_thread_compare,
			sortcrit);
}

/*
 * Thread a list of messages using the ORDEREDSUBJECT algorithm.
 */
static void index_thread_orderedsubj(struct index_state *state,
				     unsigned *msgno_list, unsigned int nmsg,
				     int usinguid)
{
    MsgData **msgdata;
    unsigned int mi;
    struct sortcrit sortcrit[] = {{ SORT_SUBJECT,  0, {{NULL, NULL}} },
				  { SORT_DATE,     0, {{NULL, NULL}} },
				  { SORT_SEQUENCE, 0, {{NULL, NULL}} }};
    unsigned psubj_hash = 0;
    char *psubj;
    Thread *head, *newnode, *cur, *parent, *last;

    /* Create/load the msgdata array */
    msgdata = index_msgdata_load(state, msgno_list, nmsg, sortcrit, 0, NULL);

    /* Sort messages by subject and date */
    the_sortcrit = sortcrit;
    qsort(msgdata, nmsg, sizeof(MsgData *), index_sort_compare_qsort);

    /* create an array of Thread to use as nodes of thread tree
     *
     * we will be building threads under a dummy head,
     * so we need (nmsg + 1) nodes
     */
    head = (Thread *) xzmalloc((nmsg + 1) * sizeof(Thread));

    newnode = head + 1;	/* set next newnode to the second
			   one in the array (skip the head) */
    parent = head;	/* parent is the head node */
    psubj = NULL;	/* no previous subject */
    cur = NULL;		/* no current thread */
    last = NULL;	/* no last child */

    for (mi = 0 ; mi < nmsg ; mi++) {
	MsgData *msg = msgdata[mi];
	newnode->msgdata = msg;

	/* if no previous subj, or
	   current subj = prev subj (subjs have same hash, and
	   the strings are equal), then add message to current thread */
	if (!psubj ||
	    (msg->xsubj_hash == psubj_hash &&
	     !strcmp(msg->xsubj, psubj))) {
	    /* if no children, create first child */
	    if (!parent->child) {
		last = parent->child = newnode;
		if (!cur)		/* first thread */
		    parent = cur = parent->child;
	    }
	    /* otherwise, add to siblings */
	    else {
		last->next = newnode;
		last = last->next;
	    }
	}
	/* otherwise, create a new thread */
	else {
	    cur->next = newnode;	/* create and start a new thread */
	    parent = cur = cur->next;	/* now work with the new thread */
	}

	psubj_hash = msg->xsubj_hash;
	psubj = msg->xsubj;
	newnode++;
    }

    /* Sort threads by date */
    index_thread_sort(head, sortcrit+1);

    /* Output the threaded messages */ 
    index_thread_print(state, head, usinguid);

    /* free the thread array */
    free(head);

    /* free the msgdata array */
    index_msgdata_free(msgdata, nmsg);
}

/*
 * Guts of thread printing.  Recurses over children when necessary.
 *
 * Frees contents of msgdata as a side effect.
 */
static void _index_thread_print(struct index_state *state,
				Thread *thread, int usinguid)
{
    Thread *child;

    /* for each thread... */
    while (thread) {
	/* start the thread */
	prot_printf(state->out, "(");

	/* if we have a message, print its identifier
	 * (do nothing for empty containers)
	 */
	if (thread->msgdata) {
	    prot_printf(state->out, "%u",
			usinguid ? thread->msgdata->uid :
			thread->msgdata->msgno);

	    /* if we have a child, print the parent-child separator */
	    if (thread->child) prot_printf(state->out, " ");
	}

	/* for each child, grandchild, etc... */
	child = thread->child;
	while (child) {
	    /* if the child has siblings, print new branch and break */
	    if (child->next) {
		_index_thread_print(state, child, usinguid);
		break;
	    }
	    /* otherwise print the only child */
	    else {
		prot_printf(state->out, "%u",
			    usinguid ? child->msgdata->uid :
			    child->msgdata->msgno);

		/* if we have a child, print the parent-child separator */
		if (child->child) prot_printf(state->out, " ");

		child = child->child;
	    }
	}

	/* end the thread */
	prot_printf(state->out, ")");

	thread = thread->next;
    }
}

/*
 * Print a list of threads.
 *
 * This is a wrapper around _index_thread_print() which simply prints the
 * start and end of the untagged thread response.
 */
static void index_thread_print(struct index_state *state,
			       Thread *thread, int usinguid)
{
    prot_printf(state->out, "* THREAD");

    if (thread) {
	prot_printf(state->out, " ");
	_index_thread_print(state, thread->child, usinguid);
    }
}

/*
 * Find threading algorithm for given arg.
 * Returns index into thread_algs[], or -1 if not found.
 */
int find_thread_algorithm(char *arg)
{
    int alg;

    ucase(arg);
    for (alg = 0; thread_algs[alg].alg_name; alg++) {
	if (!strcmp(arg, thread_algs[alg].alg_name))
	    return alg;
    }
    return -1;
}

/*
 * The following code is an interpretation of JWZ's description
 * and pseudo-code in http://www.jwz.org/doc/threading.html.
 *
 * It has been modified to match the THREAD=REFERENCES algorithm.
 */

/*
 * Determines if child is a descendent of parent.
 *
 * Returns 1 if yes, 0 otherwise.
 */
static int thread_is_descendent(Thread *parent, Thread *child)
{
    Thread *kid;

    /* self */
    if (parent == child)
	return 1;

    /* search each child's decendents */
    for (kid = parent->child; kid; kid = kid->next) {
	if (thread_is_descendent(kid, child))
	    return 1;
    }
    return 0;
}

/*
 * Links child into parent's children.
 */
static void thread_adopt_child(Thread *parent, Thread *child)
{
    child->parent = parent;
    child->next = parent->child;
    parent->child = child;
}

/*
 * Unlinks child from it's parent's children.
 */
static void thread_orphan_child(Thread *child)
{
    Thread *prev, *cur;

    /* sanity check -- make sure child is actually a child of parent */
    for (prev = NULL, cur = child->parent->child;
	 cur != child && cur != NULL; prev = cur, cur = cur->next);

    if (!cur) {
	/* uh oh!  couldn't find the child in it's parent's children
	 * we should probably return NO to thread command
	 */
	return;
    }

    /* unlink child */
    if (!prev)	/* first child */
	child->parent->child = child->next;
    else
	prev->next = child->next;
    child->parent = child->next = NULL;
}

/*
 * Link messages together using message-id and references.
 */
static void ref_link_messages(MsgData **msgdata, unsigned int nmsg,
			      Thread **newnode, struct hash_table *id_table)
{
    Thread *cur, *parent, *ref;
    unsigned int mi;
    int dup_count = 0;
    char buf[100];
    int i;

    /* for each message... */
    for (mi = 0 ; mi < nmsg ; mi++) {
	MsgData *msg = msgdata[mi];

	/* fill the containers with msgdata
	 *
	 * if we already have a container, use it
	 */
	if ((cur = (Thread *) hash_lookup(msg->msgid, id_table))) {
	    /* If this container is not empty, then we have a duplicate
	     * Message-ID.  Make this one unique so that we don't stomp
	     * on the old one.
	     */
	    if (cur->msgdata) {
		snprintf(buf, sizeof(buf), "-dup%d", dup_count++);
		msg->msgid =
		    (char *) xrealloc(msg->msgid,
				      strlen(msg->msgid) + strlen(buf) + 1);
		strcat(msg->msgid, buf);
		/* clear cur so that we create a new container */
		cur = NULL;
	    }
	    else
		cur->msgdata = msg;
	}

	/* otherwise, make and index a new container */
	if (!cur) {
	    cur = *newnode;
	    cur->msgdata = msg;
	    hash_insert(msg->msgid, cur, id_table);
	    (*newnode)++;
	}

	/* Step 1.A */
	for (i = 0, parent = NULL; i < msg->ref.count; i++) {
	    /* if we don't already have a container for the reference,
	     * make and index a new (empty) container
	     */
	    if (!(ref = (Thread *) hash_lookup(msg->ref.data[i], id_table))) {
		ref = *newnode;
		hash_insert(msg->ref.data[i], ref, id_table);
		(*newnode)++;
	    }

	    /* link the references together as parent-child iff:
	     * - we won't change existing links, AND
	     * - we won't create a loop
	     */
	    if (!ref->parent &&
		parent && !thread_is_descendent(ref, parent)) {
		thread_adopt_child(parent, ref);
	    }

	    parent = ref;
	}

	/* Step 1.B
	 *
	 * if we have a parent already, it is probably bogus (the result
	 * of a truncated references field), so unlink from it because
	 * we now have the actual parent
	 */
	if (cur->parent) thread_orphan_child(cur);

	/* make the last reference the parent of our message iff:
	 * - we won't create a loop
	 */
	if (parent && !thread_is_descendent(cur, parent))
	    thread_adopt_child(parent, cur);
    }
}

/*
 * Gather orphan messages under the root node.
 */
static void ref_gather_orphans(const char *key __attribute__((unused)),
			       void *data, void *rock)
{
    Thread *node = (Thread *)data;
    struct rootset *rootset = (struct rootset *)rock;

    /* we only care about nodes without parents */
    if (!node->parent) {
	if (node->next) {
	    /* uh oh!  a node without a parent should not have a sibling
	     * we should probably return NO to thread command
	     */
	    return;
	}

	/* add this node to root's children */
	node->next = rootset->root->child;
	rootset->root->child = node;
	rootset->nroot++;
    }
}

/*
 * Prune tree of empty containers.
 */
static void ref_prune_tree(Thread *parent)
{
    Thread *cur, *prev, *next, *child;

    for (prev = NULL, cur = parent->child, next = cur->next;
	 cur;
	 prev = cur, cur = next, next = (cur ? cur->next : NULL)) {

	/* if we have an empty container with no children, delete it */
	if (!cur->msgdata && !cur->child) {
	    if (!prev)	/* first child */
		parent->child = cur->next;
	    else
		prev->next = cur->next;

	    /* we just removed cur from our list,
	     * so we need to keep the same prev for the next pass
	     */
	    cur = prev;
	}

	/* if we have an empty container with children, AND
	 * we're not at the root OR we only have one child,
	 * then remove the container but promote its children to this level
	 * (splice them into the current child list)
	 */
	else if (!cur->msgdata && cur->child &&
		 (cur->parent || !cur->child->next)) {
	    /* move cur's children into cur's place (start the splice) */
	    if (!prev)	/* first child */
		parent->child = cur->child;
	    else
		prev->next = cur->child;

	    /* make cur's parent the new parent of cur's children
	     * (they're moving in with grandma!)
	     */
	    child = cur->child;
	    do {
		child->parent = cur->parent;
	    } while (child->next && (child = child->next));

	    /* make the cur's last child point to cur's next sibling
	     * (finish the splice)
	     */
	    child->next = cur->next;

	    /* we just replaced cur with it's children
	     * so make it's first child the next node to process
	     */
	    next = cur->child;

	    /* make cur childless and siblingless */
	    cur->child = cur->next = NULL;

	    /* we just removed cur from our list,
	     * so we need to keep the same prev for the next pass
	     */
	    cur = prev;
	}

	/* if we have a message with children, prune it's children */
	else if (cur->child)
	    ref_prune_tree(cur);
    }
}

/*
 * Sort the messages in the root set by date.
 */
static void ref_sort_root(Thread *root)
{
    Thread *cur;
    struct sortcrit sortcrit[] = {{ SORT_DATE,     0, {{NULL, NULL}} },
				  { SORT_SEQUENCE, 0, {{NULL, NULL}} }};

    cur = root->child;
    while (cur) {
	/* if the message is a dummy, sort its children */
	if (!cur->msgdata) {
	    cur->child = lsort(cur->child,
			       (void * (*)(void*)) index_thread_getnext,
			       (void (*)(void*,void*)) index_thread_setnext,
			       (int (*)(void*,void*,void*)) index_thread_compare,
			       sortcrit);
	}
	cur = cur->next;
    }

    /* sort the root set */
    root->child = lsort(root->child,
			(void * (*)(void*)) index_thread_getnext,
			(void (*)(void*,void*)) index_thread_setnext,
			(int (*)(void*,void*,void*)) index_thread_compare,
			sortcrit);
}

/*
 * Group threads with same subject.
 */
static void ref_group_subjects(Thread *root, unsigned nroot, Thread **newnode)
{
    Thread *cur, *old, *prev, *next, *child;
    struct hash_table subj_table;
    char *subj;

    /* Step 5.A: create a subj_table with one bucket for every possible
     * subject in the root set
     */
    construct_hash_table(&subj_table, nroot, 1);

    /* Step 5.B: populate the table with a container for each subject
     * at the root
     */
    for (cur = root->child; cur; cur = cur->next) {
	/* Step 5.B.i: find subject of the thread
	 *
	 * if the container is not empty, use it's subject
	 */
	if (cur->msgdata)
	    subj = cur->msgdata->xsubj;
	/* otherwise, use the subject of it's first child */
	else
	    subj = cur->child->msgdata->xsubj;

	/* Step 5.B.ii: if subject is empty, skip it */
	if (!strlen(subj)) continue;

	/* Step 5.B.iii: lookup this subject in the table */
	old = (Thread *) hash_lookup(subj, &subj_table);

	/* Step 5.B.iv: insert the current container into the table iff:
	 * - this subject is not in the table, OR
	 * - this container is empty AND the one in the table is not
	 *   (the empty one is more interesting as a root), OR
	 * - the container in the table is a re/fwd AND this one is not
	 *   (the non-re/fwd is the more interesting of the two)
	 */
	if (!old ||
	    (!cur->msgdata && old->msgdata) ||
	    (old->msgdata && old->msgdata->is_refwd &&
	     cur->msgdata && !cur->msgdata->is_refwd)) {
	  hash_insert(subj, cur, &subj_table);
	}
    }

    /* 5.C - group containers with the same subject together */
    for (prev = NULL, cur = root->child, next = cur->next;
	 cur;
	 prev = cur, cur = next, next = (next ? next->next : NULL)) {	
	/* Step 5.C.i: find subject of the thread
	 *
	 * if container is not empty, use it's subject
	 */
	if (cur->msgdata)
	    subj = cur->msgdata->xsubj;
	/* otherwise, use the subject of it's first child */
	else
	    subj = cur->child->msgdata->xsubj;

	/* Step 5.C.ii: if subject is empty, skip it */
	if (!strlen(subj)) continue;

	/* Step 5.C.iii: lookup this subject in the table */
	old = (Thread *) hash_lookup(subj, &subj_table);

	/* Step 5.C.iv: if we found ourselves, skip it */
	if (!old || old == cur) continue;

	/* ok, we already have a container which contains our current subject,
	 * so pull this container out of the root set, because we are going to
	 * merge this node with another one
	 */
	if (!prev)	/* we're at the root */
	    root->child = cur->next;
	else
	    prev->next = cur->next;
	cur->next = NULL;

	/* if both containers are dummies, append cur's children to old's */
	if (!old->msgdata && !cur->msgdata) {
	    /* find old's last child */
	    for (child = old->child; child->next; child = child->next);

	    /* append cur's children to old's children list */
	    child->next = cur->child;

	    /* make old the parent of cur's children */
	    for (child = cur->child; child; child = child->next)
		child->parent = old;

	    /* make cur childless */
	    cur->child = NULL;
	}

	/* if:
	 * - old container is empty, OR
	 * - the current message is a re/fwd AND the old one is not,
	 * make the current container a child of the old one
	 *
	 * Note: we don't have to worry about the reverse cases
	 * because step 5.B guarantees that they won't happen
	 */
	else if (!old->msgdata ||
		 (cur->msgdata && cur->msgdata->is_refwd &&
		  !old->msgdata->is_refwd)) {
	    thread_adopt_child(old, cur);
	}

	/* if both messages are re/fwds OR neither are re/fwds,
	 * then make them both children of a new dummy container
	 * (we don't want to assume any parent-child relationship between them)
	 *
	 * perhaps we can create a parent-child relationship
	 * between re/fwds by counting the number of re/fwds
	 *
	 * Note: we need the hash table to still point to old,
	 * so we must make old the dummy and make the contents of the
	 * new container a copy of old's original contents
	 */
	else {
	    Thread *new = (*newnode)++;

	    /* make new a copy of old (except parent and next) */
 	    new->msgdata = old->msgdata;
	    new->child = old->child;
	    new->next = NULL;

	    /* make new the parent of it's newly adopted children */
	    for (child = new->child; child; child = child->next)
		child->parent = new;

	    /* make old the parent of cur and new */
	    cur->parent = old;
	    new->parent = old;

	    /* empty old and make it have two children (cur and new) */
	    old->msgdata = NULL;
	    old->child = cur;
	    cur->next = new;
	}

	/* we just removed cur from our list,
	 * so we need to keep the same prev for the next pass
	 */
	cur = prev;
    }

    free_hash_table(&subj_table, NULL);
}

/*
 * Guts of thread searching.  Recurses over children when necessary.
 */
static int _index_thread_search(struct index_state *state,
				Thread *thread, int (*searchproc) (MsgData *))
{
    Thread *child;

    /* test the head node */
    if (thread->msgdata && searchproc(thread->msgdata)) return 1;

    /* test the children recursively */
    child = thread->child;
    while (child) {
	if (_index_thread_search(state, child, searchproc)) return 1;
	child = child->next;
    }

    /* if we get here, we struck out */
    return 0;
}

/*
 * Search a thread to see if it contains a message which matches searchproc().
 *
 * This is a wrapper around _index_thread_search() which iterates through
 * each thread and removes any which fail the searchproc().
 */
static void index_thread_search(struct index_state *state,
				Thread *root, int (*searchproc) (MsgData *))
{
    Thread *cur, *prev, *next;

    for (prev = NULL, cur = root->child, next = cur->next;
	 cur;
	 prev = cur, cur= next, next = (cur ? cur->next : NULL)) {
	if (!_index_thread_search(state, cur, searchproc)) {
	    /* unlink the thread from the list */
	    if (!prev)	/* first thread */
		root->child = cur->next;
	    else
		prev->next = cur->next;

	    /* we just removed cur from our list,
	     * so we need to keep the same prev for the next pass
	     */
	    cur = prev;
	}
    }
}

/*
 * Guts of the REFERENCES algorithms.  Behavior is tweaked with loadcrit[],
 * searchproc() and sortcrit[].
 */
static void _index_thread_ref(struct index_state *state, unsigned *msgno_list,
			      unsigned int nmsg,
			      struct sortcrit loadcrit[],
			      int (*searchproc) (MsgData *),
			      struct sortcrit sortcrit[], int usinguid)
{
    MsgData **msgdata;
    unsigned int mi;
    int tref, nnode;
    Thread *newnode;
    struct hash_table id_table;
    struct rootset rootset;

    /* Create/load the msgdata array */
    msgdata = index_msgdata_load(state, msgno_list, nmsg, loadcrit, 0, NULL);

    /* calculate the sum of the number of references for all messages */
    for (mi = 0, tref = 0 ; mi < nmsg ; mi++)
	tref += msgdata[mi]->ref.count;

    /* create an array of Thread to use as nodes of thread tree (including
     * empty containers)
     *
     * - We will be building threads under a dummy root, so we need at least
     *   (nmsg + 1) nodes.
     * - We also will need containers for references to non-existent messages.
     *   To make sure we have enough, we will take the worst case and
     *   use the sum of the number of references for all messages.
     * - Finally, we will need containers to group threads with the same
     *   subject together.  To make sure we have enough, we will take the
     *   worst case which will be half of the number of messages.
     *
     * This is overkill, but it is the only way to make sure we have enough
     * ahead of time.  If we tried to use xrealloc(), the array might be moved,
     * and our parent/child/next pointers will no longer be correct
     * (been there, done that).
     */
    nnode = (int) (1.5 * nmsg + 1 + tref);
    rootset.root = (Thread *) xmalloc(nnode * sizeof(Thread));
    memset(rootset.root, 0, nnode * sizeof(Thread));

    newnode = rootset.root + 1;	/* set next newnode to the second
				   one in the array (skip the root) */

    /* Step 0: create an id_table with one bucket for every possible
     * message-id and reference (nmsg + tref)
     */
    construct_hash_table(&id_table, nmsg + tref, 1);

    /* Step 1: link messages together */
    ref_link_messages(msgdata, nmsg, &newnode, &id_table);

    /* Step 2: find the root set (gather all of the orphan messages) */
    rootset.nroot = 0;
    hash_enumerate(&id_table, ref_gather_orphans, &rootset);

    /* discard id_table */
    free_hash_table(&id_table, NULL);

    /* Step 3: prune tree of empty containers - get our deposit back :^) */
    ref_prune_tree(rootset.root);

    /* Step 4: sort the root set */
    ref_sort_root(rootset.root);

    /* Step 5: group root set by subject */
    ref_group_subjects(rootset.root, rootset.nroot, &newnode);

    /* Optionally search threads (to be used by REFERENCES derivatives) */
    if (searchproc) index_thread_search(state, rootset.root, searchproc);

    /* Step 6: sort threads */
    if (sortcrit) index_thread_sort(rootset.root, sortcrit);

    /* Output the threaded messages */ 
    index_thread_print(state, rootset.root, usinguid);

    /* free the thread array */
    free(rootset.root);

    /* free the msgdata array */
    index_msgdata_free(msgdata, nmsg);
}

/*
 * Thread a list of messages using the REFERENCES algorithm.
 */
static void index_thread_ref(struct index_state *state,
			     unsigned *msgno_list, unsigned int nmsg,
			     int usinguid)
{
    struct sortcrit loadcrit[] = {{ LOAD_IDS,      0, {{NULL,NULL}} },
				  { SORT_SUBJECT,  0, {{NULL,NULL}} },
				  { SORT_DATE,     0, {{NULL,NULL}} },
				  { SORT_SEQUENCE, 0, {{NULL,NULL}} }};
    struct sortcrit sortcrit[] = {{ SORT_DATE,     0, {{NULL,NULL}} },
				  { SORT_SEQUENCE, 0, {{NULL,NULL}} }};

    _index_thread_ref(state, msgno_list, nmsg, loadcrit, NULL, sortcrit, usinguid);
}

/*
 * NNTP specific stuff.
 */
char *index_get_msgid(struct index_state *state,
		      uint32_t msgno)
{
    char *env;
    char *envtokens[NUMENVTOKENS];
    char *msgid;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    if (mailbox_cacherecord(mailbox, &im->record))
	return NULL;

    if (cacheitem_size(&im->record, CACHE_ENVELOPE) <= 2)
	return NULL;

    /* get msgid out of the envelope
     *
     * get a working copy; strip outer ()'s
     * +1 -> skip the leading paren
     * -2 -> don't include the size of the outer parens
     */
    env = xstrndup(cacheitem_base(&im->record, CACHE_ENVELOPE) + 1,
		   cacheitem_size(&im->record, CACHE_ENVELOPE) - 2);
    parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

    msgid = envtokens[ENV_MSGID] ? xstrdup(envtokens[ENV_MSGID]) : NULL;

    /* free stuff */
    free(env);

    return msgid;
}

static void massage_header(char *hdr)
{
    int n = 0;
    char *p, c;

    for (p = hdr; *p; p++) {
	if (*p == ' ' || *p == '\t' || *p == '\r') {
	    if (!n || *(p+1) == '\n') {
		/* no leading or trailing whitespace */
		continue;
	    }
	    /* replace with space */
	    c = ' ';
	}
	else if (*p == '\n') {
	    if (*(p+1) == ' ' || *(p+1) == '\t') {
		/* folded header */
		continue;
	    }
	    /* end of header */
	    break;
	}
	else
	    c = *p;

	hdr[n++] = c;
    }
    hdr[n] = '\0';
}

extern struct nntp_overview *index_overview(struct index_state *state,
					    uint32_t msgno)
{
    static struct nntp_overview over;
    static char *env = NULL, *from = NULL, *hdr = NULL;
    static int envsize = 0, fromsize = 0, hdrsize = 0;
    int size;
    char *envtokens[NUMENVTOKENS];
    struct address addr = { NULL, NULL, NULL, NULL, NULL, NULL };
    strarray_t refhdr = STRARRAY_INITIALIZER;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    /* flush any previous data */
    memset(&over, 0, sizeof(struct nntp_overview));

    if (mailbox_cacherecord(mailbox, &im->record))
	return NULL; /* upper layers can cope! */

    /* make a working copy of envelope; strip outer ()'s */
    /* -2 -> don't include the size of the outer parens */
    /* +1 -> leave space for NUL */
    size = cacheitem_size(&im->record, CACHE_ENVELOPE) - 2 + 1;
    if (envsize < size) {
	envsize = size;
	env = xrealloc(env, envsize);
    }
    /* +1 -> skip the leading paren */
    strlcpy(env, cacheitem_base(&im->record, CACHE_ENVELOPE) + 1, size);

    /* make a working copy of headers */
    size = cacheitem_size(&im->record, CACHE_HEADERS);
    if (hdrsize < size+2) {
	hdrsize = size+100;
	hdr = xrealloc(hdr, hdrsize);
    }
    memcpy(hdr, cacheitem_base(&im->record, CACHE_HEADERS), size);
    hdr[size] = '\0';

    parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

    over.uid = im->record.uid;
    over.bytes = im->record.size;
    over.lines = index_getlines(state, msgno);
    over.date = envtokens[ENV_DATE];
    over.msgid = envtokens[ENV_MSGID];

    /* massage subject */
    if ((over.subj = envtokens[ENV_SUBJECT]))
	massage_header(over.subj);

    /* build original From: header */
    if (envtokens[ENV_FROM]) /* paranoia */
	message_parse_env_address(envtokens[ENV_FROM], &addr);

    if (addr.mailbox && addr.domain) { /* paranoia */
	/* +3 -> add space for quotes and space */
	/* +4 -> add space for < @ > NUL */
	size = (addr.name ? strlen(addr.name) + 3 : 0) +
	    strlen(addr.mailbox) + strlen(addr.domain) + 4;
	if (fromsize < size) {
	    fromsize = size;
	    from = xrealloc(from, fromsize);
	}
	from[0] = '\0';
	if (addr.name) sprintf(from, "\"%s\" ", addr.name);
	snprintf(from + strlen(from), fromsize - strlen(from),
		 "<%s@%s>", addr.mailbox, addr.domain);

	over.from = from;
    }

    /* massage references */
    strarray_append(&refhdr, "references");
    message_pruneheader(hdr, &refhdr, 0);
    strarray_fini(&refhdr);

    if (*hdr) {
	over.ref = hdr + 11; /* skip over header name */
	massage_header(over.ref);
    }

    return &over;
}

extern char *index_getheader(struct index_state *state, uint32_t msgno,
			     char *hdr)
{
    static const char *msg_base = 0;
    static size_t msg_size = 0;
    strarray_t headers = STRARRAY_INITIALIZER;
    static char *alloc = NULL;
    static unsigned allocsize = 0;
    unsigned size;
    char *buf;
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im = &state->map[msgno-1];

    if (msg_base) {
	mailbox_unmap_message(NULL, 0, &msg_base, &msg_size);
	msg_base = 0;
	msg_size = 0;
    }

    /* see if the header is cached */
    if (mailbox_cached_header(hdr) != BIT32_MAX &&
        !mailbox_cacherecord(mailbox, &im->record)) {
    
	size = cacheitem_size(&im->record, CACHE_HEADERS);
	if (allocsize < size+2) {
	    allocsize = size+100;
	    alloc = xrealloc(alloc, allocsize);
	}

	memcpy(alloc, cacheitem_base(&im->record, CACHE_HEADERS), size);
	alloc[size] = '\0';

	buf = alloc;
    }
    else {
	/* uncached header */
	if (mailbox_map_message(mailbox, im->record.uid, &msg_base, &msg_size))
	    return NULL;

	buf = index_readheader(msg_base, msg_size, 0, im->record.header_size);
    }

    strarray_append(&headers, hdr);
    message_pruneheader(buf, &headers, NULL);
    strarray_fini(&headers);

    if (*buf) {
	buf += strlen(hdr) + 1; /* skip header: */
	massage_header(buf);
    }

    return buf;
}

extern unsigned long index_getsize(struct index_state *state,
				   uint32_t msgno)
{
    struct index_map *im = &state->map[msgno-1];
    return im->record.size;
}

extern unsigned long index_getlines(struct index_state *state, uint32_t msgno)
{
    struct index_map *im = &state->map[msgno-1];
    return im->record.content_lines;
}

/*
 * Parse a sequence into an array of sorted & merged ranges.
 */
static struct seqset *_parse_sequence(struct index_state *state,
				      const char *sequence, int usinguid)
{
    unsigned maxval = usinguid ? state->last_uid : state->exists;
    return seqset_parse(sequence, NULL, maxval);
}

void appendsequencelist(struct index_state *state,
			struct seqset **l,
			char *sequence, int usinguid)
{
    unsigned maxval = usinguid ? state->last_uid : state->exists;
    seqset_append(l, sequence, maxval);
}

void freesequencelist(struct seqset *l)
{
    seqset_free(l);
}
