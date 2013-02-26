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
#include "user.h"
#include "util.h"
#include "xstats.h"
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
// extern struct namespace imapd_namespace;

struct index_modified_flags {
    int added_flags;
    bit32 added_system_flags;
    bit32 added_user_flags[MAX_USER_FLAGS/32];
    int removed_flags;
    bit32 removed_system_flags;
    bit32 removed_user_flags[MAX_USER_FLAGS/32];
};

static int index_writeseen(struct index_state *state);
static void index_fetchmsg(struct index_state *state,
		    const struct buf *msg,
		    unsigned offset, unsigned size,
		    unsigned start_octet, unsigned octet_count);
static int index_fetchsection(struct index_state *state, const char *resp,
			      const struct buf *msg,
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
				 const struct searchargs *searchargs,
				 uint32_t msgno, struct buf *msgfile);
static int index_searchmsg(struct index_record *, const struct buf *msgfile,
			   const char *substr, comp_pat *pat, int skipheader);
static int index_searchheader(char *name, char *substr, comp_pat *pat,
			      struct buf *msgfile,
			      int size);
static int index_searchcacheheader(struct index_state *state, uint32_t msgno, char *name, char *substr,
				   comp_pat *pat);
static int _index_search(unsigned **msgno_list, struct index_state *state,
			 struct searchargs *searchargs,
			 modseq_t *highestmodseq);

static int index_copysetup(struct index_state *state, uint32_t msgno,
			   struct copyargs *copyargs, int is_same_user);
static int index_storeflag(struct index_state *state,
                           struct index_modified_flags *modified_flags,
                           uint32_t msgno, struct storeargs *storeargs);
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

static int index_reload_record(struct index_state *state,
			       uint32_t msgno,
			       struct index_record *recordp)
{
    struct index_map *im = &state->map[msgno-1];
    int r = 0;
    int i;

    if (!im->recno) {
	/* doh, gotta just fill in what we know */
	memset(recordp, 0, sizeof(struct index_record));
	recordp->uid = im->uid;
    }
    else {
	r = mailbox_read_index_record(state->mailbox, im->recno, recordp);
    }
    /* NOTE: we have released the cyrus.index lock at this point, but are
     * still holding the mailbox name relock.  This means nobody can rewrite
     * the file under us - so the offsets are still guaranteed to be correct,
     * and all the immutable fields are unchanged.  That said, we can get a
     * read of a partially updated record which contains an invalid checksum
     * due to incomplete concurrent changes to mutable fields.
     *
     * That's OK in just this case, because we're about to overwrite all the
     * parsed mutable fields with the clean values we cached back when we had
     * a cyrus.index lock and got a complete read. */
    if (r == IMAP_MAILBOX_CHECKSUM) r = 0;

    /* but other errors are still bad */
    if (r) return r;

    /* better be! */
    assert(recordp->uid == im->uid);

    /* restore mutable fields */
    recordp->modseq = im->modseq;
    recordp->system_flags = im->system_flags;
    for (i = 0; i < MAX_USER_FLAGS/32; i++)
	recordp->user_flags[i] = im->user_flags[i];

    return 0;
}

static int index_rewrite_record(struct index_state *state,
				uint32_t msgno,
				struct index_record *recordp)
{
    struct index_map *im = &state->map[msgno-1];
    int i;
    int r;

    assert(recordp->uid == im->uid);

    r = mailbox_rewrite_index_record(state->mailbox, recordp);
    if (r) return r;

    /* update tracking of mutable fields */
    im->modseq = recordp->modseq;
    im->system_flags = recordp->system_flags;
    for (i = 0; i < MAX_USER_FLAGS/32; i++)
	im->user_flags[i] = recordp->user_flags[i];

    return 0;
}

EXPORTED void index_release(struct index_state *state)
{
    if (!state) return;

    if (state->mailbox) {
	mailbox_close(&state->mailbox);
	state->mailbox = NULL; /* should be done by close anyway */
    }
}
static struct sortcrit *the_sortcrit;

/*
 * A mailbox is about to be closed.
 */
EXPORTED void index_close(struct index_state **stateptr)
{
    unsigned i;
    struct index_state *state = *stateptr;

    if (!state) return;

    index_release(state);

    free(state->map);
    free(state->mboxname);
    free(state->userid);
    for (i = 0; i < MAX_USER_FLAGS; i++)
	free(state->flagname[i]);
    free(state);

    *stateptr = NULL;
}

/*
 * A new mailbox has been selected, map it into memory and do the
 * initial CHECK.
 */
EXPORTED int index_open(const char *name, struct index_init *init,
	       struct index_state **stateptr)
{
    int r;
    struct index_state *state = xzmalloc(sizeof(struct index_state));

    if (init) {
	state->authstate = init->authstate;
	state->examining = init->examine_mode;
	state->mboxname = xstrdup(name);
	state->out = init->out;
	state->qresync = init->qresync;
	state->userid = xstrdupnull(init->userid);
	state->want_expunged = init->want_expunged;

	if (state->examining) {
	    r = mailbox_open_irl(state->mboxname, &state->mailbox);
	    if (r) goto fail;
	}
	else {
	    r = mailbox_open_iwl(state->mboxname, &state->mailbox);
	    if (r) goto fail;
	}
	state->myrights = cyrus_acl_myrights(init->authstate,
					     state->mailbox->acl);
	if (state->examining)
	    state->myrights &= ~ACL_READ_WRITE;

	state->internalseen = mailbox_internal_seen(state->mailbox,
						    state->userid);
	state->keepingseen = (state->myrights & ACL_SETSEEN);
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
    free(state->mboxname);
    free(state->userid);
    free(state);
    return r;
}

EXPORTED int index_expunge(struct index_state *state, char *sequence,
		  int need_deleted)
{
    int r;
    uint32_t msgno;
    struct index_map *im;
    struct seqset *seq = NULL;
    struct index_record record;
    int numexpunged = 0;
    struct mboxevent *mboxevent = NULL;

    r = index_lock(state);
    if (r) return r;

    /* XXX - earlier list if the sequence names UIDs that don't exist? */
    seq = _parse_sequence(state, sequence, 1);

    /* don't notify for messages that don't need \Deleted flag because
     * a notification should be already send (eg. MessageMove) */
    if (need_deleted)
	mboxevent = mboxevent_new(EVENT_MESSAGE_EXPUNGE);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];

	if (im->system_flags & FLAG_EXPUNGED)
	    continue; /* already expunged */

	if (need_deleted && !(im->system_flags & FLAG_DELETED))
	    continue; /* no \Deleted flag */

	/* if there is a sequence list, check it */
	if (sequence && !seqset_ismember(seq, im->uid))
	    continue; /* not in the list */

	/* load first once we know we have to process this one */
	if (index_reload_record(state, msgno, &record))
	    continue;

	if (!im->isseen) {
	    state->numunseen--;
	    im->isseen = 1;
	}

	if (im->isrecent) {
	    state->numrecent--;
	    im->isrecent = 0;
	}

	if (state->want_expunged)
	    state->num_expunged++;

	/* set the flags */
	record.system_flags |= FLAG_DELETED | FLAG_EXPUNGED;
	numexpunged++;

	r = index_rewrite_record(state, msgno, &record);
	if (r) break;

	mboxevent_extract_record(mboxevent, state->mailbox, &record);
    }

    seqset_free(seq);

    mboxevent_extract_mailbox(mboxevent, state->mailbox);
    mboxevent_set_numunseen(mboxevent, state->mailbox, state->numunseen);

    /* unlock before responding */
    index_unlock(state);

    if (!r && (numexpunged > 0)) {
	syslog(LOG_NOTICE, "Expunged %d messages from %s",
	       numexpunged, state->mboxname);
	/* send the MessageExpunge event notification for "immediate", "default"
	 * and "delayed" expunge */
	mboxevent_notify(mboxevent);
    }

    mboxevent_free(&mboxevent);

    return r;
}

static char *index_buildseen(struct index_state *state, const char *oldseenuids)
{
    struct seqset *outlist;
    uint32_t msgno;
    unsigned oldmax;
    struct index_map *im;
    char *out;

    outlist = seqset_init(0, SEQ_MERGE); 
    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	seqset_add(outlist, im->uid, im->isseen);
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

static int index_writeseen(struct index_state *state)
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
    struct index_record record;
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
    int i;

    /* need to start by having enough space for the entire index state
     * before telling of any expunges (which happens after this refresh
     * if the command allows it).  In the update case, where there's
     * already a map, we have to theoretically fit the number that existed
     * last time plus however many new records might be unEXPUNGEd on the
     * end */

    if (state->last_uid) {
	need_records = state->exists + (mailbox->i.last_uid - state->last_uid);
    }
    else if (state->want_expunged) {
	/* could need the lot! */
	need_records = mailbox->i.num_records;
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

    /* walk through all records */
    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	if (mailbox_read_index_record(mailbox, recno, &record))
	    continue; /* bogus read... should probably be fatal */

	/* skip over map records where the mailbox doesn't have any
	 * data at all for the record any more (this can only happen
	 * after a repack), otherwise there will still be a readable
	 * record, which is handled below */
	im = &state->map[msgno-1];
	while (msgno <= state->exists && im->uid < record.uid) {
	    /* NOTE: this same logic is repeated below for messages
	     * past the end of recno (repack removing the trailing
	     * records).  Make sure to keep them in sync */
	    if (!(im->system_flags & FLAG_EXPUNGED)) {
		/* we don't even know the modseq of when it was wiped,
		 * but we can be sure it's since the last given highestmodseq,
		 * so simulate the lowest possible value.  This is fine for
		 * our told_modseq logic, and doesn't have to be exact because
		 * QRESYNC/CONDSTORE clients will see deletedmodseq and fall
		 * back to the inefficient codepath anyway */
		im->modseq = state->highestmodseq + 1;
	    }
	    if (!delayed_modseq || im->modseq < delayed_modseq)
		delayed_modseq = im->modseq - 1;
	    im->recno = 0;
	    /* simulate expunged flag so we get an EXPUNGE response and
	     * tell about unlinked so we don't get IO errors trying to
	     * find the file */
	    im->system_flags |= FLAG_EXPUNGED | FLAG_UNLINKED;
	    im = &state->map[msgno++];
	}

	/* expunged record not in map, can skip immediately.  It's
	 * never been told to this connection, so it doesn't need to
	 * get its own msgno */
	if (!state->want_expunged
	    && (msgno > state->exists || record.uid < im->uid)
	    && (record.system_flags & FLAG_EXPUNGED))
	    continue;

	/* make sure our UID map is consistent */
	if (msgno <= state->exists) {
	    assert(im->uid == record.uid);
	}
	else {
	    im->uid = record.uid;
	}

	/* copy all mutable fields */
	im->recno = recno;
	im->modseq = record.modseq;
	im->system_flags = record.system_flags;
	for (i = 0; i < MAX_USER_FLAGS/32; i++)
	    im->user_flags[i] = record.user_flags[i];

	/* for expunged records, just track the modseq */
	if (!state->want_expunged && (im->system_flags & FLAG_EXPUNGED)) {
	    /* http://www.rfc-editor.org/errata_search.php?rfc=5162
	     * Errata ID: 1809 - if there are expunged records we
	     * aren't telling about, need to make the highestmodseq
	     * be one lower so the client can safely resync */
	    if (!delayed_modseq || im->modseq < delayed_modseq)
		delayed_modseq = im->modseq - 1;
	}
	else {
	    /* re-calculate seen flags */
	    if (state->internalseen)
		im->isseen = (im->system_flags & FLAG_SEEN) ? 1 : 0;
	    else
		im->isseen = seqset_ismember(seenlist, im->uid) ? 1 : 0;

	    if (msgno > state->exists) {
		/* don't auto-tell new records */
		im->told_modseq = im->modseq;
		if (im->uid > recentuid) {
		    /* mark recent if it's newly being added to the index and also
		     * greater than the recentuid - ensures only one session gets
		     * the \Recent flag for any one message */
		    im->isrecent = 1;
		    state->seen_dirty = 1;
		}
		else
		    im->isrecent = 0;
	    }

	    /* track select values */
	    if (!im->isseen) {
		numunseen++;
		if (!firstnotseen)
		    firstnotseen = msgno;
	    }
	    if (im->isrecent) {
		numrecent++;
	    }
	}

	msgno++;

	/* make sure we don't overflow the memory we mapped */
	if (msgno > state->mapsize) {
	    char buf[2048];
	    sprintf(buf, "Exists wrong %u %u %u %u", msgno,
		    state->mapsize, mailbox->i.exists, mailbox->i.num_records);
	    fatal(buf, EC_IOERR);
	}
    }

    /* may be trailing records which need to be considered for
     * delayed_modseq purposes, and to get the count right for
     * later expunge processing */
    im = &state->map[msgno-1];
    while (msgno <= state->exists) {
	/* this is the same logic as the block above in the main loop,
	 * see comments up there, and make sure the blocks are kept
	 * in sync! */
	if (!(im->system_flags & FLAG_EXPUNGED))
	    im->modseq = state->highestmodseq + 1;
	if (!delayed_modseq || im->modseq < delayed_modseq)
	    delayed_modseq = im->modseq - 1;
	im->recno = 0;
	im->system_flags |= FLAG_EXPUNGED | FLAG_UNLINKED;
	im = &state->map[msgno++];
    }

    seqset_free(seenlist);

    /* update the header tracking data */
    state->oldexists = state->exists; /* we last knew about this many */
    state->exists = msgno - 1; /* we actually got this many */
    state->delayed_modseq = delayed_modseq;
    state->highestmodseq = mailbox->i.highestmodseq;
    state->generation = mailbox->i.generation_no;
    state->uidvalidity = mailbox->i.uidvalidity;
    state->last_uid = mailbox->i.last_uid;
    state->num_records = mailbox->i.num_records;
    state->firstnotseen = firstnotseen;
    state->numunseen = numunseen;
    state->numrecent = numrecent;
}

EXPORTED modseq_t index_highestmodseq(struct index_state *state)
{
    if (state->delayed_modseq)
	return state->delayed_modseq;
    return state->highestmodseq;
}

EXPORTED void index_select(struct index_state *state, struct index_init *init)
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
	    if (sequence && !seqset_ismember(seq, im->uid))
		continue;
	    if (im->modseq <= init->vanished.modseq)
		continue;
	    index_printflags(state, msgno, 1, 0);
	}
	seqset_free(seq);
    }
}

/*
 * Check for and report updates
 */
EXPORTED int index_check(struct index_state *state, int usinguid, int printuid)
{
    int r;

    if (!state) return 0;

    r = index_lock(state);

    /* Check for deleted mailbox  */
    if (r == IMAP_MAILBOX_NONEXISTENT) {
	/* Mailbox has been (re)moved */
	if (config_getswitch(IMAPOPT_DISCONNECT_ON_VANISHED_MAILBOX)) {
	    syslog(LOG_WARNING,
		   "Mailbox %s has been (re)moved out from under client",
		   state->mboxname);
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

    index_tellchanges(state, usinguid, printuid, 0);

#if TOIMSP
    if (state->firstnotseen) {
	toimsp(state->mboxname, state->mailbox->i.uidvalidity, "SEENsnn", state->userid,
	       0, state->mailbox->i.recenttime, 0);
    }
    else {
	toimsp(state->mboxname, state->mailbox->i.uidvalidity, "SEENsnn", state->userid,
	       state->mailbox->last_uid, state->mailbox->i.recenttime, 0);
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
		if (state->map[msgno-1].uid != uid)
		    break;
		/* ok, they matched - so we can start at the recno and UID
		 * first past the match */
		prevuid = uid;
		recno = state->map[msgno-1].recno + 1;
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

static int _fetch_setseen(struct index_state *state,
			  struct mboxevent *mboxevent,
			  uint32_t msgno)
{
    struct index_map *im = &state->map[msgno-1];
    struct index_record record;
    int r;

    /* already seen */
    if (im->isseen)
	return 0;

    /* no rights to change it */
    if (!(state->myrights & ACL_SETSEEN))
	return 0;

    r = index_reload_record(state, msgno, &record);
    if (r) return r;

    /* track changes internally */
    state->numunseen--;
    state->seen_dirty = 1;
    im->isseen = 1;

    /* also store in the record if it's internal seen */
    if (state->internalseen)
	record.system_flags |= FLAG_SEEN;

    /* need to bump modseq anyway, so always rewrite it */
    r = index_rewrite_record(state, msgno, &record);
    if (r) return r;

    mboxevent_extract_record(mboxevent, state->mailbox, &record);

    /* RFC2060 says:
     * The \Seen flag is implicitly set; if this causes
     * the flags to change they SHOULD be included as part
     * of the FETCH responses.   This is handled later by
     * always including flags if the modseq has changed.
     */

    return 0;
}

/* seq can be NULL - means "ALL" */
EXPORTED void index_fetchresponses(struct index_state *state,
			  struct seqset *seq,
			  int usinguid,
			  const struct fetchargs *fetchargs,
			  int *fetchedsomething)
{
    uint32_t msgno, start, end;
    struct index_map *im;
    int fetched = 0;
    annotate_db_t *annot_db = NULL;

    /* Keep an open reference on the per-mailbox db to avoid
     * doing too many slow database opens during the fetch */
    if ((fetchargs->fetchitems & FETCH_ANNOTATION))
	annotate_getdb(state->mboxname, &annot_db);

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
	if (seq && !seqset_ismember(seq, usinguid ? im->uid : msgno))
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
EXPORTED int index_fetch(struct index_state *state,
		const char *sequence,
		int usinguid,
		const struct fetchargs *fetchargs,
		int *fetchedsomething)
{
    struct seqset *seq;
    struct seqset *vanishedlist = NULL;
    struct index_map *im;
    uint32_t msgno;
    int r;
    struct mboxevent *mboxevent = NULL;

    r = index_lock(state);
    if (r) return r;

    seq = _parse_sequence(state, sequence, usinguid);

    /* set the \Seen flag if necessary - while we still have the lock */
    if (fetchargs->fetchitems & FETCH_SETSEEN && !state->examining
	&& state->firstnotseen) {
	mboxevent = mboxevent_new(EVENT_MESSAGE_READ);
	for (msgno = state->firstnotseen; msgno <= state->exists; msgno++) {
	    im = &state->map[msgno-1];
	    if (!seqset_ismember(seq, usinguid ? im->uid : msgno))
		continue;
	    r = _fetch_setseen(state, mboxevent, msgno);
	    if (r) break;
	}

	mboxevent_extract_mailbox(mboxevent, state->mailbox);
	mboxevent_set_numunseen(mboxevent, state->mailbox,
				state->numunseen);
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

    /* send MessageRead event notification for successfully rewritten records */
    mboxevent_notify(mboxevent);
    mboxevent_free(&mboxevent);

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
EXPORTED int index_store(struct index_state *state, char *sequence,
			 struct storeargs *storeargs)
{
    struct mailbox *mailbox;
    int i, r = 0;
    uint32_t msgno;
    int userflag;
    struct seqset *seq;
    struct index_map *im;
    const strarray_t *flags = &storeargs->flags;
    struct mboxevent *mboxevents = NULL;
    struct mboxevent *flagsset = NULL, *flagsclear = NULL;
    struct index_modified_flags modified_flags;
    struct index_record record;

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

    mailbox = state->mailbox;

    seq = _parse_sequence(state, sequence, storeargs->usinguid);

    for (i = 0; i < flags->count ; i++) {
	r = mailbox_user_flag(mailbox, flags->data[i], &userflag, 1);
	if (r) goto out;
	storeargs->user_flags[userflag/32] |= 1<<(userflag&31);
    }

    storeargs->update_time = time((time_t *)0);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	if (!seqset_ismember(seq, storeargs->usinguid ? im->uid : msgno))
	    continue;

	/* if it's expunged already, skip it now */
	if ((im->system_flags & FLAG_EXPUNGED))
	    continue;

	/* if it's changed already, skip it now */
	if (im->modseq > storeargs->unchangedsince) {
	    if (!storeargs->modified) {
		uint32_t maxval = (storeargs->usinguid ?
				   state->last_uid : state->exists);
		storeargs->modified = seqset_init(maxval, SEQ_SPARSE);
	    }
	    seqset_add(storeargs->modified,
		       (storeargs->usinguid ? im->uid : msgno),
		       /*ismember*/1);
	    continue;
	}

	r = index_reload_record(state, msgno, &record);
	if (r) goto out;

	switch (storeargs->operation) {
	case STORE_ADD_FLAGS:
	case STORE_REMOVE_FLAGS:
	case STORE_REPLACE_FLAGS:
	    r = index_storeflag(state, &modified_flags, msgno, storeargs);
	    if (r)
		break;

	    if (modified_flags.added_flags) {
		if (flagsset == NULL)
		    flagsset = mboxevent_enqueue(EVENT_FLAGS_SET, &mboxevents);

		mboxevent_add_flags(flagsset, mailbox->flagname,
		                    modified_flags.added_system_flags,
		                    modified_flags.added_user_flags);
		mboxevent_extract_record(flagsset, mailbox, &record);
	    }
	    if (modified_flags.removed_flags) {
		if (flagsclear == NULL)
		    flagsclear = mboxevent_enqueue(EVENT_FLAGS_CLEAR, &mboxevents);

		mboxevent_add_flags(flagsclear, mailbox->flagname,
		                    modified_flags.removed_system_flags,
		                    modified_flags.removed_user_flags);
		mboxevent_extract_record(flagsclear, mailbox, &record);
	    }

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

    /* let mboxevent_notify split FlagsSet into MessageRead, MessageTrash
     * and FlagsSet events */
    mboxevent_extract_mailbox(flagsset, mailbox);
    mboxevent_set_numunseen(flagsset, mailbox, state->numunseen);
    mboxevent_extract_mailbox(flagsclear, mailbox);
    mboxevent_set_numunseen(flagsclear, mailbox, state->numunseen);

    mboxevent_notify(mboxevents);
    mboxevent_freequeue(&mboxevents);
out:
    if (storeargs->operation == STORE_ANNOTATION && r)
	annotate_state_abort(&mailbox->annot_state);
    seqset_free(seq);
    index_unlock(state);
    index_tellchanges(state, storeargs->usinguid, storeargs->usinguid,
		      (storeargs->unchangedsince != ~0ULL));

    return r;
}

/*
 * Warm up a file, by beginning background readahead.  @offset and
 * @length define a subset of the file to be warmed; @length = 0 means
 * to the end of the file.  Returns a UNIX errno or 0 on success.  No
 * error is reported if the file is missing or the kernel doesn't have
 * the magic system call.
 *
 * Returns zero on success or an error code (system error code).
 */
static int warmup_file(const char *filename,
		       off_t offset, off_t length)
{
    int fd;
    int r;

    fd = open(filename, O_RDONLY, 0);
    if (fd < 0) return errno;

    /* Note, posix_fadvise() returns it's error code rather than
     * setting errno.  Unlike every other system call including
     * others defined in the same standard by the same committee. */
    r = posix_fadvise(fd, offset, length, POSIX_FADV_WILLNEED);

    /* posix_fadvise(WILLNEED) on Linux will return an EINVAL error
     * if the file is on tmpfs, even though this effectively means
     * the file's bytes are all already available in RAM.  Duh. */
    if (r == EINVAL) r = 0;

    close(fd);
    return r;
}

static void prefetch_messages(struct index_state *state,
			      struct seqset *seq,
			      int usinguid)
{
    struct mailbox *mailbox = state->mailbox;
    struct index_map *im;
    uint32_t msgno;
    char *fname;

    syslog(LOG_ERR, "Prefetching initial parts of messages\n");

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	if (!seqset_ismember(seq, usinguid ? im->uid : msgno))
	    continue;

	fname = mailbox_message_fname(mailbox, im->uid);
	if (!fname)
	    continue;

	warmup_file(fname, 0, 16384);
    }
}


/*
 * Perform the XRUNANNOTATOR command which runs the
 * annotator callout for each message in the given sequence.
 */
EXPORTED int index_run_annotator(struct index_state *state,
			const char *sequence, int usinguid,
			struct namespace *namespace, int isadmin)
{
    struct index_record record;
    struct seqset *seq = NULL;
    struct index_map *im;
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

    r = append_setup_mbox(&as, state->mailbox,
			  state->userid, state->authstate,
			  0, NULL, namespace, isadmin, 0);
    if (r) goto out;

    seq = _parse_sequence(state, sequence, usinguid);
    if (!seq) goto out;

    prefetch_messages(state, seq, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	if (!seqset_ismember(seq, usinguid ? im->uid : msgno))
	    continue;

	/* if it's expunged already, skip it now */
	if ((im->system_flags & FLAG_EXPUNGED))
	    continue;

	r = index_reload_record(state, msgno, &record);
	if (r) goto out;

	r = append_run_annotator(&as, &record);
	if (r) goto out;

	r = index_rewrite_record(state, msgno, &record);
	if (r) goto out;
    }

out:
    seqset_free(seq);

    if (!r) {
	r = append_commit(&as);
    }
    else {
	append_abort(&as);
    }
    index_unlock(state);

    index_tellchanges(state, usinguid, usinguid, 1);

    return r;
}

EXPORTED int index_warmup(struct mboxlist_entry *mbentry, unsigned int warmup_flags)
{
    const char *fname = NULL;
    char *tofree1 = NULL;
    char *tofree2 = NULL;
    int r = 0;

    if (warmup_flags & WARMUP_INDEX) {
	fname = mboxname_metapath(mbentry->partition, mbentry->name, META_INDEX, 0);
	r = warmup_file(fname, 0, 0);
	if (r) goto out;
    }
    if (warmup_flags & WARMUP_CONVERSATIONS) {
	if (config_getswitch(IMAPOPT_CONVERSATIONS)) {
	    fname = tofree1 = conversations_getmboxpath(mbentry->name);
	    r = warmup_file(fname, 0, 0);
	    if (r) goto out;
	}
    }
    if (warmup_flags & WARMUP_ANNOTATIONS) {
	fname = mboxname_metapath(mbentry->partition, mbentry->name, META_ANNOTATIONS, 0);
	r = warmup_file(fname, 0, 0);
	if (r) goto out;
    }
    if (warmup_flags & WARMUP_FOLDERSTATUS) {
	if (config_getswitch(IMAPOPT_STATUSCACHE)) {
	    fname = tofree2 = statuscache_filename();
	    r = warmup_file(fname, 0, 0);
	    if (r) goto out;
	}
    }

out:
    if (r == ENOENT || r == ENOSYS)
	r = 0;
    if (r)
	syslog(LOG_ERR, "IOERROR: unable to warmup file %s: %s",
		fname, error_message(r));
    free(tofree1);
    free(tofree2);
    return r;
}

static void build_query_part(search_builder_t *bx,
			     struct strlist **slp,
			     int part, int remove,
			     int *nmatchesp)
{
    struct strlist *s;

    for (s = (*slp) ; s ; s = s->next) {
	bx->match(bx, part, s->s);
	(*nmatchesp)++;
    }

    if (remove) {
	freestrlist(*slp);
	*slp = NULL;
    }
}

static void build_query(search_builder_t *bx,
			struct searchargs *searchargs,
			int remove,
			int *nmatchesp)
{
    struct searchsub* sub;

    bx->begin_boolean(bx, SEARCH_OP_AND);

    build_query_part(bx, &searchargs->from, SEARCH_PART_FROM, remove, nmatchesp);
    build_query_part(bx, &searchargs->to, SEARCH_PART_TO, remove, nmatchesp);
    build_query_part(bx, &searchargs->cc, SEARCH_PART_CC, remove, nmatchesp);
    build_query_part(bx, &searchargs->bcc, SEARCH_PART_BCC, remove, nmatchesp);
    build_query_part(bx, &searchargs->subject, SEARCH_PART_SUBJECT, remove, nmatchesp);
    /* Note - we cannot remove when searching headers, as we need
     * to match both the header field name and value, which always
     * requires a post filter pass */
    build_query_part(bx, &searchargs->header_name, SEARCH_PART_HEADERS, 0, nmatchesp);
    build_query_part(bx, &searchargs->header, SEARCH_PART_HEADERS, 0, nmatchesp);
    build_query_part(bx, &searchargs->body, SEARCH_PART_BODY, remove, nmatchesp);
    build_query_part(bx, &searchargs->text, SEARCH_PART_ANY, remove, nmatchesp);

    for (sub = searchargs->sublist ; sub ; sub = sub->next) {
	assert(!remove);
	if (sub->sub2 == NULL) {
	    /* do nothing; because our search is conservative (may include false
	       positives) we can't compute the NOT (since the result might include
	       false negatives, which we do not allow) */
	    /* Note that it's OK to do nothing. We'll just be returning more
	       false positives. */
	} else {
	    bx->begin_boolean(bx, SEARCH_OP_OR);
	    build_query(bx, sub->sub1, remove, nmatchesp);
	    build_query(bx, sub->sub2, remove, nmatchesp);
	    bx->end_boolean(bx, SEARCH_OP_OR);
	}
    }

    bx->end_boolean(bx, SEARCH_OP_AND);
}

static int index_prefilter_messages(unsigned* msg_list,
				    struct index_state *state,
				    struct searchargs *searchargs __attribute((unused)))
{
    unsigned int msgno;

    xstats_inc(SEARCH_TRIVIAL);

    /* Just put in all possible messages. This falls back to Cyrus' default
     * search. */

    for (msgno = 1; msgno <= state->exists; msgno++)
	msg_list[msgno-1] = msgno;

    return state->exists;
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
EXPORTED int index_scan(struct index_state *state, const char *contents)
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

    listcount = index_prefilter_messages(msgno_list, state, &searchargs);

    for (listindex = 0; !n && listindex < listcount; listindex++) {
	struct buf msgfile = BUF_INITIALIZER;
	msgno = msgno_list[listindex];
	im = &state->map[msgno-1];

	if (mailbox_map_message(mailbox, im->uid, &msgfile))
	    continue;

	n += index_scan_work(msgfile.s, msgfile.len, contents, length);

	buf_free(&msgfile);
    }

    free(strlist.s);
    free(strlist.p);
    free(msgno_list);

    return n;
}

EXPORTED message_t *index_get_message(struct index_state *state, uint32_t msgno)
{
    struct index_map *im = &state->map[msgno-1];
    uint32_t indexflags = 0;
    if (im->isseen) indexflags |= MESSAGE_SEEN;
    if (im->isrecent) indexflags |= MESSAGE_RECENT;
    return message_new_from_index(state->mailbox, &record,
				  msgno, indexflags);
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
    listcount = index_prefilter_messages(*msgno_list, state, searchargs);

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
	if (!state->want_expunged && (im->system_flags & FLAG_EXPUNGED))
	    continue;

	if (index_search_evaluate(state, searchargs, msgno, NULL)) {
	    (*msgno_list)[n++] = msgno;
	    if (highestmodseq && im->modseq > *highestmodseq) {
		*highestmodseq = im->modseq;
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
		    *highestmodseq = im->modseq;
	    }
	}
    }

    /* Reverse search.  Stops at previously found MIN (if any) */
    for (listindex = listcount; listindex > min; listindex--) {
	msgno = (*msgno_list)[listindex-1];
	im = &state->map[msgno-1];

	/* expunged messages hardly ever match */
	if (!state->want_expunged && (im->system_flags & FLAG_EXPUNGED))
	    continue;

	if (index_search_evaluate(state, searchargs, msgno, NULL)) {
	    (*msgno_list)[n++] = msgno;
	    if (highestmodseq && im->modseq > *highestmodseq) {
		*highestmodseq = im->modseq;
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

EXPORTED uint32_t index_getuid(struct index_state *state, uint32_t msgno)
{
    assert(msgno <= state->exists);
    return state->map[msgno-1].uid;
}

/* 'uid_list' is malloc'd string representing the hits from searchargs;
   returns number of hits */
EXPORTED int index_getuidsequence(struct index_state *state,
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
    int r;

    if (state->mailbox) {
	if (state->examining) {
	    r = mailbox_lock_index(state->mailbox, LOCK_SHARED);
	    if (r) return r;
	}
	else {
	    r = mailbox_lock_index(state->mailbox, LOCK_EXCLUSIVE);
	    if (r) return r;
	}
    }
    else {
	if (state->examining) {
	    r = mailbox_open_irl(state->mboxname, &state->mailbox);
	    if (r) return r;
	}
	else {
	    r = mailbox_open_iwl(state->mboxname, &state->mailbox);
	    if (r) return r;
	}
    }

    /* if the UIDVALIDITY has changed, treat as a delete */
    if (state->mailbox->i.uidvalidity != state->uidvalidity) {
	mailbox_close(&state->mailbox);
	return IMAP_MAILBOX_NONEXISTENT;
    }

    /* if highestmodseq has changed or file is repacked, read updates */
    if (state->highestmodseq != state->mailbox->i.highestmodseq
	|| state->generation != state->mailbox->i.generation_no)
	index_refresh(state);

    return 0;
}

EXPORTED int index_status(struct index_state *state, struct statusdata *sdata)
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

    mailbox_unlock_index(state->mailbox, NULL);
}

/*
 * Performs a SEARCH command.
 * This is a wrapper around _index_search() which simply prints the results.
 */
EXPORTED int index_search(struct index_state *state, struct searchargs *searchargs,
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
	    list[i] = state->map[list[i]-1].uid;

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
EXPORTED int index_sort(struct index_state *state, struct sortcrit *sortcrit,
	       struct searchargs *searchargs, int usinguid)
{
    unsigned *msgno_list = NULL;
    MsgData **msgdata = NULL;
    int mi;
    int nmsg = 0;
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
	    unsigned no = usinguid ? state->map[msg->msgno-1].uid
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
	    case SORT_CONVSIZE:
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
	return (conversations ?
		    convexists :
		    state->exists - state->num_expunged);
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
EXPORTED int index_convsort(struct index_state *state,
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

    /* Check the client didn't specify MULTIANCHOR. */
    if (windowargs->anchor && windowargs->anchorfolder)
	return IMAP_PROTOCOL_BAD_PARAMETERS;


    /* make sure \Deleted messages are expunged.  Will also lock the
     * mailbox state and read any new information */
    r = index_expunge(state, NULL, 1);
    if (r) return r;

    if (windowargs->conversations) {
	cstate = conversations_get_mbox(state->mailbox->name);
	if (!cstate)
	    return IMAP_INTERNAL;
    }

    total = search_predict_total(state, cstate, searchargs,
				windowargs->conversations,
				&xconvmodseq);
    if (!total)
	goto out;

    construct_hashu64_table(&seen_cids, state->exists/4+4, 0);

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

	/* can happen if we didn't "tellchanges" yet */
	if (record->system_flags & FLAG_EXPUNGED)
	    continue;

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

static int add_search_folder(void *rock,
			     const char *key,
			     size_t keylen,
			     const char *val __attribute((unused)),
			     size_t vallen __attribute((unused)))
{
    ptrarray_t *folders = (ptrarray_t *)rock;
    SearchFolder *sf = xzmalloc(sizeof(SearchFolder));

    sf->mboxname = xstrndup(key, keylen);
    sf->id = -1; /* unassigned */
    ptrarray_append(folders, sf);

    return 0;
}

struct multisort_item {
    modseq_t cid;
    int32_t folderid; /* can be -1 */
    uint32_t uid;
};

struct multisort_folder {
    char *name;
    uint32_t uidvalidity;
};

struct multisort_result {
    struct multisort_folder *folders;
    struct multisort_item *msgs;
    uint32_t nfolders;
    uint32_t nmsgs;
};

static struct db *sortcache_db(const char *userid, int create)
{
    char *fname = user_hash_meta(userid, "sortcache");
    int flags = create ? CYRUSDB_CREATE : 0;
    struct db *db = NULL;
    int r = cyrusdb_open("twoskip", fname, flags, &db);

    free(fname);

    return r ? NULL : db;
}

struct sortcache_cleanup_rock {
    struct db *db;
    const char *prefix;
    size_t prefixlen;
};

static int sortcache_cleanup_cb(void *rock,
				const char *key,
				size_t keylen,
				const char *val __attribute__((unused)),
				size_t vallen __attribute__((unused)))
{
    struct sortcache_cleanup_rock *scr = (struct sortcache_cleanup_rock *)rock;

    if (keylen < scr->prefixlen || memcmp(key, scr->prefix, scr->prefixlen)) {
	/* doesn't match the prefix, remove it */
	cyrusdb_delete(scr->db, key, keylen, NULL, /*force*/1);
    }

    return 0;
}

static int folder_may_be_in_search(const char *mboxname,
				   struct searchargs *searchargs)
{
    struct searchsub *s;
    struct strlist *l;

    for (l = searchargs->folder; l; l = l->next) {
	if (strcmpsafe(l->s, mboxname)) return 0;
    }

    for (s = searchargs->sublist; s; s = s->next) {
	if (folder_may_be_in_search(mboxname, s->sub1)) {
	    if (!s->sub2) return 0;
	}
	else {
	    if (s->sub2 && !folder_may_be_in_search(mboxname, s->sub1))
		return 0;
	}
    }

    return 1;
}

static struct multisort_result *multisort_run(struct index_state *state,
					      struct sortcrit *sortcrit,
					      struct searchargs *searchargs)
{
    int fi;
    int mi;
    int nfolders = 0;
    ptrarray_t folders = PTRARRAY_INITIALIZER;
    ptrarray_t merged_msgdata = PTRARRAY_INITIALIZER;
    int r = 0;
    struct index_state *state2 = NULL;
    unsigned msgno;
    struct multisort_result *result = NULL;

    if (searchargs->folder) {
	struct strlist *l;
	for (l = searchargs->folder; l; l = l->next) {
	    syslog(LOG_NOTICE, "DOING %s", l->s);
	    add_search_folder(&folders, l->s, strlen(l->s), NULL, 0);
	}
    }
    else {
	r = mboxlist_allusermbox(mboxname_to_userid(state->mailbox->name),
				add_search_folder, &folders, /*+deleted*/0);
	if (r) return NULL;
    }

    for (fi = 0; fi < folders.count; fi++) {
	SearchFolder *sf = ptrarray_nth(&folders, fi);
	unsigned int *msgs;
	int count = 0;

	if (!folder_may_be_in_search(sf->mboxname, searchargs))
	    continue;

	if (state2 && state2 != state)
	    index_close(&state2);

	/* open an index_state */
	if (!strcmp(state->mailbox->name, sf->mboxname)) {
	    state2 = state;
	}
	else {
	    struct index_init init;

	    memset(&init, 0, sizeof(struct index_init));
	    init.userid = searchargs->userid;
	    init.authstate = searchargs->authstate;
	    init.out = state->out;

	    r = index_open(sf->mboxname, &init, &state2);
	    if (r) continue;

	    index_checkflags(state2, 0, 0);
	}

	/* make sure \Deleted messages are expunged.  Will also lock the
	 * mailbox state and read any new information */
	r = index_expunge(state2, NULL, 1);
	if (r) continue;

	if (!state2->exists) continue;

	msgs = xmalloc(state2->exists * sizeof(uint32_t));

	/* One pass through the folder's message list */
	for (msgno = 1 ; msgno <= state2->exists ; msgno++) {
	    struct index_record *record = &state2->map[msgno-1].record;

	    /* can happen if we didn't "tellchanges" yet */
	    if (record->system_flags & FLAG_EXPUNGED)
		continue;

	    /* run the search program */
	    if (!index_search_evaluate(state2, searchargs, msgno, NULL))
		continue;

	    msgs[count++] = msgno;
	}

	/* Delay assigning ids to folders until we can be
	 * certain that any results will be reported for
	 * the folder */
	if (count) {
	    sf->id = nfolders++;
	    sf->uidvalidity = state2->mailbox->i.uidvalidity;

	    /* Create/load the msgdata array. */
	    sf->msgdata = index_msgdata_load(state2, msgs, count,
					     sortcrit, 0, 0);
	    for (mi = 0; mi < count; mi++) {
		sf->msgdata[mi]->folder = sf;
		/* merged_msgdata is now "owner" of the pointer */
		ptrarray_append(&merged_msgdata, sf->msgdata[mi]);
	    }
	}

	free(msgs);
    }

    if (state2 && state2 != state)
	index_close(&state2);

    /* Sort the merged messages based on the given criteria */
    the_sortcrit = sortcrit;
    qsort(merged_msgdata.data, merged_msgdata.count,
	  sizeof(MsgData *), index_sort_compare_qsort);

    /* convert the result for caching */
    result = xzmalloc(sizeof(struct multisort_result));

    result->nmsgs = merged_msgdata.count;
    result->msgs = xmalloc(result->nmsgs * sizeof(struct multisort_item));
    for (mi = 0; mi < merged_msgdata.count; mi++) {
	MsgData *msg = ptrarray_nth(&merged_msgdata, mi);
	result->msgs[mi].folderid = msg->folder->id;
	result->msgs[mi].uid = msg->uid;
	result->msgs[mi].cid = msg->cid;
    }

    result->nfolders = nfolders;
    result->folders = xmalloc(result->nmsgs * sizeof(struct multisort_folder));
    for (fi = 0; fi < folders.count; fi++) {
	SearchFolder *sf = ptrarray_nth(&folders, fi);
	if (sf->id >= 0) {
	    result->folders[sf->id].name = xstrdup(sf->mboxname);
	    result->folders[sf->id].uidvalidity = sf->uidvalidity;
	}
	free(sf->mboxname);
	free(sf->msgdata);
	free(sf);
    }

    /* free all our temporary data */
    ptrarray_fini(&folders);
    ptrarray_fini(&merged_msgdata);

    return result;
}

static void index_format_search(struct dlist *parent,
				const struct searchargs *searchargs)
{
    struct dlist *sublist;
    struct strlist *l, *h;
    struct searchannot *sa;
    struct searchsub *s;
    struct seqset *seq;
    int i, have_one;

    if (searchargs->flags & SEARCH_RECENT_SET)
	dlist_setatom(parent, NULL, "RECENT");
    if (searchargs->flags & SEARCH_RECENT_UNSET)
	dlist_setatom(parent, NULL, "UNRECENT");
    if (searchargs->flags & SEARCH_SEEN_SET)
	dlist_setatom(parent, NULL, "SEEN");
    if (searchargs->flags & SEARCH_SEEN_UNSET)
	dlist_setatom(parent, NULL, "UNSEEN");

    if (searchargs->smaller) {
	dlist_setatom(parent, NULL, "SMALLER");
	dlist_setnum64(parent, NULL, searchargs->smaller);
    }
    if (searchargs->larger) {
	dlist_setatom(parent, NULL, "LARGER");
	dlist_setnum64(parent, NULL, searchargs->larger);
    }

    if (searchargs->after) {
	dlist_setatom(parent, NULL, "AFTER");
	dlist_setdate(parent, NULL, searchargs->after);
    }
    if (searchargs->before) {
	dlist_setatom(parent, NULL, "BEFORE");
	dlist_setdate(parent, NULL, searchargs->before);
    }
    if (searchargs->sentafter) {
	dlist_setatom(parent, NULL, "SENTAFTER");
	dlist_setdate(parent, NULL, searchargs->sentafter);
    }
    if (searchargs->sentbefore) {
	dlist_setatom(parent, NULL, "SENTBEFORE");
	dlist_setdate(parent, NULL, searchargs->sentbefore);
    }

    if (searchargs->modseq) {
	dlist_setatom(parent, NULL, "MODSEQ");
	dlist_setnum64(parent, NULL, searchargs->modseq);
    }

    if (searchargs->system_flags_set) {
	dlist_setatom(parent, NULL, "SYSTEM_FLAGS");
	dlist_setnum32(parent, NULL, searchargs->system_flags_set);
    }

    if (searchargs->system_flags_unset) {
	dlist_setatom(parent, NULL, "UNSYSTEM_FLAGS");
	dlist_setnum32(parent, NULL, searchargs->system_flags_unset);
    }

    have_one = 0;
    for (i = 0; i < (MAX_USER_FLAGS/32); i++)
	if (searchargs->user_flags_set[i]) have_one = 1;
    if (have_one) {
	dlist_setatom(parent, NULL, "USER_FLAGS");
	sublist = dlist_newkvlist(parent, NULL);
	for (i = 0; i < (MAX_USER_FLAGS/32); i++)
	    dlist_setnum32(sublist, NULL, searchargs->user_flags_set[i]);
    }

    have_one = 0;
    for (i = 0; i < (MAX_USER_FLAGS/32); i++)
	if (searchargs->user_flags_unset[i]) have_one = 1;
    if (have_one) {
	dlist_setatom(parent, NULL, "UNUSER_FLAGS");
	sublist = dlist_newkvlist(parent, NULL);
	for (i = 0; i < (MAX_USER_FLAGS/32); i++)
	    dlist_setnum32(sublist, NULL, searchargs->user_flags_unset[i]);
    }

    for (seq = searchargs->sequence; seq; seq = seq->nextseq) {
	char *str = seqset_cstring(seq);
	dlist_setatom(parent, NULL, str);
	free(str);
    }

    for (seq = searchargs->uidsequence; seq; seq = seq->nextseq) {
	char *str = seqset_cstring(seq);
	dlist_setatom(parent, NULL, "UID");
	dlist_setatom(parent, NULL, str);
	free(str);
    }

    for (l = searchargs->folder; l; l = l->next) {
	dlist_setatom(parent, NULL, "FOLDER");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->from; l; l = l->next) {
	dlist_setatom(parent, NULL, "FROM");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->to; l; l = l->next) {
	dlist_setatom(parent, NULL, "TO");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->cc; l; l = l->next) {
	dlist_setatom(parent, NULL, "CC");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->bcc; l; l = l->next) {
	dlist_setatom(parent, NULL, "BCC");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->subject; l; l = l->next) {
	dlist_setatom(parent, NULL, "SUBJECT");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->messageid; l; l = l->next) {
	dlist_setatom(parent, NULL, "MESSAGEID");
	dlist_setatom(parent, NULL, l->s);
    }

    for (sa = searchargs->annotations ; sa ; sa = sa->next) {
	dlist_setatom(parent, NULL, "ANNOTATION");
	sublist = dlist_newlist(parent, NULL);
	dlist_setatom(sublist, NULL, sa->entry);
	dlist_setatom(sublist, NULL, sa->attrib);
	dlist_setmap(sublist, NULL, sa->value.s, sa->value.len);
    }

    for (s = searchargs->sublist; s; s = s->next) {
	if (s->sub2) {
	    dlist_setatom(parent, NULL, "OR");
	    sublist = dlist_newlist(parent, NULL);
	    index_format_search(sublist, s->sub1);
	    sublist = dlist_newlist(parent, NULL);
	    index_format_search(sublist, s->sub2);
	}
	else {
	    dlist_setatom(parent, NULL, "NOT");
	    sublist = dlist_newlist(parent, NULL);
	    index_format_search(sublist, s->sub1);
	}
    }

    for (l = searchargs->body; l; l = l->next) {
	dlist_setatom(parent, NULL, "BODY");
	dlist_setatom(parent, NULL, l->s);
    }

    for (l = searchargs->text; l; l = l->next) {
	dlist_setatom(parent, NULL, "TEXT");
	dlist_setatom(parent, NULL, l->s);
    }

    h = searchargs->header_name;
    for (l = searchargs->header; l; (l = l->next), (h = h->next)) {
	dlist_setatom(parent, NULL, "HEADER");
	dlist_setatom(parent, NULL, h->s);
	dlist_setatom(parent, NULL, l->s);
    }

    if (searchargs->convmodseq) {
	dlist_setatom(parent, NULL, "CONVMODSEQ");
	dlist_setnum64(parent, NULL, searchargs->convmodseq);
    }

    if (searchargs->flags & SEARCH_CONVSEEN_SET)
	dlist_setatom(parent, NULL, "CONVSEEN");

    if (searchargs->flags & SEARCH_CONVSEEN_UNSET)
	dlist_setatom(parent, NULL, "UNCONVSEEN");

    for (l = searchargs->convflags; l; l = l->next) {
	dlist_setatom(parent, NULL, "CONVFLAG");
	dlist_setatom(parent, NULL, l->s);
    }
}

static void index_format_sort(struct dlist *parent,
			      struct sortcrit *sortcrit)
{
    int i = 0;

    do {
	/* determine sort order from reverse flag bit */
	if (sortcrit[i].flags & SORT_REVERSE)
	    dlist_setatom(parent, NULL, "REVERSE");

	switch (sortcrit[i].key) {
	case SORT_SEQUENCE:
	    /* nothing to say here unless it's the only thing */
	    if (!i) dlist_setatom(parent, NULL, "SEQUENCE");
	    break;
	case SORT_ARRIVAL:
	    dlist_setatom(parent, NULL, "ARRIVAL");
	    break;
	case SORT_CC:
	    dlist_setatom(parent, NULL, "CC");
	    break;
	case SORT_DATE:
	    dlist_setatom(parent, NULL, "DATE");
	    break;
	case SORT_FROM:
	    dlist_setatom(parent, NULL, "FROM");
	    break;
	case SORT_SIZE:
	    dlist_setatom(parent, NULL, "SIZE");
	    break;
	case SORT_SUBJECT:
	    dlist_setatom(parent, NULL, "SUBJECT");
	    break;
	case SORT_TO:
	    dlist_setatom(parent, NULL, "TO");
	    break;
	case SORT_ANNOTATION:
	    dlist_setatom(parent, NULL, "ANNOTATION");
	    dlist_setatom(parent, NULL, sortcrit[i].args.annot.entry);
	    dlist_setatom(parent, NULL, sortcrit[i].args.annot.userid);
	    break;
	case SORT_MODSEQ:
	    dlist_setatom(parent, NULL, "MODSEQ");
	    break;
	case SORT_DISPLAYFROM:
	    dlist_setatom(parent, NULL, "DISPLAYFROM");
	    break;
	case SORT_DISPLAYTO:
	    dlist_setatom(parent, NULL, "DISPLAYTO");
	    break;
	case SORT_UID:
	    dlist_setatom(parent, NULL, "UID");
	    break;
	case SORT_CONVMODSEQ:
	    dlist_setatom(parent, NULL, "CONVMODSEQ");
	    break;
	case SORT_CONVEXISTS:
	    dlist_setatom(parent, NULL, "CONVEXISTS");
	    break;
	case SORT_CONVSIZE:
	    dlist_setatom(parent, NULL, "CONVSIZE");
	    break;
	case SORT_HASFLAG:
	    dlist_setatom(parent, NULL, "FLAG");
	    dlist_setatom(parent, NULL, sortcrit[i].args.flag.name);
	    break;
	case SORT_HASCONVFLAG:
	    dlist_setatom(parent, NULL, "CONVFLAG");
	    dlist_setatom(parent, NULL, sortcrit[i].args.flag.name);
	    break;
	case SORT_FOLDER:
	    dlist_setatom(parent, NULL, "FOLDER");
	    break;
	}
    } while (sortcrit[i++].key != SORT_SEQUENCE);
}

static char *multisort_cachekey(struct sortcrit *sortcrit,
				struct searchargs *searchargs)
{
    struct buf b = BUF_INITIALIZER;
    struct dlist *dl = dlist_newlist(NULL, NULL);
    struct dlist *sc = dlist_newlist(dl, NULL);
    struct dlist *sa = dlist_newlist(dl, NULL);

    index_format_sort(sc, sortcrit);
    index_format_search(sa, searchargs);

    dlist_printbuf(dl, 0, &b);

    dlist_free(&dl);

    return buf_release(&b);
}

static struct multisort_result *multisort_cache_load(struct index_state *state,
						     modseq_t hms,
						     const char *cachekey)
{
    struct sortcache_cleanup_rock rock;
    const char *userid = mboxname_to_userid(state->mailbox->name);
    struct multisort_result *sortres = NULL;
    struct buf prefix = BUF_INITIALIZER;
    const char *val = NULL;
    size_t vallen = 0;
    struct dlist *dl = NULL;
    struct dlist *dc;
    struct dlist *di;
    int i;

    memset(&rock, 0, sizeof(struct sortcache_cleanup_rock));

    rock.db = sortcache_db(userid, 0);
    if (!rock.db) goto done;

    buf_printf(&prefix, MODSEQ_FMT " ", hms);
    rock.prefix = prefix.s;
    rock.prefixlen = prefix.len;

    if (cyrusdb_foreach(rock.db, "", 0, NULL,
			sortcache_cleanup_cb, &rock, NULL))
	goto done;

    buf_appendcstr(&prefix, cachekey);

    if (cyrusdb_fetch(rock.db, prefix.s, prefix.len, &val, &vallen, NULL))
	goto done;

    /* OK, we have found value! */
    if (dlist_parsemap(&dl, 0, val, vallen))
	goto done;

    sortres = xzmalloc(sizeof(struct multisort_result));
    dlist_getnum32(dl, "NFOLDERS", &sortres->nfolders);
    dlist_getnum32(dl, "NMSGS", &sortres->nmsgs);
    sortres->folders = xzmalloc(sortres->nfolders * sizeof(struct multisort_folder));
    sortres->msgs = xzmalloc(sortres->nmsgs * sizeof(struct multisort_item));

    dc = dlist_getchild(dl, "FOLDERS");
    i = 0;
    for (di = dc->head; di; di = di->next) {
	struct dlist *item = di->head;
	sortres->folders[i].name = xstrdup(dlist_cstring(item));
	item = item->next;
	sortres->folders[i].uidvalidity = dlist_num(item);
	i++;
    }

    dc = dlist_getchild(dl, "MSGS");
    i = 0;
    for (di = dc->head; di; di = di->next) {
	struct dlist *item = di->head;
	sortres->msgs[i].folderid = dlist_num(item);
	item = item->next;
	sortres->msgs[i].uid = dlist_num(item);
	item = item->next;
	sortres->msgs[i].cid = dlist_num(item);
	i++;
    }

done:
    if (rock.db)
	cyrusdb_close(rock.db);
    dlist_free(&dl);
    buf_free(&prefix);
    return sortres;
}

static void multisort_cache_save(struct index_state *state,
				 modseq_t hms,
				 const char *cachekey,
				 struct multisort_result *sortres)
{
    const char *userid = mboxname_to_userid(state->mailbox->name);
    struct db *db = NULL;
    struct buf prefix = BUF_INITIALIZER;
    struct buf result = BUF_INITIALIZER;
    struct dlist *dl = NULL;
    struct dlist *dc;
    struct dlist *di;
    int i;

    db = sortcache_db(userid, 1);
    if (!db) goto done;

    buf_printf(&prefix, MODSEQ_FMT " %s", hms, cachekey);

    dl = dlist_newkvlist(NULL, NULL);
    dlist_setnum32(dl, "NFOLDERS", sortres->nfolders);
    dlist_setnum32(dl, "NMSGS", sortres->nmsgs);
    dc = dlist_newlist(dl, "FOLDERS");
    for (i = 0; i < (int)sortres->nfolders; i++) {
	di = dlist_newlist(dc, NULL);
	dlist_setatom(di, NULL, sortres->folders[i].name);
	dlist_setnum32(di, NULL, sortres->folders[i].uidvalidity);
    }
    dc = dlist_newlist(dl, "MSGS");
    for (i = 0; i < (int)sortres->nmsgs; i++) {
	di = dlist_newlist(dc, NULL);
	dlist_setnum32(di, NULL, sortres->msgs[i].folderid);
	dlist_setnum32(di, NULL, sortres->msgs[i].uid);
	dlist_setnum64(di, NULL, sortres->msgs[i].cid);
    }

    dlist_printbuf(dl, 0, &result);

    if (cyrusdb_store(db, prefix.s, prefix.len, result.s, result.len, NULL))
	goto done;

done:
    if (db)
	cyrusdb_close(db);
    dlist_free(&dl);
    buf_free(&prefix);
    buf_free(&result);
}

struct multisort_response {
    struct multisort_item *item;
    ptrarray_t cidother;
};

/*
 * Performs a XCONVMULTISORT command
 */
EXPORTED int index_convmultisort(struct index_state *state,
				 struct sortcrit *sortcrit,
				 struct searchargs *searchargs,
				 const struct windowargs *windowargs)
{
    unsigned int mi;
    unsigned int fi;
    int i;
    hashu64_table seen_cids = HASHU64_TABLE_INITIALIZER;
    uint32_t pos = 0;
    uint32_t anchor_pos = 0;
    uint32_t first_pos = 0;
    unsigned int ninwindow = 0;
    ptrarray_t results = PTRARRAY_INITIALIZER;
    struct multisort_response dummy_response;
    int total = UNPREDICTABLE;
    int r = 0;
    int32_t anchor_folderid = -1;
    char extname[MAX_MAILBOX_BUFFER];
    modseq_t hms;
    struct multisort_result *sortres = NULL;
    char *cachekey;

    assert(windowargs);
    assert(!windowargs->changedsince);
    assert(!windowargs->upto);

    /* Client needs to have specified MULTIANCHOR which includes
     * the folder name instead of just ANCHOR.  Check that here
     * 'cos it's easier than doing so during parsing */
    if (windowargs->anchor && !windowargs->anchorfolder)
	return IMAP_PROTOCOL_BAD_PARAMETERS;

    hms = mboxname_readmodseq(state->mailbox->name);
    cachekey = multisort_cachekey(sortcrit, searchargs);

    sortres = multisort_cache_load(state, hms, cachekey);
    if (sortres) {
	syslog(LOG_NOTICE, "CACHEKEY HIT %llu %s", hms, cachekey);
    }
    else {
	sortres = multisort_run(state, sortcrit, searchargs);
	/* OK if it fails */
	multisort_cache_save(state, hms, cachekey, sortres);
	syslog(LOG_NOTICE, "CACHEKEY MISS %llu %s", hms, cachekey);
    }

    if (windowargs->anchorfolder) {
	for (fi = 0; fi < sortres->nfolders; fi++) {
	    if (strcmpsafe(windowargs->anchorfolder, sortres->folders[fi].name))
		continue;
	    anchor_folderid = fi;
	    break;
	}
	if (anchor_folderid < 0) {
	    r = IMAP_ANCHOR_NOT_FOUND;
	    goto out;
	}
    }

    /* going to need to do conversation-level breakdown */
    if (windowargs->conversations)
	construct_hashu64_table(&seen_cids, sortres->nmsgs/4+4, 0);
    /* no need */
    else
	total = sortres->nmsgs;

    /* Another pass through the merged message list */
    for (mi = 0; mi < sortres->nmsgs; mi++) {
	struct multisort_item *item = &sortres->msgs[mi];
	struct multisort_response *response = NULL;

	/* figure out whether this message is an exemplar */
	if (windowargs->conversations) {
	    response = hashu64_lookup(item->cid, &seen_cids);
	    /* in conversations mode => only the first message seen
	     * with each unique CID is an exemplar */
	    if (response) {
		if (response != &dummy_response)
		    ptrarray_append(&response->cidother, item);
		continue;
	    }
	    hashu64_insert(item->cid, &dummy_response, &seen_cids);
	}
	/* else not in conversations mode => all messages are exemplars */

	pos++;

	if (!anchor_pos &&
	    windowargs->anchor == item->uid &&
	    anchor_folderid == item->folderid) {
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

	response = xzmalloc(sizeof(struct multisort_response));
	response->item = item;
	ptrarray_push(&results, response);

	if (windowargs->conversations) {
	    hashu64_insert(item->cid, response, &seen_cids);
	}
    }

    if (total == UNPREDICTABLE) {
	/* the total was not predictable prima facie */
	total = pos;
    }

    if (windowargs->anchor && !anchor_pos) {
	/* the anchor was not found */
	assert(results.count == 0);
	r = IMAP_ANCHOR_NOT_FOUND;
	goto out;
    }

    /* Print the resulting list */

    xstats_add(SEARCH_RESULT, results.count);
    if (results.count) {
	/* The untagged reponse would be XCONVMULTISORT but
	 * Mail::IMAPTalk has an undocumented hack whereby any untagged
	 * response matching /sort/i is assumed to be a sequence of
	 * numeric uids.  Meh. */
	prot_printf(state->out, "* XCONVMULTI (");
	for (fi = 0 ; fi < sortres->nfolders ; fi++) {
	    struct multisort_folder *mf = &sortres->folders[fi];

	    searchargs->namespace->mboxname_toexternal(searchargs->namespace,
						       mf->name,
						       searchargs->userid,
						       extname);
	    if (fi)
		prot_printf(state->out, " ");
	    prot_printf(state->out, "(");
	    prot_printstring(state->out, extname);
	    prot_printf(state->out, " %u)", mf->uidvalidity);
	}
	prot_printf(state->out, ") (");
	for (i = 0 ; i < results.count ; i++) {
	    struct multisort_response *response = results.data[i];
	    int j;
	    if (i)
		prot_printf(state->out, " ");
	    prot_printf(state->out, "(%u %u %llu (", response->item->folderid,
			response->item->uid, response->item->cid);
	    for (j = 0; j < response->cidother.count; j++) {
		struct multisort_item *item = response->cidother.data[j];
		if (j)
		    prot_printf(state->out, " ");
		prot_printf(state->out, "(%u %u)", item->folderid, item->uid);
	    }
	    prot_printf(state->out, "))");
	    /* clean up here */
	    ptrarray_fini(&response->cidother);
	    free(response);
	}
	prot_printf(state->out, ")\r\n");
    }

out:
    if (!r) {
	if (first_pos)
	    prot_printf(state->out, "* OK [POSITION %u]\r\n", first_pos);

	prot_printf(state->out, "* OK [HIGHESTMODSEQ " MODSEQ_FMT "]\r\n",
		    hms);
#if 0
	prot_printf(state->out, "* OK [UIDNEXT %u]\r\n",
		    state->mailbox->i.last_uid + 1);
#endif
	prot_printf(state->out, "* OK [TOTAL %u]\r\n",
		    total);
    }

    /* free all our temporary data */
    ptrarray_fini(&results);
    for (fi = 0 ; fi < sortres->nfolders ; fi++) {
	free(sortres->folders[fi].name);
    }
    free(sortres->folders);
    free(sortres->msgs);
    free(sortres);
    free_hashu64_table(&seen_cids, NULL);

    return r;
}

struct snippet_rock {
    struct protstream *out;
    struct namespace *namespace;
    const char *userid;
};

static int emit_snippet(struct mailbox *mailbox, uint32_t uid,
			int part, const char *snippet, void *rock)
{
    struct snippet_rock *sr = (struct snippet_rock *)rock;
    const char *partname = search_part_as_string(part);
    int r;
    char extname[MAX_MAILBOX_BUFFER];

    if (!partname) return 0;

    r = sr->namespace->mboxname_toexternal(sr->namespace, mailbox->name,
					   sr->userid, extname);
    if (r) return r;

    prot_printf(sr->out, "* SNIPPET ");
    prot_printstring(sr->out, extname);
    prot_printf(sr->out, " %u %u %s ", mailbox->i.uidvalidity, uid, partname);
    prot_printstring(sr->out, snippet);
    prot_printf(sr->out, "\r\n");
    return 0;
}

EXPORTED int index_snippets(struct index_state *state,
			    const struct snippetargs *snippetargs,
			    struct searchargs *searchargs)
{
    void *intquery = NULL;
    search_builder_t *bx = NULL;
    search_text_receiver_t *rx = NULL;
    struct mailbox *mailbox = NULL;
    int i;
    int r = 0;
    int nmatches = 0;
    struct snippet_rock srock;

    bx = search_begin_search(state->mailbox, SEARCH_MULTIPLE);
    if (!bx) {
	r = IMAP_INTERNAL;
	goto out;
    }

    build_query(bx, searchargs, 0, &nmatches);
    intquery = bx->get_internalised(bx);
    search_end_search(bx);
    if (!intquery) goto out;

    srock.out = state->out;
    srock.namespace = searchargs->namespace;
    srock.userid = searchargs->userid;
    rx = search_begin_snippets(intquery, 0/*verbose*/,
			       emit_snippet, &srock);

    for ( ; snippetargs ; snippetargs = snippetargs->next) {

	mailbox = NULL;
	if (!strcmp(snippetargs->mboxname, state->mailbox->name)) {
	    mailbox = state->mailbox;
	}
	else {
	    r = mailbox_open_iwl(snippetargs->mboxname, &mailbox);
	    if (r) goto out;
	}

	if (snippetargs->uidvalidity &&
	    snippetargs->uidvalidity != mailbox->i.uidvalidity) {
	    r = IMAP_NOTFOUND;
	    goto out;
	}

	r = rx->begin_mailbox(rx, mailbox, /*incremental*/0);

	for (i = 0 ; i < snippetargs->uids.count ; i++) {
	    uint32_t uid = snippetargs->uids.data[i];
	    struct index_record record;
	    message_t *msg;

	    /* This UID didn't appear in the old index file */
	    r = mailbox_find_index_record(mailbox, uid, &record, NULL);
	    if (r) goto out;

	    msg = message_new_from_record(mailbox, &record);
	    index_getsearchtext(msg, rx, /*snippet*/1);
	    message_unref(&msg);
	}

	r = rx->end_mailbox(rx, mailbox);
	if (r) goto out;
	if (mailbox != state->mailbox)
	    mailbox_close(&mailbox);
    }

out:
    if (rx) search_end_snippets(rx);
    if (intquery) search_free_internalised(intquery);
    if (mailbox != state->mailbox)
	mailbox_close(&mailbox);
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
EXPORTED int index_convupdates(struct index_state *state,
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

    /* make sure \Deleted messages are expunged.  Will also lock the
     * mailbox state and read any new information */
    r = index_expunge(state, NULL, 1);
    if (r) return r;

    cstate = conversations_get_mbox(state->mailbox->name);
    if (!cstate)
	return IMAP_INTERNAL;

    total = search_predict_total(state, cstate, searchargs,
				windowargs->conversations,
				&xconvmodseq);
    /* If there are no current and no expunged messages, we won't
     * have any results at all and can short circuit the main loop;
     * note that is a righter criterion than for XCONVSORT. */
    if (!total && !state->exists)
	goto out;

    construct_hashu64_table(&seen_cids, state->exists/4+4, 0);
    construct_hashu64_table(&old_seen_cids, state->exists/4+4, 0);

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
	    msg->uid == windowargs->upto) {
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
EXPORTED int index_thread(struct index_state *state, int algorithm,
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
EXPORTED int
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
    struct mailbox *mailbox;
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

    mailbox = state->mailbox;

    seq = _parse_sequence(state, sequence, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	checkval = usinguid ? im->uid : msgno;
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
			  qptr, namespace, isadmin,
			  ismove ? EVENT_MESSAGE_MOVE : EVENT_MESSAGE_COPY);
    if (r) goto done;

    docopyuid = (appendstate.myrights & ACL_READ);

    r = append_copy(mailbox, &appendstate, copyargs.nummsg,
		    copyargs.copymsg, nolink);
    if (r) {
	append_abort(&appendstate);
	goto done;
    }

    r = append_commit(&appendstate);
    if (r) goto done;

    /* unlock first so we don't hold the lock while expunging
     * the source */
    mailbox_unlock_index(destmailbox, NULL);

    if (docopyuid || ismove) {
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

done:
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
    struct buf msg = BUF_INITIALIZER;
    unsigned flag, flagmask;
    char datebuf[RFC3501_DATETIME_MAX+1];
    char sepchar = '(';
    struct index_record record;
    int r;

    r = index_reload_record(state, msgno, &record);
    if (r) return r;

    /* Open the message file */
    if (mailbox_map_message(mailbox, record.uid, &msg))
	return IMAP_NO_MSGGONE;

    /* start the individual append */
    prot_printf(pout, " ");

    /* add system flags */
    if (record.system_flags & FLAG_ANSWERED) {
	prot_printf(pout, "%c\\Answered", sepchar);
	sepchar = ' ';
    }
    if (record.system_flags & FLAG_FLAGGED) {
	prot_printf(pout, "%c\\Flagged", sepchar);
	sepchar = ' ';
    }
    if (record.system_flags & FLAG_DRAFT) {
	prot_printf(pout, "%c\\Draft", sepchar);
	sepchar = ' ';
    }
    if (record.system_flags & FLAG_DELETED) {
	prot_printf(pout, "%c\\Deleted", sepchar);
	sepchar = ' ';
    }
    if (record.system_flags & FLAG_SEEN) {
	prot_printf(pout, "%c\\Seen", sepchar);
	sepchar = ' ';
    }

    /* add user flags */
    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	if ((flag & 31) == 0) {
	    flagmask = record.user_flags[flag/32];
	}
	if (state->flagname[flag] && (flagmask & (1<<(flag & 31)))) {
	    prot_printf(pout, "%c%s", sepchar, state->flagname[flag]);
	    sepchar = ' ';
	}
    }

    /* add internal date */
    time_to_rfc3501(record.internaldate, datebuf, sizeof(datebuf));
    prot_printf(pout, ") \"%s\" ", datebuf);

    /* message literal */
    index_fetchmsg(state, &msg, 0, record.size, 0, 0);

    /* close the message file */
    buf_free(&msg);

    return 0;
}

/*
 * Performs a COPY command from a local mailbox to a remote mailbox
 */
EXPORTED int index_copy_remote(struct index_state *state, char *sequence,
		      int usinguid, struct protstream *pout)
{
    uint32_t msgno;
    struct seqset *seq;
    struct index_map *im;
    int r;

    r = index_check(state, usinguid, usinguid);
    if (r) return r;

    seq = _parse_sequence(state, sequence, usinguid);

    for (msgno = 1; msgno <= state->exists; msgno++) {
	im = &state->map[msgno-1];
	if (!seqset_ismember(seq, usinguid ? im->uid : msgno))
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
EXPORTED uint32_t index_finduid(struct index_state *state, uint32_t uid)
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
void index_fetchmsg(struct index_state *state, const struct buf *msg,
		    unsigned offset,
		    unsigned size,     /* this is the correct size for a news message after
					  having LF translated to CRLF */
		    unsigned start_octet, unsigned octet_count)
{
    unsigned n, domain;

    /* If no data, output NIL */
    if (!msg || !msg->s) {
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
    if (offset + size > msg->len) {
	if (msg->len > offset) {
	    n = msg->len - offset;
	}
	else {
	    prot_printf(state->out, "\"\"");
	    return;
	}
    }

    /* Get domain of the data */
    domain = data_domain(msg->s + offset, n);

    if (domain == DOMAIN_BINARY) {
	/* Write size of literal8 */
	prot_printf(state->out, "~{%u}\r\n", size);
    } else {
	/* Write size of literal */
	prot_printf(state->out, "{%u}\r\n", size);
    }

    /* Non-text literal -- tell the protstream about it */
    if (domain != DOMAIN_7BIT) prot_data_boundary(state->out);

    prot_write(state->out, msg->s + offset, n);
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
			      const struct buf *inmsg,
			      char *section, const char *cachestr, unsigned size,
			      unsigned start_octet, unsigned octet_count)
{
    const char *p;
    int32_t skip = 0;
    int fetchmime = 0;
    unsigned offset = 0;
    char *decbuf = NULL;
    struct buf msg = BUF_INITIALIZER;

    buf_init_ro(&msg, inmsg->s, inmsg->len);

    p = section;

    /* Special-case BODY[] */
    if (*p == ']') {
	if (strstr(resp, "BINARY.SIZE")) {
	    prot_printf(state->out, "%s%u", resp, size);
	} else {
	    prot_printf(state->out, "%s", resp);
	    index_fetchmsg(state, &msg, 0, size,
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

    if (msg.s && (p = strstr(resp, "BINARY"))) {
	/* BINARY or BINARY.SIZE */
	int encoding = CACHE_ITEM_BIT32(cachestr + 2 * 4) & 0xff;
	size_t newsize;

	/* check that the offset isn't corrupt */
	if (offset + size > msg_size) {
	    syslog(LOG_ERR, "invalid part offset in %s", state_mboxname(state));
	    return IMAP_IOERROR;
	}

	msg.s = (char *)charset_decode_mimebody(msg.s + offset, size, encoding,
						&decbuf, &newsize);

	if (!msg.s) {
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
	    msg.len = newsize;
	}
    }

    /* Output body part */
    prot_printf(state->out, "%s", resp);
    index_fetchmsg(state, &msg, offset, size,
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
    static struct buf buf = BUF_INITIALIZER;

    if (offset + size > msg_size) {
	/* Message file is too short, truncate request */
	if (offset < msg_size) {
	    size = msg_size - offset;
	}
	else {
	    size = 0;
	}
    }

    buf_reset(&buf);
    buf_appendmap(&buf, msg_base+offset, size);
    return (char *)buf_cstring(&buf);
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
    static struct buf buf = BUF_INITIALIZER;
    unsigned size;
    unsigned crlf_start = 0;
    unsigned crlf_size = 2;
    struct mailbox *mailbox = state->mailbox;

    if (mailbox_cacherecord(mailbox, record)) {
	/* bogus cache record */
	prot_printf(state->out, "\"\"");
	return;
    }

    buf_setmap(&buf, cacheitem_base(record, CACHE_HEADERS),
		     cacheitem_size(record, CACHE_HEADERS));
    buf_cstring(&buf);

    message_pruneheader(buf.s, headers, 0);
    size = strlen(buf.s); /* not buf.len, it has been pruned */

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
	prot_write(state->out, buf.s + start_octet, size);
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

EXPORTED void index_checkflags(struct index_state *state, int print, int dirty)
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
	if (im->system_flags & FLAG_EXPUNGED) {
	    state->exists--;
	    /* they never knew about this one, skip */
	    if (msgno > state->oldexists)
		continue;
	    state->oldexists--;
	    if (state->qresync)
		seqset_add(vanishedlist, im->uid, 1);
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

EXPORTED void index_tellchanges(struct index_state *state, int canexpunge,
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
	if (im->system_flags & FLAG_EXPUNGED)
	    continue;

	/* report if it's changed since last told */
	if (im->modseq > im->told_modseq)
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
			           state->map[msgno-1].uid,
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
    if (im->system_flags & FLAG_ANSWERED) {
	prot_printf(state->out, "%c\\Answered", sepchar);
	sepchar = ' ';
    }
    if (im->system_flags & FLAG_FLAGGED) {
	prot_printf(state->out, "%c\\Flagged", sepchar);
	sepchar = ' ';
    }
    if (im->system_flags & FLAG_DRAFT) {
	prot_printf(state->out, "%c\\Draft", sepchar);
	sepchar = ' ';
    }
    if (im->system_flags & FLAG_DELETED) {
	prot_printf(state->out, "%c\\Deleted", sepchar);
	sepchar = ' ';
    }
    if (im->isseen) {
	prot_printf(state->out, "%c\\Seen", sepchar);
	sepchar = ' ';
    }
    for (flag = 0; flag < VECTOR_SIZE(state->flagname); flag++) {
	if ((flag & 31) == 0) {
	    flagmask = im->user_flags[flag/32];
	}
	if (state->flagname[flag] && (flagmask & (1<<(flag & 31)))) {
	    prot_printf(state->out, "%c%s", sepchar, state->flagname[flag]);
	    sepchar = ' ';
	}
    }
    if (sepchar == '(') (void)prot_putc('(', state->out);
    (void)prot_putc(')', state->out);
    im->told_modseq = im->modseq;
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
	prot_printf(state->out, " UID %u", im->uid);
    if (printmodseq || state->qresync)
	prot_printf(state->out, " MODSEQ (" MODSEQ_FMT ")", im->modseq);
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
    struct buf msg = BUF_INITIALIZER;
    struct octetinfo *oi = NULL;
    int sepchar = '(';
    int started = 0;
    struct section *section;
    struct fieldlist *fsection;
    char respbuf[100];
    int r = 0;
    struct index_map *im = &state->map[msgno-1];
    struct index_record record;

    /* Check the modseq against changedsince */
    if (fetchargs->changedsince && im->modseq <= fetchargs->changedsince)
	return 0;

    /* skip missing records entirely */
    if (!im->recno)
	return 0;

    r = index_reload_record(state, msgno, &record);
    if (r) {
	prot_printf(state->out, "* OK ");
	prot_printf(state->out, error_message(IMAP_NO_MSGGONE), msgno);
	prot_printf(state->out, "\r\n");
	return 0;
    }

    /* Check against the CID list filter */
    if (fetchargs->cidhash) {
	const char *key = conversation_id_encode(record.cid);
	if (!hash_lookup(key, fetchargs->cidhash))
	    return 0;
    }

    /* Open the message file if we're going to need it */
    if ((fetchitems & (FETCH_HEADER|FETCH_TEXT|FETCH_SHA1|FETCH_RFC822)) ||
	fetchargs->cache_atleast > record.cache_version || 
	fetchargs->binsections || fetchargs->sizesections ||
	fetchargs->bodysections) {
	if (mailbox_map_message(mailbox, record.uid, &msg)) {
	    prot_printf(state->out, "* OK ");
	    prot_printf(state->out, error_message(IMAP_NO_MSGGONE), msgno);
	    prot_printf(state->out, "\r\n");
	    return 0;
	}
    }

    /* display flags if asked _OR_ if they've changed */
    if (fetchitems & FETCH_FLAGS || im->told_modseq < record.modseq) {
	index_fetchflags(state, msgno);
	sepchar = ' ';
    }
    else if ((fetchitems & ~FETCH_SETSEEN) || fetchargs->fsections ||
	     fetchargs->headers.count || fetchargs->headers_not.count) {
	/* these fetch items will always succeed, so start the response */
	prot_printf(state->out, "* %u FETCH ", msgno);
	started = 1;
    }
    if (fetchitems & FETCH_UID) {
	prot_printf(state->out, "%cUID %u", sepchar, record.uid);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_GUID) {
	prot_printf(state->out, "%cDIGEST.SHA1 %s", sepchar,
		    message_guid_encode(&record.guid));
	sepchar = ' ';
    }

    if (fetchitems & FETCH_INTERNALDATE) {
	time_t msgdate = record.internaldate;
	char datebuf[RFC3501_DATETIME_MAX+1];

	time_to_rfc3501(msgdate, datebuf, sizeof(datebuf));

	prot_printf(state->out, "%cINTERNALDATE \"%s\"",
		    sepchar, datebuf);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_MODSEQ) {
	prot_printf(state->out, "%cMODSEQ (" MODSEQ_FMT ")",
		    sepchar, record.modseq);
	sepchar = ' ';
    }
    if (fetchitems & FETCH_SIZE) {
	prot_printf(state->out, "%cRFC822.SIZE %u", 
		    sepchar, record.size);
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
	unsigned int msg_size = msg.len;
	if (!msg.s) {
	    char *fname = mailbox_message_fname(mailbox, record.uid);
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
	message_guid_generate(&tmpguid, msg.s, msg.len);
	prot_printf(state->out, "%cRFC822.SHA1 %s", sepchar, message_guid_encode(&tmpguid));
	sepchar = ' ';
    }
    if ((fetchitems & FETCH_CID) &&
	config_getswitch(IMAPOPT_CONVERSATIONS)) {
	struct buf buf = BUF_INITIALIZER;
	if (!record.cid)
	    buf_appendcstr(&buf, "NIL");
	else
	    buf_printf(&buf, CONV_FMT, record.cid);
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
        if (!mailbox_cacherecord(mailbox, &record)) {
	    prot_printf(state->out, "%cENVELOPE ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&record, CACHE_ENVELOPE));
	}
    }
    if (fetchitems & FETCH_BODYSTRUCTURE) {
        if (!mailbox_cacherecord(mailbox, &record)) {
	    prot_printf(state->out, "%cBODYSTRUCTURE ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&record, CACHE_BODYSTRUCTURE));
	}
    }
    if (fetchitems & FETCH_BODY) {
        if (!mailbox_cacherecord(mailbox, &record)) {
	    prot_printf(state->out, "%cBODY ", sepchar);
	    sepchar = ' ';
	    prot_putbuf(state->out, cacheitem_buf(&record, CACHE_BODY));
	}
    }

    if (fetchitems & FETCH_HEADER) {
	prot_printf(state->out, "%cRFC822.HEADER ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, &msg, 0,
		       record.header_size,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->start_octet : 0,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->octet_count : 0);
    }
    else if (fetchargs->headers.count || fetchargs->headers_not.count) {
	prot_printf(state->out, "%cRFC822.HEADER ", sepchar);
	sepchar = ' ';
	if (fetchargs->cache_atleast > record.cache_version) {
	    index_fetchheader(state, msg.s, msg.len,
			      record.header_size,
			      &fetchargs->headers, &fetchargs->headers_not);
	} else {
	    index_fetchcacheheader(state, &record, &fetchargs->headers, 0, 0);
	}
    }

    if (fetchitems & FETCH_TEXT) {
	prot_printf(state->out, "%cRFC822.TEXT ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, &msg,
		       record.header_size, record.size - record.header_size,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->start_octet : 0,
		       (fetchitems & FETCH_IS_PARTIAL) ?
		         fetchargs->octet_count : 0);
    }
    if (fetchitems & FETCH_RFC822) {
	prot_printf(state->out, "%cRFC822 ", sepchar);
	sepchar = ' ';
	index_fetchmsg(state, &msg, 0, record.size,
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

	if (fetchargs->cache_atleast > record.cache_version) {
	    if (!mailbox_cacherecord(mailbox, &record))
		index_fetchfsection(state, msg.s, msg.len,
				    fsection,
				    cacheitem_base(&record, CACHE_SECTION),
				    (fetchitems & FETCH_IS_PARTIAL) ?
				      fetchargs->start_octet : oi->start_octet,
				    (fetchitems & FETCH_IS_PARTIAL) ?
				      fetchargs->octet_count : oi->octet_count);
	    else
		prot_printf(state->out, "NIL");
	    
	}
	else {
	    index_fetchcacheheader(state, &record, fsection->fields,
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

	if (!mailbox_cacherecord(mailbox, &record)) {
	    r = index_fetchsection(state, respbuf, &msg,
				   section->name, cacheitem_base(&record, CACHE_SECTION),
				   record.size,
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

	if (!mailbox_cacherecord(mailbox, &record)) {
	    oi = &section->octetinfo;
	    r = index_fetchsection(state, respbuf, &msg,
				   section->name, cacheitem_base(&record, CACHE_SECTION),
				   record.size,
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

        if (!mailbox_cacherecord(mailbox, &record)) {
	    r = index_fetchsection(state, respbuf, &msg,
				   section->name, cacheitem_base(&record, CACHE_SECTION),
				   record.size,
				   fetchargs->start_octet, fetchargs->octet_count);
	    if (!r) sepchar = ' ';
	}
    }
    if (sepchar != '(') {
	/* finsh the response if we have one */
	prot_printf(state->out, ")\r\n");
    }
    buf_free(&msg);

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
EXPORTED int index_urlfetch(struct index_state *state, uint32_t msgno,
		   unsigned params, const char *section,
		   unsigned long start_octet, unsigned long octet_count,
		   struct protstream *pout, unsigned long *outsize)
{
    const char *data;
    struct buf msg = BUF_INITIALIZER;
    const char *cacheitem;
    int fetchmime = 0, domain = DOMAIN_7BIT;
    size_t size;
    int32_t skip = 0;
    int n, r = 0;
    char *decbuf = NULL;
    struct mailbox *mailbox = state->mailbox;
    struct index_record record;

    if (outsize) *outsize = 0;

    r = index_reload_record(state, msgno, &record);

    r = mailbox_cacherecord(mailbox, &record);
    if (r) return r;

    /* Open the message file */
    if (mailbox_map_message(mailbox, record.uid, &msg))
	return IMAP_NO_MSGGONE;

    data = msg.s;
    size = record.size;

    if (size > msg.len) size = msg.len;

    cacheitem = cacheitem_base(&record, CACHE_SECTION);

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
    buf_free(&msg);

    if (decbuf) free(decbuf);
    return r;
}

/*
 * Helper function to perform a STORE command for flags.
 */
static int index_storeflag(struct index_state *state,
                           struct index_modified_flags *modified_flags,
                           uint32_t msgno, struct storeargs *storeargs)
{
    bit32 old, new;
    unsigned i;
    int dirty = 0;
    modseq_t oldmodseq;
    struct index_map *im = &state->map[msgno-1];
    struct index_record record;
    int r;

    memset(modified_flags, 0, sizeof(struct index_modified_flags));

    oldmodseq = im->modseq;

    r = index_reload_record(state, msgno, &record);
    if (r) return r;

    /* Change \Seen flag.  This gets done on the index first and will only be
       copied into the record later if internalseen is set */
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

    old = record.system_flags;
    new = storeargs->system_flags;

    /* all other updates happen directly to the record */
    if (storeargs->operation == STORE_REPLACE_FLAGS) {
	if (!(state->myrights & ACL_WRITE)) {
	    /* ACL_DELETE handled in index_store() */
	    if ((old & FLAG_DELETED) != (new & FLAG_DELETED)) {
		dirty++;
	        record.system_flags = (old & ~FLAG_DELETED) | (new & FLAG_DELETED);
	    }
	}
	else {
	    if (!(state->myrights & ACL_DELETEMSG)) {
		if ((old & ~FLAG_DELETED) != (new & ~FLAG_DELETED)) {
		    dirty++;
		    record.system_flags = (old & FLAG_DELETED) | (new & ~FLAG_DELETED);
		}
	    }
	    else {
		if (old != new) {
		    dirty++;
		    record.system_flags = new;
		}
	    }
	    for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
		if (record.user_flags[i] != storeargs->user_flags[i]) {
		    bit32 changed;
		    dirty++;

		    changed = ~record.user_flags[i] & storeargs->user_flags[i];
		    if (changed) {
			modified_flags->added_user_flags[i] = changed;
			modified_flags->added_flags++;
		    }

		    changed = record.user_flags[i] & ~storeargs->user_flags[i];
		    if (changed) {
			modified_flags->removed_user_flags[i] = changed;
			modified_flags->removed_flags++;
		    }
		    record.user_flags[i] = storeargs->user_flags[i];
		}
	    }
	}
    }
    else if (storeargs->operation == STORE_ADD_FLAGS) {
	bit32 added;

	if (~old & new) {
	    dirty++;
	    record.system_flags = old | new;
	}
	for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	    added = ~record.user_flags[i] & storeargs->user_flags[i];
	    if (added) {
		dirty++;
		record.user_flags[i] |= storeargs->user_flags[i];

		modified_flags->added_user_flags[i] = added;
		modified_flags->added_flags++;
	    }
	}
    }
    else { /* STORE_REMOVE_FLAGS */
	bit32 removed;

	if (old & new) {
	    dirty++;
	    record.system_flags &= ~storeargs->system_flags;
	}
	for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	    removed = record.user_flags[i] & storeargs->user_flags[i];
	    if (removed) {
		dirty++;
		record.user_flags[i] &= ~storeargs->user_flags[i];

		modified_flags->removed_user_flags[i] = removed;
		modified_flags->removed_flags++;
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
	/* copy the seen flag from the index */
	if (im->isseen)
	    record.system_flags |= FLAG_SEEN;
	else
	    record.system_flags &= ~FLAG_SEEN;
    }

    modified_flags->added_system_flags = ~old & record.system_flags;
    if (modified_flags->added_system_flags)
	modified_flags->added_flags++;
    modified_flags->removed_system_flags = old & ~record.system_flags;
    if (modified_flags->removed_system_flags)
	modified_flags->removed_flags++;

    r = index_rewrite_record(state, msgno, &record);
    if (r) return r;

    /* if it's silent and unchanged, update the seen value, but
     * not if qresync is enabled - RFC 4551 says that the MODSEQ
     * must always been told, and we prefer just to tell flags
     * as well in this case, it's simpler and not much more
     * bandwidth */
    if (!state->qresync && storeargs->silent && im->told_modseq == oldmodseq)
	im->told_modseq = im->modseq;

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
    struct index_record record;
    annotate_state_t *astate = NULL;
    struct index_map *im = &state->map[msgno-1];
    int r;

    r = index_reload_record(state, msgno, &record);

    oldmodseq = record.modseq;

    r = mailbox_get_annotate_state(state->mailbox, record.uid, &astate);
    if (r) goto out;
    annotate_state_set_auth(astate, storeargs->isadmin,
			    storeargs->userid, storeargs->authstate);
    r = annotate_state_store(astate, storeargs->entryatts);
    if (r) goto out;

    /* It would be nice if the annotate layer told us whether it
     * actually made a change to the database, but it doesn't, so
     * we have to assume the message is dirty */

    r = index_rewrite_record(state, msgno, &record);
    if (r) goto out;

    /* if it's silent and unchanged, update the seen value */
    if (!state->qresync && storeargs->silent && im->told_modseq == oldmodseq)
	im->told_modseq = im->modseq;

out:
    return r;
}


static int _search_searchbuf(char *s, comp_pat *p, struct buf *b)
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
			           state->map[msgno-1].uid,
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
				 const struct searchargs *searchargs,
				 uint32_t msgno,
				 struct buf *msgfile)
{
    unsigned i;
    struct strlist *l, *h;
    struct searchsub *s;
    struct seqset *seq;
    struct index_map *im = &state->map[msgno-1];
    struct index_record record;
    conversation_t *conv = NULL;
    struct searchannot *sa;
    struct buf localmap = BUF_INITIALIZER;
    int retval = 0;

    if (index_reload_record(state, msgno, &record))
	goto zero;

    if (!msgfile) xstats_inc(SEARCH_EVALUATE);

    if (!msgfile) msgfile = &localmap;

    if ((searchargs->flags & SEARCH_RECENT_SET) && !im->isrecent)
	goto zero;
    if ((searchargs->flags & SEARCH_RECENT_UNSET) && im->isrecent)
	goto zero;
    if ((searchargs->flags & SEARCH_SEEN_SET) && !im->isseen)
	goto zero;
    if ((searchargs->flags & SEARCH_SEEN_UNSET) && im->isseen)
	goto zero;

    if (searchargs->smaller && record.size >= searchargs->smaller)
	goto zero;
    if (searchargs->larger && record.size <= searchargs->larger)
	goto zero;

    if (searchargs->after && record.internaldate < searchargs->after)
	goto zero;
    if (searchargs->before && record.internaldate >= searchargs->before)
	goto zero;
    if (searchargs->sentafter && record.sentdate < searchargs->sentafter)
	goto zero;
    if (searchargs->sentbefore && record.sentdate >= searchargs->sentbefore)
	goto zero;

    if (searchargs->modseq && record.modseq < searchargs->modseq)
	goto zero;

    if (~record.system_flags & searchargs->system_flags_set)
	goto zero;
    if (record.system_flags & searchargs->system_flags_unset)
	goto zero;

    for (i = 0; i < (MAX_USER_FLAGS/32); i++) {
	if (~record.user_flags[i] & searchargs->user_flags_set[i])
	    goto zero;
	if (record.user_flags[i] & searchargs->user_flags_unset[i])
	    goto zero;
    }

    for (seq = searchargs->sequence; seq; seq = seq->nextseq) {
	if (!seqset_ismember(seq, msgno)) goto zero;
    }
    for (seq = searchargs->uidsequence; seq; seq = seq->nextseq) {
	if (!seqset_ismember(seq, record.uid)) goto zero;
    }

    for (l = searchargs->folder; l; l = l->next) {
	if (strcmpsafe(l->s, state->mailbox->name)) goto zero;
    }

    if (searchargs->from || searchargs->to || searchargs->cc ||
	searchargs->bcc || searchargs->subject || searchargs->messageid) {

	if (mailbox_cacherecord(state->mailbox, &record))
	    goto zero;

	if (searchargs->messageid) {
	    char *tmpenv;
	    char *envtokens[NUMENVTOKENS];
	    char *msgid;
	    int msgidlen;

	    /* must be long enough to actually HAVE some contents */
	    if (cacheitem_size(&record, CACHE_ENVELOPE) <= 2)
		goto zero;

	    /* get msgid out of the envelope */

	    /* get a working copy; strip outer ()'s */
	    /* +1 -> skip the leading paren */
	    /* -2 -> don't include the size of the outer parens */
	    tmpenv = xstrndup(cacheitem_base(&record, CACHE_ENVELOPE) + 1, 
			      cacheitem_size(&record, CACHE_ENVELOPE) - 2);
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
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&record, CACHE_FROM)))
		goto zero;
	}

	for (l = searchargs->to; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&record, CACHE_TO)))
		goto zero;
	}

	for (l = searchargs->cc; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&record, CACHE_CC)))
		goto zero;
	}

	for (l = searchargs->bcc; l; l = l->next) {
	    if (!_search_searchbuf(l->s, l->p, cacheitem_buf(&record, CACHE_BCC)))
		goto zero;
	}

	for (l = searchargs->subject; l; l = l->next) {
	    if ((cacheitem_size(&record, CACHE_SUBJECT) == 3 && 
		!strncmp(cacheitem_base(&record, CACHE_SUBJECT), "NIL", 3)) ||
		!_search_searchbuf(l->s, l->p, cacheitem_buf(&record, CACHE_SUBJECT)))
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
	searchargs->cache_atleast > record.cache_version) {
	if (!msgfile->s) { /* Map the message in if we haven't before */
	    if (mailbox_map_message(mailbox, record.uid, msgfile))
		goto zero;
	}

	h = searchargs->header_name;
	for (l = searchargs->header; l; (l = l->next), (h = h->next)) {
	    if (!index_searchheader(h->s, l->s, l->p, msgfile,
				    record.header_size)) goto zero;
	}

	if (mailbox_cacherecord(state->mailbox, &record))
	    goto zero;

	for (l = searchargs->body; l; l = l->next) {
	    if (!index_searchmsg(&record, msgfile, l->s, l->p, 1)) goto zero;
	}
	for (l = searchargs->text; l; l = l->next) {
	    if (!index_searchmsg(&record, msgfile, l->s, l->p, 0)) goto zero;
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
	if (conversation_load(cstate, record.cid, &conv))
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
    buf_free(&localmap);

    return retval;
}

/*
 * Search part of a message for a substring.
 */
struct searchmsg_rock
{
    const char *substr;
    comp_pat *pat;
    int skipheader;
};

static int searchmsg_cb(int partno, int charset, int encoding,
			struct buf *data, void *rock)
{
    struct searchmsg_rock *sr = (struct searchmsg_rock *)rock;

    if (!partno) {
	/* header-like */
	if (sr->skipheader) {
	    sr->skipheader = 0; /* Only skip top-level message header */
	    return 0;
	}
	return charset_search_mimeheader(sr->substr, sr->pat,
					 buf_cstring(data), charset_flags);
    }
    else {
	/* body-like */
	if (charset < 0 || charset == 0xffff)
		return 0;
	return charset_searchfile(sr->substr, sr->pat,
				  data->s, data->len,
				  charset, encoding, charset_flags);
    }
}


static int index_searchmsg(struct index_record *record,
			   const struct buf *msgfile,
			   const char *substr,
			   comp_pat *pat,
			   int skipheader)
{
    struct searchmsg_rock sr;

    xstats_inc(SEARCH_BODY);
    sr.substr = substr;
    sr.pat = pat;
    sr.skipheader = skipheader;
    return message_foreach_part(record, msgfile, searchmsg_cb, &sr);
}

/*
 * Search named header of a message for a substring
 */
static int index_searchheader(char *name,
			      char *substr,
			      comp_pat *pat,
			      struct buf *msgfile,
			      int size)
{
    char *p;
    strarray_t header = STRARRAY_INITIALIZER;

    xstats_inc(SEARCH_HEADER);

    strarray_append(&header, name);

    p = index_readheader(msgfile->s, msgfile->len, 0, size);
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
    struct index_record record;

    r = index_reload_record(state, msgno, &record);
    if (r) return 0;

    xstats_inc(SEARCH_CACHE_HEADER);

    r = mailbox_cacherecord(mailbox, &record);
    if (r) return 0;

    size = cacheitem_size(&record, CACHE_HEADERS);
    if (!size) return 0;	/* No cached headers, fail */
    
    if (bufsize < size+2) {
	bufsize = size+100;
	buf = xrealloc(buf, bufsize);
    }

    /* Copy this item to the buffer */
    memcpy(buf, cacheitem_base(&record, CACHE_HEADERS), size);
    buf[size] = '\0';

    strarray_append(&header, name);
    message_pruneheader(buf, &header, 0);
    strarray_fini(&header);

    if (!*buf) return 0;	/* Header not present, fail */
    if (!*substr) return 1;	/* Only checking existence, succeed */

    return charset_search_mimeheader(substr, pat, strchr(buf, ':') + 1, charset_flags);
}


struct getsearchtext_rock
{
    search_text_receiver_t *receiver;
    int partcount;
    int charset_flags;
};

static void stuff_part(search_text_receiver_t *receiver,
		       int part, const struct buf *buf)
{
    receiver->begin_part(receiver, part);
    receiver->append_text(receiver, buf);
    receiver->end_part(receiver, part);
}

static void extract_cb(const struct buf *text, void *rock)
{
    struct getsearchtext_rock *str = (struct getsearchtext_rock *)rock;
    str->receiver->append_text(str->receiver, text);
}

static int getsearchtext_cb(int partno, int charset, int encoding,
			    const char *subtype, struct buf *data,
			    void *rock)
{
    struct getsearchtext_rock *str = (struct getsearchtext_rock *)rock;
    char *q;
    struct buf text = BUF_INITIALIZER;

    if (!partno) {
	/* header-like */
	q = charset_decode_mimeheader(buf_cstring(data), str->charset_flags);
	buf_init_ro_cstr(&text, q);
	if (++str->partcount == 1) {
	    stuff_part(str->receiver, SEARCH_PART_HEADERS, &text);
	    str->receiver->begin_part(str->receiver, SEARCH_PART_BODY);
	} else {
	    str->receiver->append_text(str->receiver, &text);
	}
	free(q);
	buf_free(&text);
    }
    else {
	/* body-like */
	charset_extract(extract_cb, str, data, charset, encoding, subtype,
			str->charset_flags);
    }

    return 0;
}

EXPORTED int index_getsearchtext(message_t *msg,
			 search_text_receiver_t *receiver,
			 int snippet)
{
    struct getsearchtext_rock str;
    struct buf buf = BUF_INITIALIZER;
    uint32_t uid = 0;
    int format = MESSAGE_SEARCH;
    int r;

    message_get_uid(msg, &uid);
    receiver->begin_message(receiver, uid);

    str.receiver = receiver;
    str.partcount = 0;
    str.charset_flags = charset_flags;

    if (snippet) {
	str.charset_flags |= CHARSET_SNIPPET;
	format = MESSAGE_SNIPPET;
    }

    message_foreach_text_section(msg, getsearchtext_cb, &str);
    receiver->end_part(receiver, SEARCH_PART_BODY);

    if (!message_get_field(msg, "From", format, &buf))
	stuff_part(receiver, SEARCH_PART_FROM, &buf);

    if (!message_get_field(msg, "To", format, &buf))
	stuff_part(receiver, SEARCH_PART_TO, &buf);

    if (!message_get_field(msg, "Cc", format, &buf))
	stuff_part(receiver, SEARCH_PART_CC, &buf);

    if (!message_get_field(msg, "Bcc", format, &buf))
	stuff_part(receiver, SEARCH_PART_BCC, &buf);

    if (!message_get_field(msg, "Subject", format, &buf))
	stuff_part(receiver, SEARCH_PART_SUBJECT, &buf);

    r = receiver->end_message(receiver);
    buf_free(&buf);
    return r;
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
    struct index_record record;

    r = index_reload_record(state, msgno, &record);
    if (r) return 0;

    r = mailbox_cacherecord(mailbox, &record);
    if (r) return r;

    if (copyargs->nummsg == copyargs->msgalloc) {
	copyargs->msgalloc += COPYARGSGROW;
	copyargs->copymsg = (struct copymsg *)
	  xrealloc((char *)copyargs->copymsg,
		   copyargs->msgalloc * sizeof(struct copymsg));
    }

    copyargs->copymsg[copyargs->nummsg].uid = record.uid;
    copyargs->copymsg[copyargs->nummsg].internaldate = record.internaldate;
    copyargs->copymsg[copyargs->nummsg].sentdate = record.sentdate;
    copyargs->copymsg[copyargs->nummsg].gmtime = record.gmtime;
    copyargs->copymsg[copyargs->nummsg].size = record.size;
    copyargs->copymsg[copyargs->nummsg].header_size = record.header_size;
    copyargs->copymsg[copyargs->nummsg].content_lines = record.content_lines;
    copyargs->copymsg[copyargs->nummsg].cache_version = record.cache_version;
    copyargs->copymsg[copyargs->nummsg].cache_crc = record.cache_crc;
    copyargs->copymsg[copyargs->nummsg].crec = record.crec;

    message_guid_copy(&copyargs->copymsg[copyargs->nummsg].guid,
		      &record.guid);

    copyargs->copymsg[copyargs->nummsg].system_flags = record.system_flags;
    for (userflag = 0; userflag < MAX_USER_FLAGS; userflag++) {
	if ((userflag & 31) == 0) {
	    flagmask = record.user_flags[userflag/32];
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
		    (is_same_user ? record.cid : NULLCONVERSATION);

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
    struct index_record record;
    struct index_map *im;
    struct conversations_state *cstate = NULL;
    conversation_t *conv = NULL;

    if (!n) return NULL;

    /* create an array of MsgData */
    ptrs = (MsgData **) xzmalloc(n * sizeof(MsgData *) + n * sizeof(MsgData));
    md = (MsgData *)(ptrs + n);
    xstats_add(MSGDATA_LOAD, n);

    if (found_anchor)
	*found_anchor = 0;

    for (i = 0 ; i < n ; i++) {
	cur = &md[i];
	ptrs[i] = cur;

	/* set msgno */
	cur->msgno = (msgno_list ? msgno_list[i] : (unsigned)(i+1));

	if (index_reload_record(state, cur->msgno, &record))
	    continue;

	im = &state->map[cur->msgno-1];
	cur->uid = record.uid;
	cur->cid = record.cid;
	if (found_anchor && record.uid == anchor)
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
		if (mailbox_cacherecord(mailbox, &record))
		    continue; /* can't do this with a broken cache */

		did_cache++;
	    }

	    if ((label == LOAD_IDS) && !did_env) {
		/* no point if we don't have enough data */
		if (cacheitem_size(&record, CACHE_ENVELOPE) <= 2)
		    continue;

		/* make a working copy of envelope -- strip outer ()'s */
		/* +1 -> skip the leading paren */
		/* -2 -> don't include the size of the outer parens */
		tmpenv = xstrndup(cacheitem_base(&record, CACHE_ENVELOPE) + 1, 
				  cacheitem_size(&record, CACHE_ENVELOPE) - 2);

		/* parse envelope into tokens */
		parse_cached_envelope(tmpenv, envtokens,
				      VECTOR_SIZE(envtokens));

		did_env++;
	    }

	    if ((label == SORT_HASCONVFLAG || label == SORT_CONVMODSEQ ||
		label == SORT_CONVEXISTS || label == SORT_CONVSIZE) && !did_conv) {
		if (!cstate) cstate = conversations_get_mbox(state->mailbox->name);
		assert(cstate);
		if (conversation_load(cstate, record.cid, &conv))
		    continue;
		if (!conv) conv = conversation_new(cstate);
		did_conv++;
	    }

	    switch (label) {
	    case SORT_CC:
		cur->cc = get_localpart_addr(cacheitem_base(&record, CACHE_CC));
		break;
	    case SORT_DATE:
		cur->sentdate = record.gmtime;
		/* fall through */
	    case SORT_ARRIVAL:
		cur->internaldate = record.internaldate;
		break;
	    case SORT_FROM:
		cur->from = get_localpart_addr(cacheitem_base(&record, CACHE_FROM));
		break;
	    case SORT_MODSEQ:
		cur->modseq = record.modseq;
		break;
	    case SORT_SIZE:
		cur->size = record.size;
		break;
	    case SORT_SUBJECT:
		cur->xsubj = index_extract_subject(cacheitem_base(&record, CACHE_SUBJECT),
						   cacheitem_size(&record, CACHE_SUBJECT),
						   &cur->is_refwd);
		cur->xsubj_hash = strhash(cur->xsubj);
		break;
	    case SORT_TO:
		cur->to = get_localpart_addr(cacheitem_base(&record, CACHE_TO));
		break;
 	    case SORT_ANNOTATION: {
		struct buf value = BUF_INITIALIZER;

		annotatemore_msg_lookup(state->mboxname,
					record.uid,
					sortcrit[j].args.annot.entry,
					sortcrit[j].args.annot.userid,
					&value);

		/* buf_release() never returns NULL, so if the lookup
		 * fails for any reason we just get an empty string here */
		strarray_appendm(&cur->annot, buf_release(&value));
 		break;
	    }
	    case LOAD_IDS:
		index_get_ids(cur, envtokens, cacheitem_base(&record, CACHE_HEADERS),
					      cacheitem_size(&record, CACHE_HEADERS));
		break;
	    case SORT_DISPLAYFROM:
		cur->displayfrom = get_displayname(
				   cacheitem_base(&record, CACHE_FROM));
		break;
	    case SORT_DISPLAYTO:
		cur->displayto = get_displayname(
				 cacheitem_base(&record, CACHE_TO));
		break;
	    case SORT_HASFLAG: {
		const char *name = sortcrit[j].args.flag.name;
		if (mailbox_record_hasflag(mailbox, &record, name))
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
	    case SORT_CONVSIZE:
		cur->convsize = conv->size;
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
	    strarray_appendm(&msgdata->ref, in_reply_to);
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
	    time_t d1 = md1->sentdate ? md1->sentdate : md1->internaldate;
	    time_t d2 = md2->sentdate ? md2->sentdate : md2->internaldate;
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
	case SORT_CONVSIZE:
	    ret = numcmp(md1->size, md2->convsize);
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
	case SORT_FOLDER:
	    if (md1->folder && md2->folder)
		ret = strcmpsafe(md1->folder->mboxname, md2->folder->mboxname);
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

    if (!msgdata)
	return;
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
EXPORTED int find_thread_algorithm(char *arg)
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
EXPORTED char *index_get_msgid(struct index_state *state,
			       uint32_t msgno)
{
    struct mailbox *mailbox = state->mailbox;
    struct index_record record;

    if (index_reload_record(state, msgno, &record))
	return NULL;

    return mailbox_cache_get_msgid(mailbox, &record);
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

EXPORTED extern struct nntp_overview *index_overview(struct index_state *state,
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
    struct index_record record;

    /* flush any previous data */
    memset(&over, 0, sizeof(struct nntp_overview));

    if (index_reload_record(state, msgno, &record))
	return NULL;

    if (mailbox_cacherecord(mailbox, &record))
	return NULL; /* upper layers can cope! */

    /* make a working copy of envelope; strip outer ()'s */
    /* -2 -> don't include the size of the outer parens */
    /* +1 -> leave space for NUL */
    size = cacheitem_size(&record, CACHE_ENVELOPE) - 2 + 1;
    if (envsize < size) {
	envsize = size;
	env = xrealloc(env, envsize);
    }
    /* +1 -> skip the leading paren */
    strlcpy(env, cacheitem_base(&record, CACHE_ENVELOPE) + 1, size);

    /* make a working copy of headers */
    size = cacheitem_size(&record, CACHE_HEADERS);
    if (hdrsize < size+2) {
	hdrsize = size+100;
	hdr = xrealloc(hdr, hdrsize);
    }
    memcpy(hdr, cacheitem_base(&record, CACHE_HEADERS), size);
    hdr[size] = '\0';

    parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

    over.uid = record.uid;
    over.bytes = record.size;
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

EXPORTED char *index_getheader(struct index_state *state, uint32_t msgno,
			       char *hdr)
{
    struct buf msg = BUF_INITIALIZER;
    strarray_t headers = STRARRAY_INITIALIZER;
    static char *alloc = NULL;
    static unsigned allocsize = 0;
    unsigned size;
    char *buf;
    struct mailbox *mailbox = state->mailbox;
    struct index_record record;

    if (index_reload_record(state, msgno, &record))
	return NULL;

    buf_free(&msg);

    /* see if the header is cached */
    if (mailbox_cached_header(hdr) != BIT32_MAX &&
        !mailbox_cacherecord(mailbox, &record)) {
    
	size = cacheitem_size(&record, CACHE_HEADERS);
	if (allocsize < size+2) {
	    allocsize = size+100;
	    alloc = xrealloc(alloc, allocsize);
	}

	memcpy(alloc, cacheitem_base(&record, CACHE_HEADERS), size);
	alloc[size] = '\0';

	buf = alloc;
    }
    else {
	/* uncached header */
	if (mailbox_map_message(mailbox, record.uid, &msg))
	    return NULL;

	buf = index_readheader(msg.s, msg.len, 0, record.header_size);
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

EXPORTED extern unsigned long index_getsize(struct index_state *state,
					    uint32_t msgno)
{
    struct index_record record;

    if (index_reload_record(state, msgno, &record))
	return 0;

    return record.size;
}

EXPORTED extern unsigned long index_getlines(struct index_state *state,
					     uint32_t msgno)
{
    struct index_record record;

    if (index_reload_record(state, msgno, &record))
	return 0;

    return record.content_lines;
}

EXPORTED const char *index_mboxname(const struct index_state *state)
{
    if (!state) return NULL;
    return state->mboxname;
}

EXPORTED int index_hasrights(const struct index_state *state, int rights)
{
    return state->myrights & rights;
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

EXPORTED void appendsequencelist(struct index_state *state,
			struct seqset **l,
			char *sequence, int usinguid)
{
    unsigned maxval = usinguid ? state->last_uid : state->exists;
    seqset_append(l, sequence, maxval);
}

EXPORTED void freesequencelist(struct seqset *l)
{
    seqset_free(l);
}
