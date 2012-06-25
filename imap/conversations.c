/* conversations.c -- Routines for dealing with the conversation database
 *
 * Copyright (c) 1994-2010 Carnegie Mellon University.  All rights reserved.
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

#include <config.h>

#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <ctype.h>
#include <stdlib.h>

#include "acl.h"
#include "annotate.h"
#include "append.h"
#include "assert.h"
#include "charset.h"
#include "dlist.h"
#include "exitcodes.h"
#include "hash.h"
#include "imap_err.h"
#include "global.h"
#include "imapd.h"
#include "lsort.h"
#include "mailbox.h"
#include "map.h"
#include "mboxname.h"
#include "message.h"
#include "parseaddr.h"
#include "search_engines.h"
#include "seen.h"
#include "statuscache.h"
#include "strhash.h"
#include "stristr.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "times.h"

#include "conversations.h"


#define CONVERSATION_ID_STRMAX	    (1+sizeof(conversation_id_t)*2)

/* per user conversations db extension */
#define FNAME_CONVERSATIONS_SUFFIX "conversations"
#define FNKEY "$FOLDER_NAMES"
#define CFKEY "$COUNTED_FLAGS"

#define DB config_conversations_db

#define CONVERSATIONS_VERSION 0

static char *convdir = NULL;
static char *suffix = NULL;

void conversations_set_directory(const char *dir)
{
    free(convdir);
    convdir = xstrdupnull(dir);
}

void conversations_set_suffix(const char *suff)
{
    free(suffix);
    suffix = xstrdupnull(suff);
}

static char *conversations_path(struct mboxname_parts *parts)
{
    const char *suff = (suffix ? suffix : FNAME_CONVERSATIONS_SUFFIX);
    if (convdir)
	return strconcat(convdir, "/", parts->userid, ".", suff, (char *)NULL);
    return mboxname_conf_getpath(parts, suff);
}

char *conversations_getuserpath(const char *username)
{
    struct mboxname_parts parts;
    char *fname;

    if (mboxname_userid_to_parts(username, &parts))
	return NULL;
    fname = conversations_path(&parts);
    mboxname_free_parts(&parts);

    return fname;
}

char *conversations_getmboxpath(const char *mboxname)
{
    struct mboxname_parts parts;
    char *fname;

    if (mboxname_to_parts(mboxname, &parts))
	return NULL;
    fname = conversations_path(&parts);
    mboxname_free_parts(&parts);

    return fname;
}

static int _init_counted(struct conversations_state *state,
			 const char *val, int vallen)
{
    int r;

    if (!vallen) {
	val = config_getstring(IMAPOPT_CONVERSATIONS_COUNTED_FLAGS);
	if (!val) val = "";
	vallen = strlen(val);
	r = cyrusdb_store(state->db, CFKEY, strlen(CFKEY),
			  val, vallen, &state->txn);
	if (r) {
	    syslog(LOG_ERR, "Failed to write counted_flags");
	    return r;
	}
    }

    /* remove any existing value */
    if (state->counted_flags) {
	strarray_free(state->counted_flags);
	state->counted_flags = NULL;
    }

    /* add the value only if there's some flags set */
    if (vallen) {
	state->counted_flags = strarray_nsplit(val, vallen, " ");
    }

    return 0;
}

int conversations_open_path(const char *fname, struct conversations_state **statep)
{
    struct conversations_open *open = NULL;
    const char *val = NULL;
    size_t vallen = 0;
    int r = 0;

    if (!fname)
	return IMAP_MAILBOX_BADNAME;

    for (open = open_conversations; open; open = open->next) {
	if (!strcmp(open->s.path, fname))
	    return IMAP_CONVERSATIONS_ALREADY_OPEN;
    }

    open = xzmalloc(sizeof(struct conversations_open));

    r = cyrusdb_open(DB, fname, CYRUSDB_CREATE, &open->s.db);
    if (r || open->s.db == NULL) {
	free(open);
	return IMAP_IOERROR;
    }

    open->s.path = xstrdup(fname);
    open->next = open_conversations;
    open_conversations = open;

    /* ensure a write lock immediately, and also load the counted flags */
    cyrusdb_fetchlock(open->s.db, CFKEY, strlen(CFKEY),
		      &val, &vallen, &open->s.txn);
    _init_counted(&open->s, val, vallen);

    /* we should just read the folder names up front too */
    open->s.folder_names = strarray_new();

    /* if there's a value, parse as a dlist */
    if (!cyrusdb_fetch(open->s.db, FNKEY, strlen(FNKEY),
		   &val, &vallen, &open->s.txn)) {
	struct dlist *dl = NULL;
	struct dlist *dp;
	dlist_parsemap(&dl, 0, val, vallen);
	for (dp = dl->head; dp; dp = dp->next) {
	    strarray_append(open->s.folder_names, dlist_cstring(dp));
	}
	dlist_free(&dl);
    }

    *statep = &open->s;

    return 0;
}

int conversations_open_user(const char *username, struct conversations_state **statep)
{
    char *path = conversations_getuserpath(username);
    int r;
    if (!path) return IMAP_MAILBOX_BADNAME;
    r = conversations_open_path(path, statep);
    free(path);
    return r;
}

int conversations_open_mbox(const char *mboxname, struct conversations_state **statep)
{
    char *path = conversations_getmboxpath(mboxname);
    int r;
    if (!path) return IMAP_MAILBOX_BADNAME;
    r = conversations_open_path(path, statep);
    free(path);
    return r;
}

struct conversations_state *conversations_get_path(const char *fname)
{
    struct conversations_open *open = NULL;

    for (open = open_conversations; open; open = open->next) {
	if (!strcmp(open->s.path, fname))
	    return &open->s;
    }
    
    return NULL;
}

struct conversations_state *conversations_get_user(const char *username)
{
    struct conversations_state *state;
    char *path = conversations_getuserpath(username);
    if (!path) return NULL;
    state = conversations_get_path(path);
    free(path);
    return state;
}

struct conversations_state *conversations_get_mbox(const char *mboxname)
{
    struct conversations_state *state;
    char *path = conversations_getmboxpath(mboxname);
    if (!path) return NULL;
    state = conversations_get_path(path);
    free(path);
    return state;
}


void _conv_remove(struct conversations_state **statep)
{
    struct conversations_open **prevp = &open_conversations;
    struct conversations_open *cur;

    for (cur = open_conversations; cur; cur = cur->next) {
	if (*statep == &cur->s) {
	    /* found it! */
	    *prevp = cur->next;
	    free(cur->s.path);
	    if (cur->s.counted_flags)
		strarray_free(cur->s.counted_flags);
	    if (cur->s.folder_names)
		strarray_free(cur->s.folder_names);
	    free(cur);
	    *statep = NULL;
	    return;
	}
	prevp = &cur->next;
    }

    fatal("unknown conversation db closed", EC_SOFTWARE);
}

int conversations_abort(struct conversations_state **statep)
{
    struct conversations_state *state = *statep;

    if (!state) return 0;
    
    if (state->db) {
	if (state->txn)
	    cyrusdb_abort(state->db, state->txn);
	cyrusdb_close(state->db);
    }

    _conv_remove(statep);

    return 0;
}

int conversations_commit(struct conversations_state **statep)
{
    struct conversations_state *state = *statep;
    int r = 0;

    if (!state) return 0;

    if (state->db) {
	if (state->txn)
	    r = cyrusdb_commit(state->db, state->txn);
	cyrusdb_close(state->db);
    }

    _conv_remove(statep);

    return r;
}

static int check_msgid(const char *msgid, size_t len, size_t *lenp)
{
    if (msgid == NULL)
	return IMAP_INVALID_IDENTIFIER;

    if (!len)
	len = strlen(msgid);

    if (msgid[0] != '<' || msgid[len-1] != '>' || strchr(msgid, '@') == NULL)
	return IMAP_INVALID_IDENTIFIER;

    if (lenp)
	*lenp = len;

    return 0;
}

static int _conversations_set_key(struct conversations_state *state,
				  const char *key, size_t keylen,
				  conversation_id_t cid, time_t stamp)
{
    int r;
    struct buf buf;
    int version = CONVERSATIONS_VERSION;

    buf_init(&buf);

    if (state->db == NULL)
	return IMAP_IOERROR;

    buf_printf(&buf, "%d " CONV_FMT " %lu", version, cid, stamp);

    r = cyrusdb_store(state->db,
		      key, keylen,
		      buf.s, buf.len,
		      &state->txn);

    buf_free(&buf);
    if (r)
	return IMAP_IOERROR;

    return 0;
}

static int _sanity_check_counts(conversation_t *conv)
{
    conv_folder_t *folder;
    uint32_t num_records = 0;
    uint32_t exists = 0;

    for (folder = conv->folders; folder; folder = folder->next) {
	num_records += folder->num_records;
	exists += folder->exists;
    }

    if (num_records != conv->num_records)
	return IMAP_INTERNAL;

    if (exists != conv->exists)
	return IMAP_INTERNAL;

    return 0;
}


int conversations_set_msgid(struct conversations_state *state,
			  const char *msgid,
			  conversation_id_t cid)
{
    size_t keylen;
    int r;

    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    return _conversations_set_key(state, msgid, keylen, cid, time(NULL));
}

static int _conversations_parse(const char *data, size_t datalen,
				conversation_id_t *cidp, time_t *stampp)
{ 
    const char *rest;
    size_t restlen;
    int r;
    bit64 tval;
    bit64 version;

    r = parsenum(data, &rest, datalen, &version);
    if (r) return r;

    if (rest[0] != ' ')
	return IMAP_MAILBOX_BADFORMAT;
    rest++; /* skip space */
    restlen = datalen - (rest - data);

    if (version != CONVERSATIONS_VERSION) {
	/* XXX - an error code for "incorrect version"? */
	return IMAP_MAILBOX_BADFORMAT;
    }

    if (restlen < 17)
	return IMAP_MAILBOX_BADFORMAT;

    r = parsehex(rest, &rest, 16, cidp);
    if (r) return IMAP_MAILBOX_BADFORMAT;

    if (rest[0] != ' ')
	return IMAP_MAILBOX_BADFORMAT;
    rest++; /* skip space */
    restlen = datalen - (rest - data);

    r = parsenum(rest, &rest, restlen, &tval);
    if (r) return IMAP_MAILBOX_BADFORMAT;

    /* should have parsed to the end of the string */
    if (rest - data != (int)datalen)
	return IMAP_MAILBOX_BADFORMAT;

    if (stampp) *stampp = tval;

    return 0;
}

int conversations_get_msgid(struct conversations_state *state,
		          const char *msgid,
		          conversation_id_t *cidp)
{
    size_t keylen;
    size_t datalen = 0;
    const char *data;
    int r;

    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    r = cyrusdb_fetch(state->db,
		      msgid, keylen,
		      &data, &datalen,
		      &state->txn);

    if (!r) r = _conversations_parse(data, datalen, cidp, NULL);

    if (r) *cidp = NULLCONVERSATION;

    return 0;
}

/*
 * Normalise a subject string, to a form which can be used for deciding
 * whether a message belongs in the same conversation as it's antecedent
 * messages.  What we're doing here is the same idea as the "base
 * subject" algorithm described in RFC5256 but slightly adapted from
 * experience.  Differences are:
 *
 *  - We eliminate all whitespace; RFC5256 normalises any sequence
 *    of whitespace characters to a single SP.  We do this because
 *    we have observed combinations of buggy client software both
 *    add and remove whitespace around folding points.
 *
 *  - Because we eliminate whitespace entirely, and whitespace helps
 *    delimit some of our other replacements, we do that whitespace
 *    step last instead of first.
 *
 *  - We eliminate leading tokens like Re: and Fwd: using a simpler
 *    and more generic rule than RFC5256's; this rule catches a number
 *    of semantically identical prefixes in other human languages, but
 *    unfortunately also catches lots of other things.  We think we can
 *    get away with this because the normalised subject is never directly
 *    seen by human eyes, so some information loss is acceptable as long
 *    as the subjects in different messages match correctly.
 */
void conversation_normalise_subject(struct buf *s)
{
    static int initialised_res = 0;
    static regex_t whitespace_re;
    static regex_t relike_token_re;
    static regex_t blob_re;
    int r;

    if (!initialised_res) {
	r = regcomp(&whitespace_re, "[ \t\r\n]+", REG_EXTENDED);
	assert(r == 0);
	r = regcomp(&relike_token_re, "^[ \t]*[A-Za-z0-9]+:", REG_EXTENDED);
	assert(r == 0);
	r = regcomp(&blob_re, "^[ \t]*\\[[^]]+\\]", REG_EXTENDED);
	assert(r == 0);
	initialised_res = 1;
    }

    /* step 1 is to decode any RFC2047 MIME encoding of the header
     * field, but we assume that has already happened */

    /* step 2 is to eliminate all "Re:"-like tokens and [] blobs
     * at the start */
    while (buf_replace_one_re(s, &relike_token_re, NULL) ||
	   buf_replace_one_re(s, &blob_re, NULL))
	;

    /* step 3 is eliminating whitespace. */
    buf_replace_all_re(s, &whitespace_re, NULL);
}

int conversations_set_subject(struct conversations_state *state,
			      conversation_id_t cid,
			      const struct buf *sub)
{
    char skey[CONVERSATION_ID_STRMAX+2];
    struct buf buf = BUF_INITIALIZER;
    int version = CONVERSATIONS_VERSION;
    int r;

    if (state->db == NULL)
	return IMAP_IOERROR;

    snprintf(skey, sizeof(skey), "S" CONV_FMT, cid);

    buf_printf(&buf, "%d ", version);
    buf_append(&buf, sub);

    r = cyrusdb_store(state->db,
		      skey, strlen(skey),
		      buf.s, buf.len,
		      &state->txn);

    buf_free(&buf);
    if (r)
	return IMAP_IOERROR;

    return 0;
}

int conversations_get_subject(struct conversations_state *state,
			      conversation_id_t cid,
			      struct buf *sub)
{
    char skey[CONVERSATION_ID_STRMAX+2];
    size_t datalen = 0;
    const char *data;
    const char *rest;
    size_t restlen;
    int r;
    bit64 version;

    snprintf(skey, sizeof(skey), "S" CONV_FMT, cid);

    r = cyrusdb_fetch(state->db,
		      skey, strlen(skey),
		      &data, &datalen,
		      &state->txn);

    if (r == CYRUSDB_NOTFOUND) {
	buf_free(sub);
	return 0;
    }
    if (r)
	return IMAP_IOERROR;

    rest = data;
    r = parsenum(data, &rest, datalen, &version);
    if (r) return r;

    if (rest[0] != ' ')
	return IMAP_MAILBOX_BADFORMAT;
    rest++; /* skip space */
    restlen = datalen - (rest - data);

    if (version != CONVERSATIONS_VERSION) {
	/* XXX - an error code for "incorrect version"? */
	return IMAP_MAILBOX_BADFORMAT;
    }

    buf_init_ro(sub, rest, restlen);
    buf_cstring(sub);

    return 0;
}

static int conversation_rename_sub(struct conversations_state *state,
				   conversation_id_t from_cid,
				   conversation_id_t to_cid)
{
    char skey[CONVERSATION_ID_STRMAX+2];
    size_t datalen = 0;
    const char *data;
    int r;

    snprintf(skey, sizeof(skey), "S" CONV_FMT, from_cid);

    r = cyrusdb_fetch(state->db,
		      skey, strlen(skey),
		      &data, &datalen,
		      &state->txn);

    if (r == CYRUSDB_NOTFOUND)
	return 0;
    if (r)
	return IMAP_IOERROR;

    snprintf(skey, sizeof(skey), "S" CONV_FMT, to_cid);

    r = cyrusdb_store(state->db,
		      skey, strlen(skey),
		      data, datalen,
		      &state->txn);
    return r;
}

static int write_folders(struct conversations_state *state)
{
    struct dlist *dl = dlist_newlist(NULL, NULL);
    struct buf buf = BUF_INITIALIZER;
    int r;
    int i;

    for (i = 0; i < state->folder_names->count; i++) {
	const char *fname = strarray_nth(state->folder_names, i);
	dlist_setatom(dl, NULL, fname);
    }

    dlist_printbuf(dl, 0, &buf);
    dlist_free(&dl);

    r = cyrusdb_store(state->db, FNKEY, strlen(FNKEY),
		      buf.s, buf.len, &state->txn);

    buf_free(&buf);

    return r;
}

static int folder_number(struct conversations_state *state,
			 const char *name,
			 int create_flag)
{
    int pos = strarray_find(state->folder_names, name, 0);
    int r;

    /* if we have to add it, then save the keys back */
    if (pos < 0 && create_flag) {
	pos = strarray_append(state->folder_names, name);

	/* store must succeed */
	r = write_folders(state);
	if (r) abort();
    }

    return pos;
}

static int folder_number_rename(struct conversations_state *state,
				const char *from_name,
				const char *to_name)
{
    int pos = strarray_find(state->folder_names, from_name, 0);

    if (pos < 0) return 0; /* nothing to do! */

    /* replace the name  - set to '-' if deleted */
    strarray_set(state->folder_names, pos, to_name ? to_name : "-");

    return write_folders(state);
}

int conversation_storestatus(struct conversations_state *state,
			     const char *key, size_t keylen,
			     modseq_t modseq,
			     uint32_t exists,
			     uint32_t unseen)
{
    struct dlist *dl = NULL;
    struct buf buf = BUF_INITIALIZER;
    int version = CONVERSATIONS_VERSION;
    int r;

    dl = dlist_newlist(NULL, NULL);
    dlist_setnum64(dl, "MODSEQ", modseq);
    dlist_setnum32(dl, "EXISTS", exists);
    dlist_setnum32(dl, "UNSEEN", unseen);

    buf_printf(&buf, "%d ", version);
    dlist_printbuf(dl, 0, &buf);
    dlist_free(&dl);

    r = cyrusdb_store(state->db,
		      key, keylen,
		      buf.s, buf.len,
		      &state->txn);

    buf_free(&buf);

    return r;
}

int conversation_setstatus(struct conversations_state *state,
			   const char *mboxname,
			   modseq_t modseq,
			   uint32_t exists,
			   uint32_t unseen)
{
    char *key = strconcat("F", mboxname, (char *)NULL);
    int r;

    r = conversation_storestatus(state, key, strlen(key),
				 modseq, exists, unseen);

    free(key);

    return r;
}

int conversation_store(struct conversations_state *state,
		       const char *key, int keylen,
		       conversation_t *conv)
{
    struct dlist *dl, *n, *nn;
    struct buf buf = BUF_INITIALIZER;
    const conv_folder_t *folder;
    const conv_sender_t *sender;
    int version = CONVERSATIONS_VERSION;
    int i;
    int r;

    dl = dlist_newlist(NULL, NULL);
    dlist_setnum64(dl, "MODSEQ", conv->modseq);
    dlist_setnum32(dl, "NUMRECORDS", conv->num_records);
    dlist_setnum32(dl, "EXISTS", conv->exists);
    dlist_setnum32(dl, "UNSEEN", conv->unseen);
    n = dlist_newlist(dl, "COUNTS");
    if (state->counted_flags) {
	for (i = 0; i < state->counted_flags->count; i++) {
	    const char *flag = strarray_nth(state->counted_flags, i);
	    dlist_setnum32(n, flag, conv->counts[i]);
	}
    }

    n = dlist_newlist(dl, "FOLDER");
    for (folder = conv->folders ; folder ; folder = folder->next) {
	if (!folder->num_records)
	    continue;
	nn = dlist_newlist(n, "FOLDER");
	dlist_setnum32(nn, "FOLDERNUM", folder->number);
	dlist_setnum64(nn, "MODSEQ", folder->modseq);
	dlist_setnum32(nn, "NUMRECORDS", folder->num_records);
	dlist_setnum32(nn, "EXISTS", folder->exists);
    }

    n = dlist_newlist(dl, "SENDER");
    for (sender = conv->senders ; sender ; sender = sender->next) {
	/* there's no refcounting of senders, they last forever */
	nn = dlist_newlist(n, "SENDER");
	/* envelope form */
	dlist_setatom(nn, "NAME", sender->name);
	dlist_setatom(nn, "ROUTE", sender->route);
	dlist_setatom(nn, "MAILBOX", sender->mailbox);
	dlist_setatom(nn, "DOMAIN", sender->domain);
    }

    buf_printf(&buf, "%d ", version);
    dlist_printbuf(dl, 0, &buf);
    dlist_free(&dl);

    if (_sanity_check_counts(conv)) {
	syslog(LOG_ERR, "IOERROR: conversations_audit on store: %s %.*s %.*s",
	       state->path, keylen, key, buf.len, buf.s);
    }

    r = cyrusdb_store(state->db, key, keylen, buf.s, buf.len, &state->txn);

    buf_free(&buf);

    return r;
}

static int _conversation_save(struct conversations_state *state,
			      const char *key, int keylen,
			      conversation_t *conv)
{
    const conv_folder_t *folder;
    int r;

    /* see if any 'F' keys need to be changed */
    for (folder = conv->folders ; folder ; folder = folder->next) {
	const char *mboxname = strarray_nth(state->folder_names, folder->number);
	int exists_diff = 0;
	int unseen_diff = 0;
	modseq_t modseq;
	uint32_t exists;
	uint32_t unseen;

	/* case: full removal of conversation - make sure to remove
	 * unseen as well */
	if (folder->exists) {
	    if (folder->prev_exists) {
		/* both exist, just check for unseen changes */
		unseen_diff = !!conv->unseen - !!conv->prev_unseen;
	    }
	    else {
		/* adding, check if it's unseen */
		exists_diff = 1;
		if (conv->unseen) unseen_diff = 1;
	    }
	}
	else if (folder->prev_exists) {
	    /* removing, check if it WAS unseen */
	    exists_diff = -1;
	    if (conv->prev_unseen) unseen_diff = -1;
	}
	else {
	    /* we don't care about unseen if the cid is not registered
	     * in this folder, and wasn't previously either */
	}

	/* XXX - it's super inefficient to be doing this for
	 * every cid in every folder in the transaction.  Big
	 * wins available by caching these in memory and writing
	 * once at the end of the transaction */
	r = conversation_getstatus(state, mboxname,
				   &modseq, &exists, &unseen);
	if (r) goto done;
	if (exists_diff || unseen_diff || modseq < conv->modseq) {
	    if (modseq < conv->modseq) modseq = conv->modseq;
	    exists += exists_diff;
	    unseen += unseen_diff;
	    r = conversation_setstatus(state, mboxname,
				       modseq, exists, unseen);
	    if (r) goto done;
	}
    }

    if (!conv->num_records) {
	/* last existing record removed - clean up the 'B' record */
	r = cyrusdb_delete(state->db, key, keylen, &state->txn, 1);
	if (!r) {
	    /* and the 'S' record too */
	    char *skey = xstrndup(key, keylen);
	    skey[0] = 'S';
	    r = cyrusdb_delete(state->db, skey, keylen, &state->txn, 1);
	    free(skey);
	}
	goto done;
    }

    r = conversation_store(state, key, keylen, conv);

done:
    if (!r)
	conv->dirty = 0;

    return r;
}

int conversation_save(struct conversations_state *state,
		      conversation_id_t cid,
		      conversation_t *conv)
{
    char bkey[CONVERSATION_ID_STRMAX+2];

    if (!conv)
	return IMAP_INTERNAL;
    if (!conv->dirty)
	return 0;

    /* old pre-conversations message, nothing to do */
    if (!cid)
	return 0;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);

    return _conversation_save(state, bkey, strlen(bkey), conv);
}

int conversation_parsestatus(const char *data, size_t datalen,
			     modseq_t *modseqp,
			     uint32_t *existsp,
			     uint32_t *unseenp)
{
    bit64 version;
    const char *rest;
    size_t restlen;
    struct dlist *dl = NULL;
    struct dlist *n;
    int r;

    r = parsenum(data, &rest, datalen, &version);
    if (r) return r;

    if (rest[0] != ' ')
	return IMAP_MAILBOX_BADFORMAT;
    rest++; /* skip space */
    restlen = datalen - (rest - data);

    if (version != CONVERSATIONS_VERSION) {
	/* XXX - an error code for "incorrect version"? */
	return IMAP_MAILBOX_BADFORMAT;
    }

    r = dlist_parsemap(&dl, 0, rest, restlen);
    if (r) return r;

    n = dlist_getchildn(dl, 0);
    if (modseqp && n)
	*modseqp = dlist_num(n);
    n = dlist_getchildn(dl, 1);
    if (existsp && n)
	*existsp = dlist_num(n);
    n = dlist_getchildn(dl, 2);
    if (unseenp && n)
	*unseenp = dlist_num(n);

    dlist_free(&dl);
    return 0;
}

int conversation_getstatus(struct conversations_state *state,
			   const char *mboxname,
			   modseq_t *modseqp,
			   uint32_t *existsp,
			   uint32_t *unseenp)
{
    char *key = strconcat("F", mboxname, (char *)NULL);
    const char *data;
    size_t datalen;
    int r = IMAP_IOERROR;

    if (modseqp) *modseqp = 0;
    if (existsp) *existsp = 0;
    if (unseenp) *unseenp = 0;

    if (!state->db)
	goto done;

    r = cyrusdb_fetch(state->db,
		      key, strlen(key),
		      &data, &datalen,
		      &state->txn);

    if (r == CYRUSDB_NOTFOUND) {
	/* not existing is not an error */
	r = 0;
	goto done;
    }
    if (r) goto done;

    r = conversation_parsestatus(data, datalen, modseqp, existsp, unseenp);

 done:
    if (r)
	syslog(LOG_ERR, "IOERROR: conversations invalid status %s", mboxname);

    free(key);

    return r;
}

static conv_folder_t *conversation_get_folder(conversation_t *conv,
					      int number, int create_flag)
{
    conv_folder_t *folder, **nextp = &conv->folders;

    if (number < 0)
	return NULL;

    /* first check if it already exists */
    for (folder = conv->folders ; folder ; folder = folder->next) {
	if (folder->number < number)
	    nextp = &folder->next;
	else if (folder->number == number)
	    return folder;
	else
	    break;
    }

    if (!create_flag)
	return NULL;

    /* not found, create a new one */
    folder = xzmalloc(sizeof(*folder));
    folder->number = number;
    folder->next = *nextp;
    *nextp = folder;
    conv->dirty = 1;

    return folder;
}

int conversation_parse(struct conversations_state *state,
		       const char *data, size_t datalen,
		       conversation_t **convp)
{
    const char *rest;
    int i;
    int restlen;
    bit64 version;
    struct dlist *dl = NULL;
    struct dlist *n, *nn;
    conversation_t *conv;
    conv_folder_t *folder;
    int r;

    r = parsenum(data, &rest, datalen, &version);
    if (r) {
	*convp = NULL;
	return 0;
    }

    if (rest[0] != ' ') {
	*convp = NULL;
	return 0;
    }
    rest++; /* skip space */
    restlen = datalen - (rest - data);

    if (version != CONVERSATIONS_VERSION) {
	*convp = NULL;
	return 0;
    }

    r = dlist_parsemap(&dl, 0, rest, restlen);
    if (r) return r;

    conv = conversation_new(state);

    n = dlist_getchildn(dl, 0);
    if (n)
	conv->modseq = dlist_num(n);
    n = dlist_getchildn(dl, 1);
    if (n)
	conv->num_records = dlist_num(n);
    n = dlist_getchildn(dl, 2);
    if (n)
	conv->exists = dlist_num(n);
    n = dlist_getchildn(dl, 3);
    if (n)
	conv->unseen = dlist_num(n);
    n = dlist_getchildn(dl, 4);
    if (state->counted_flags) {
	nn = n ? n->head : NULL;
	for (i = 0; i < state->counted_flags->count; i++) {
	    if (nn) {
		conv->counts[i] = dlist_num(nn);
		nn = nn->next;
	    }
	    else
		conv->counts[i] = 0;
	}
    }

    n = dlist_getchildn(dl, 5);
    for (n = (n ? n->head : NULL) ; n ; n = n->next) {
	int number;
	nn = dlist_getchildn(n, 0);
	if (!nn)
	    continue;
	number = dlist_num(nn);
	folder = conversation_get_folder(conv, number, 1);

	nn = dlist_getchildn(n, 1);
	if (nn)
	    folder->modseq = dlist_num(nn);
	nn = dlist_getchildn(n, 2);
	if (nn)
	    folder->num_records = dlist_num(nn);
	nn = dlist_getchildn(n, 3);
	if (nn)
	    folder->exists = dlist_num(nn);

	folder->prev_exists = folder->exists;
    }

    n = dlist_getchildn(dl, 6);
    for (n = (n ? n->head : NULL) ; n ; n = n->next) {
	struct dlist *nn2, *nn3, *nn4;
	nn = dlist_getchildn(n, 0);
	nn2 = dlist_getchildn(n, 1);
	nn3 = dlist_getchildn(n, 2);
	nn4 = dlist_getchildn(n, 3);
	if (nn3 && nn4)
	    conversation_add_sender(conv,
				    nn->sval, nn2->sval,
				    nn3->sval, nn4->sval);
    }

    conv->prev_unseen = conv->unseen;

    dlist_free(&dl);
    conv->dirty = 0;
    *convp = conv;
    return 0;
}

int conversation_load(struct conversations_state *state,
		      conversation_id_t cid,
		      conversation_t **convp)
{
    const char *data;
    size_t datalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    int r;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);
    r = cyrusdb_fetch(state->db,
		  bkey, strlen(bkey),
		  &data, &datalen,
		  &state->txn);

    if (r == CYRUSDB_NOTFOUND) {
	*convp = NULL;
	return 0;
    } else if (r != CYRUSDB_OK) {
	return r;
    }

    r = conversation_parse(state, data, datalen, convp);
    if (r) {
	syslog(LOG_ERR, "IOERROR: conversations invalid conversation "
	       CONV_FMT, cid);
	*convp = NULL;
    }

    if (_sanity_check_counts(*convp)) {
	syslog(LOG_ERR, "IOERROR: conversations_audit on load: %s %s %.*s",
	       state->path, bkey, (int)datalen, data);
    }

    return 0;
}

/* Parse just enough of the B record to retrieve the modseq.
 * Fortunately the modseq is the first field after the record version
 * number, given the way that _conversation_save() and dlist works.  See
 * _conversation_load() for the full shebang. */
static int _conversation_load_modseq(const char *data, int datalen,
				     modseq_t *modseqp)
{
    const char *p = data;
    const char *end = data + datalen;
    bit64 version = ~0ULL;
    int r;

    r = parsenum(p, &p, (end-p), &version);
    if (r || version != CONVERSATIONS_VERSION)
	return IMAP_INTERNAL;

    if ((end - p) < 4 || p[0] != ' ' || p[1] != '(')
	return IMAP_INTERNAL;
    p += 2; /* skip space and left parenthesis */

    r = parsenum(p, &p, (end-p), modseqp);
    if ((end - p) < 1 || *p != ' ')
	return IMAP_INTERNAL;

    return 0;
}

int conversation_get_modseq(struct conversations_state *state,
			    conversation_id_t cid,
			    modseq_t *modseqp)
{
    const char *data;
    size_t datalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    int r;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);
    r = cyrusdb_fetch(state->db,
		  bkey, strlen(bkey),
		  &data, &datalen,
		  &state->txn);

    if (r == CYRUSDB_NOTFOUND) {
	*modseqp = 0;
	return 0;
    } else if (r != CYRUSDB_OK) {
	return r;
    }

    r = _conversation_load_modseq(data, datalen, modseqp);
    if (r) {
	syslog(LOG_ERR, "IOERROR: conversation_get_modseq: invalid conversation "
	       CONV_FMT, cid);
	*modseqp = 0;
    }

    return 0;
}

conv_folder_t *conversation_find_folder(struct conversations_state *state,
					conversation_t *conv,
					const char *mboxname)
{
    int number = folder_number(state, mboxname, /*create*/0);
    return conversation_get_folder(conv, number, /*create*/0);
}

/* Compare a sender vs a new sender key (mailbox and domain).
 * Returns 0 if identical, nonzero if different (sign indicates
 * sort order, like strcmp()).
 *
 * This is not quite RFC compliant: we are comparing the
 * localpart case insensitively even though the RFC says the
 * interpretation is up to the domain itself.  However this
 * seems to yield better results. [IRIS-1484] */
static int sender_cmp(const conv_sender_t *sender,
		      const char *mailbox,
		      const char *domain)
{
    int d = strcasecmp(sender->domain, domain);
    if (!d)
	d = strcasecmp(sender->mailbox, mailbox);
    return d;
}

/* Choose a preferred mailbox. Returns <0 if @a is preferred,
 * 0 if we don't care, and >0 if @b is preferred */
static int sender_preferred_mailbox(const char *a, const char *b)
{
    /* choosing the lexically earlier string tends to keep
     * capital letters, which is an arbitrary asthetic */
    return strcmp(a, b);
}

/* Choose a preferred domain. Returns <0 if @a is preferred,
 * 0 if we don't care, and >0 if @b is preferred */
static int sender_preferred_domain(const char *a, const char *b)
{
    /* choosing the lexically earlier string tends to keep
     * capital letters, which is an arbitrary asthetic */
    return strcmp(a, b);
}

static int has_non_ascii(const char *s)
{
    for ( ; *s ; s++) {
	if (*(unsigned char *)s > 0x7f)
	    return 1;
    }
    return 0;
}

/* Choose a preferred name. Returns <0 if @a is preferred,
 * 0 if we don't care, and >0 if @b is preferred */
static int sender_preferred_name(const char *a, const char *b)
{
    int d;
    char *sa = NULL;
    char *sb = NULL;

    sa = charset_parse_mimeheader((a ? a : ""));
    sb = charset_parse_mimeheader((b ? b : ""));

    /* A name with characters > 0x7f is preferred to a flat
     * ascii one, on the assumption that this is more likely to
     * contain an actual name rather than a romanisation. */
    d = has_non_ascii(sb) - has_non_ascii(sa);

    /* A longer name is preferred over a shorter. */
    if (!d)
	d = strlen(sb) - strlen(sa);

    /* The lexically earlier name is preferred (earlier on the grounds
     * that's more likely to start with a capital letter) */
    if (!d)
	d = strcmp(sa, sb);

    free(sa);
    free(sb);
    return d;
}

void conversation_add_sender(conversation_t *conv,
			     const char *name,
			     const char *route,
			     const char *mailbox,
			     const char *domain)
{
    conv_sender_t *sender, **nextp = &conv->senders;

    if (!mailbox || !domain) return;

    for (sender = conv->senders; sender; sender = sender->next) {
	if (!sender_cmp(sender, mailbox, domain)) {
	    /* found it.  To ensure the database is consistent regardless
	     * of message arrival order, update the record if the newly
	     * seen values are more preferred */
	    if (sender_preferred_mailbox(sender->mailbox, mailbox) > 0) {
		free(sender->mailbox);
		sender->mailbox = xstrdup(mailbox);
		conv->dirty = 1;
	    }

	    if (sender_preferred_domain(sender->domain, domain) > 0) {
		free(sender->domain);
		sender->domain = xstrdup(domain);
		conv->dirty = 1;
	    }

	    if (sender_preferred_name(sender->name, name) > 0) {
		free(sender->name);
		/* a NULL name should never be *more* preferred
		 * than any other name */
		assert(name);
		sender->name = xstrdup(name);
		conv->dirty = 1;
	    }
	    return;
	}
    }

    /* second pass so we don't break on unordered data */
    for (sender = conv->senders; sender; sender = sender->next) {
	if (sender_cmp(sender, mailbox, domain) > 0)
	    break;
	nextp = &sender->next;
    }

    sender = xzmalloc(sizeof(*sender));
    if (name) sender->name = xstrdup(name);
    if (route) sender->route = xstrdup(route);
    sender->mailbox = xstrdup(mailbox);
    sender->domain = xstrdup(domain);
    sender->next = *nextp;
    *nextp = sender;

    conv->dirty = 1;
}

static void _apply_delta(uint32_t *valp, int delta)
{
    if (delta >= 0) {
	*valp += delta;
    }
    else {
	uint32_t decrease = -delta;
	/* let us die where it broke */
	assert (decrease <= *valp);
	*valp -= decrease;
    }
}

void conversation_update(struct conversations_state *state,
			 conversation_t *conv, const char *mboxname,
			 int delta_num_records,
			 int delta_exists, int delta_unseen,
			 int *delta_counts, modseq_t modseq)
{
    conv_folder_t *folder;
    int number = folder_number(state, mboxname, /*create*/1);
    int i;

    folder = conversation_get_folder(conv, number, /*create*/1);

    if (delta_num_records) {
	_apply_delta(&conv->num_records, delta_num_records);
	_apply_delta(&folder->num_records, delta_num_records);
	conv->dirty = 1;
    }
    if (delta_exists) {
	_apply_delta(&conv->exists, delta_exists);
	_apply_delta(&folder->exists, delta_exists);
	conv->dirty = 1;
    }
    if (delta_unseen) {
	_apply_delta(&conv->unseen, delta_unseen);
	conv->dirty = 1;
    }
    if (state->counted_flags) {
	for (i = 0; i < state->counted_flags->count; i++) {
	    if (delta_counts[i]) {
		_apply_delta(&conv->counts[i], delta_counts[i]);
		conv->dirty = 1;
	    }
	}
    }
    if (modseq > conv->modseq) {
	conv->modseq = modseq;
	conv->dirty = 1;
    }
    if (modseq > folder->modseq) {
	folder->modseq = modseq;
	conv->dirty = 1;
    }
}

conversation_t *conversation_new(struct conversations_state *state)
{
    conversation_t *conv;

    conv = xzmalloc(sizeof(conversation_t));
    if (state->counted_flags)
	conv->counts = xzmalloc(sizeof(uint32_t) * state->counted_flags->count);
    conv->dirty = 1;

    return conv;
}

void conversation_free(conversation_t *conv)
{
    conv_folder_t *folder;
    conv_sender_t *sender;

    if (!conv) return;

    while ((folder = conv->folders)) {
	conv->folders = folder->next;
	free(folder);
    }

    while ((sender = conv->senders)) {
	conv->senders = sender->next;
	free(sender->name);
	free(sender->route);
	free(sender->mailbox);
	free(sender->domain);
	free(sender);
    }

    free(conv->counts);
    free(conv);
}


struct prune_rock {
    struct conversations_state *state;
    time_t thresh;
    unsigned int nseen;
    unsigned int ndeleted;
};

static int prunecb(void *rock,
		   const char *key, size_t keylen,
		   const char *data, size_t datalen)
{
    struct prune_rock *prock = (struct prune_rock *)rock;
    conversation_id_t cid;
    time_t stamp;
    int r;

    prock->nseen++;
    r = check_msgid(key, keylen, NULL);
    if (r) return r;

    r = _conversations_parse(data, datalen, &cid, &stamp);
    if (r) return r;

    /* keep records newer than the threshold */
    if (stamp >= prock->thresh)
	return 0;

    prock->ndeleted++;

    return cyrusdb_delete(prock->state->db,
		      key, keylen,
		      &prock->state->txn,
		      /*force*/1);
}

int conversations_prune(struct conversations_state *state,
			time_t thresh, unsigned int *nseenp,
			unsigned int *ndeletedp)
{
    struct prune_rock rock = { state, thresh, 0, 0 };

    cyrusdb_foreach(state->db, "<", 1, NULL, prunecb, &rock, &state->txn);

    if (nseenp)
	*nseenp = rock.nseen;
    if (ndeletedp)
	*ndeletedp = rock.ndeleted;

    return 0;
}

/* NOTE: this makes an "ATOM" return */
const char *conversation_id_encode(conversation_id_t cid)
{
    static char text[2*sizeof(cid)+1];

    if (cid != NULLCONVERSATION) {
	snprintf(text, sizeof(text), CONV_FMT, cid);
    } else {
	strncpy(text, "NIL", sizeof(text));
    }

    return text;
}

int conversation_id_decode(conversation_id_t *cid, const char *text)
{
    if (!strcmp(text, "NIL")) {
	*cid = NULLCONVERSATION;
    } else {
	if (strlen(text) != 16) return 0;
	*cid = strtoull(text, 0, 16);
    }
    return 1;
}

struct rename_rock {
    struct conversations_state *state;
    conversation_id_t from_cid;
    conversation_id_t to_cid;
    unsigned long entries_seen;
    unsigned long entries_renamed;
};

static int do_one_rename(void *rock,
		         const char *key, size_t keylen,
		         const char *data, size_t datalen)
{
    struct rename_rock *rrock = (struct rename_rock *)rock;
    conversation_id_t cid;
    time_t stamp;
    int r;

    r = check_msgid(key, keylen, NULL);
    if (r) return r;

    r = _conversations_parse(data, datalen, &cid, &stamp);
    if (r) return r;

    rrock->entries_seen++;

    if (cid != rrock->from_cid)
	return 0;	/* nothing to see, move along */

    rrock->entries_renamed++;

    return _conversations_set_key(rrock->state, key, keylen,
				  rrock->to_cid, stamp);
}

int conversations_rename_cid(struct conversations_state *state,
			     conversation_id_t from_cid,
			     conversation_id_t to_cid)
{
    struct rename_rock rrock;
    conv_folder_t *folder = NULL;
    conversation_t *conv = NULL;
    int r = 0;

    if (!from_cid)
	return 0;

    if (from_cid == to_cid)
	return 0;

    /* we never rename down! */
    assert(from_cid < to_cid);

    memset(&rrock, 0, sizeof(rrock));
    rrock.state = state;
    rrock.from_cid = from_cid;
    rrock.to_cid = to_cid;

    cyrusdb_foreach(state->db, "<", 1, NULL, do_one_rename, &rrock, &state->txn);

    syslog(LOG_NOTICE, "conversations_rename_cid: saw %lu entries, renamed %lu"
		       " from " CONV_FMT " to " CONV_FMT,
			rrock.entries_seen, rrock.entries_renamed,
			from_cid, to_cid);

    /* Rename the 'S' record for the CID */
    r = conversation_rename_sub(state, from_cid, to_cid);

    /* Use the B record to find the mailboxes for a CID rename.
     * The rename events will decrease the NUM_RECORDS count back
     * to zero, and the record will delete itself! */
    r = conversation_load(state, from_cid, &conv);
    if (r) return r;
    if (!conv) return 0;

    for (folder = conv->folders ; folder ; folder = folder->next) {
	const char *mboxname = strarray_nth(state->folder_names, folder->number);
	/* use the hacky 'findopen' to get any existing mailbox
	 * directly, regardless of where we came in */
	struct mailbox *mailbox = mailbox_findopen(mboxname);

	if (mailbox) {
	    r = mailbox_cid_rename(mailbox, from_cid, to_cid);
	    if (r) return r;
	}
	else {
	    r = mailbox_open_iwl(mboxname, &mailbox);
	    if (r) return r;

	    r = mailbox_cid_rename(mailbox, from_cid, to_cid);
	    if (r) return r;

	    mailbox_close(&mailbox);
	}
    }

    conversation_free(conv);

    /* XXX - COULD try to read the B key and confirm that it doesn't exist any more... */

    return 0;
}

static int folder_key_rename(struct conversations_state *state,
			     const char *from_name,
			     const char *to_name)
{
    const char *val;
    size_t vallen;
    char *oldkey = strconcat("F", from_name, (void *)NULL);
    int r = 0;

    r = cyrusdb_fetch(state->db, oldkey, strlen(oldkey),
		      &val, &vallen, &state->txn);
    if (r) {
	if (r == CYRUSDB_NOTFOUND) r = 0; /* nothing to delete */
	goto done;
    }

    /* create before deleting so val is still valid */
    if (to_name) {
	char *newkey = strconcat("F", to_name, (void *)NULL);
	r = cyrusdb_store(state->db, newkey, strlen(newkey),
			  val, vallen, &state->txn);
	free(newkey);
	if (r) goto done;
    }

    r = cyrusdb_delete(state->db, oldkey, strlen(oldkey), &state->txn, 1);

 done:
    free(oldkey);

    return r;
}

int conversations_rename_folder(struct conversations_state *state,
			        const char *from_name,
			        const char *to_name)
{
    int r;

    assert(from_name);

    r = folder_number_rename(state, from_name, to_name);
    if (r) return r;

    r = folder_key_rename(state, from_name, to_name);
    if (r) return r;

    if (to_name) {
	syslog(LOG_NOTICE, "conversations_rename_folder: renamed %s to %s",
	       from_name, to_name);
    }
    else {
	syslog(LOG_NOTICE, "conversations_rename_folder: deleted %s",
	       from_name);
    }

    return 0;
}


static int delete_cb(void *rock,
		     const char *key,
		     size_t keylen,
		     const char *val __attribute__((unused)),
		     size_t vallen __attribute__((unused)))
{
    struct conversations_state *state = (struct conversations_state *)rock;
    return cyrusdb_delete(state->db, key, keylen, &state->txn, 1);
}

int conversations_wipe_counts(struct conversations_state *state,
			      int keepnames)
{
    int r = 0;

    /* wipe B counts */
    r = cyrusdb_foreach(state->db, "B", 1, NULL, delete_cb,
			state, &state->txn);
    if (r) return r;

    /* wipe F counts */
    r = cyrusdb_foreach(state->db, "F", 1, NULL, delete_cb,
			state, &state->txn);
    if (r) return r;

    /* wipe S keys */
    r = cyrusdb_foreach(state->db, "S", 1, NULL, delete_cb,
			state, &state->txn);
    if (r) return r;

    if (!keepnames) {
	/* remove folder names */
	strarray_truncate(state->folder_names, 0);
	r = write_folders(state);
	if (r) return r;
    }

    /* re-init the counted flags */
    r = _init_counted(state, NULL, 0);
    if (r) return r;

    return r;
}

void conversations_dump(struct conversations_state *state, FILE *fp)
{
    cyrusdb_dumpfile(state->db, "", 0, fp, &state->txn);
}

int conversations_truncate(struct conversations_state *state)
{
    return cyrusdb_truncate(state->db, &state->txn);
}

int conversations_undump(struct conversations_state *state, FILE *fp)
{
    return cyrusdb_undumpfile(state->db, fp, &state->txn);
}



#undef DB
