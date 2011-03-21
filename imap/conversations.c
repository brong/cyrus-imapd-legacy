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

#define DB config_conversations_db


char *conversations_getpath(const char *mboxname)
{
    struct mboxname_parts parts;
    char *fname;

    if (mboxname_to_parts(mboxname, &parts))
	return NULL;

    fname = mboxname_conf_getpath(&parts, FNAME_CONVERSATIONS_SUFFIX);

    mboxname_free_parts(&parts);
    return fname;
}


int conversations_open(struct conversations_state *state, const char *fname)
{
    int r;

    if (!fname)
	return IMAP_MAILBOX_BADNAME;
    memset(state, 0, sizeof(*state));

    r = DB->open(fname, CYRUSDB_CREATE, &state->db);
    if (r || state->db == NULL)
	return IMAP_IOERROR;

    return 0;
}

int conversations_close(struct conversations_state *state)
{
    if (state->txn != NULL) {
	DB->abort(state->db, state->txn);
	state->txn = NULL;
    }
    if (state->db != NULL) {
	DB->close(state->db);
	state->db = NULL;
    }
    return 0;
}

int conversations_commit(struct conversations_state *state)
{
    int r = 0;

    if (state->db != NULL && state->txn != NULL) {
	r = DB->commit(state->db, state->txn);
	state->txn = NULL;
    }

    return r;
}

static int check_msgid(const char *msgid, int len, int *lenp)
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
				  const char *key, int keylen,
				  conversation_id_t cid, time_t stamp)
{
    int r;
    struct buf buf;

    buf_init(&buf);

    if (state->db == NULL)
	return IMAP_IOERROR;

    buf_printf(&buf, CONV_FMT " %lu", cid, stamp);

    r = DB->store(state->db,
		  key, keylen,
		  buf.s, buf.len,
		  &state->txn);

    buf_free(&buf);
    if (r)
	return IMAP_IOERROR;

    return 0;
}

int conversations_set_msgid(struct conversations_state *state,
			  const char *msgid,
			  conversation_id_t cid)
{
    int keylen;
    int r;

    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    return _conversations_set_key(state, msgid, keylen, cid, time(NULL));
}

static int _conversations_parse(const char *data, int datalen,
				conversation_id_t *cidp, time_t *stampp)
{ 
    const char *rest;
    int r;
    bit64 tval;

    r = parsehex(data, &rest, 16, cidp);
    if (r) return IMAP_MAILBOX_BADFORMAT;

    /* should have parsed exactly 16 characters */
    if (rest != data + 16)
	return IMAP_MAILBOX_BADFORMAT;

    /* next character is a space */
    if (rest[0] != ' ')
	return IMAP_MAILBOX_BADFORMAT;

    r = parsenum(rest+1, &rest, datalen-17, &tval);
    if (r) return IMAP_MAILBOX_BADFORMAT;

    /* should have parsed to the end of the string */
    if (rest - data != datalen)
	return IMAP_MAILBOX_BADFORMAT;

    if (stampp) *stampp = tval;

    return 0;
}

int conversations_get_msgid(struct conversations_state *state,
		          const char *msgid,
		          conversation_id_t *cidp)
{
    int keylen;
    int datalen = 0;
    const char *data;
    int r;

    if (state->db == NULL)
	return IMAP_IOERROR;
    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    r = DB->fetch(state->db,
		  msgid, keylen,
		  &data, &datalen,
		  &state->txn);

    if (!r) r = _conversations_parse(data, datalen, cidp, NULL);

    if (r) *cidp = NULLCONVERSATION;

    return 0;
}

int conversations_update(struct conversations_state *state,
			 struct mailbox *mailbox,
			 struct index_record *old,
			 struct index_record *new)
{
    const char *bdata;
    int bdatalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    struct dlist *data = NULL;
    struct dlist *hl = NULL;
    struct dlist *el = NULL;
    struct dlist *ul = NULL;
    struct dlist *dl = NULL;
    struct dlist *fl = NULL;
    struct dlist *ml = NULL;
    struct dlist *mhl = NULL;
    struct dlist *mel = NULL;
    struct dlist *sl = NULL;
    struct dlist *sel = NULL;
    struct dlist *enl = NULL;
    struct dlist *eel = NULL;
    struct buf buf = BUF_INITIALIZER;
    int r = 0;
    char *envtokens[NUMENVTOKENS];
    struct address addr = { NULL, NULL, NULL, NULL, NULL, NULL };
    char *env = NULL;
    char *email = NULL;
    struct index_record *record;

    if (old && new) assert(old->cid == new->cid);

    record = new ? new : old;

    modseq_t oldh, newh;
    uint32_t olde, newe;
    uint32_t oldu, newu;
    uint32_t oldd, newd;
    modseq_t oldmh, newmh;
    uint32_t oldme, newme;
    uint32_t oldee, newee;

    if (!state->db)
	return IMAP_IOERROR;

    if (!mailbox_cacherecord(mailbox, record)) {
	/* +1 -> skip the leading paren */
	env = xstrndup(cacheitem_base(new, CACHE_ENVELOPE) + 1,
		       cacheitem_size(new, CACHE_ENVELOPE) - 1);

	parse_cached_envelope(env, envtokens, VECTOR_SIZE(envtokens));

	if (envtokens[ENV_FROM]) /* paranoia */
	    message_parse_env_address(envtokens[ENV_FROM], &addr);

	if (addr.mailbox && addr.domain)
	    email = strconcat(addr.mailbox, "@", addr.domain, (char *)NULL);
    }

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, record->cid);
    r = DB->fetch(state->db,
		  bkey, strlen(bkey),
		  &bdata, &bdatalen,
		  &state->txn);

    if (r == CYRUSDB_OK)
    {
	/* found an existing record */
	dlist_parsemap(&data, 0, bdata, bdatalen);
	if (data) {
	    hl = dlist_getchild(data, "MODSEQ");
	    el = dlist_getchild(data, "EXISTS");
	    ul = dlist_getchild(data, "UNSEEN");
	    dl = dlist_getchild(data, "DRAFTS");
	    fl = dlist_getchild(data, "FOLDER");
	    for (ml = fl->head; ml; ml = ml->next) {
		struct dlist *tmpl = dlist_getchild(ml, "MBOXNAME");
		if (tmpl && !strcmp(tmpl->sval, mailbox->name))
		    break;
	    }
	    sl = dlist_getchild(data, "SENDER");
	    if (email) {
		for (sel = sl->head; sel; sel = sel->next) {
		    struct dlist *tmpl = dlist_getchild(sel, "EMAIL");
		    if (tmpl && !strcmp(tmpl->sval, email))
			break;
		}
	    }
	    
	}
    } else if (r != CYRUSDB_NOTFOUND) {
	return r;	/* some db error */
    }

    /* create if not exists */
    if (!data) data = dlist_kvlist(NULL, NULL);
    if (!hl) hl = dlist_modseq(data, "MODSEQ", 0);
    if (!el) el = dlist_num(data, "EXISTS", 0);
    if (!ul) ul = dlist_num(data, "UNSEEN", 0);
    if (!dl) dl = dlist_num(data, "DRAFTS", 0);
    if (!fl) fl = dlist_list(data, "FOLDER");
    if (!ml) {
	ml = dlist_kvlist(fl, "FOLDER");
	dlist_atom(ml, "MBOXNAME", mailbox->name);
    }
    mhl = dlist_getchild(ml, "MODSEQ");
    mel = dlist_getchild(ml, "EXISTS");
    if (!mhl) mhl = dlist_modseq(ml, "MODSEQ", 0);
    if (!mel) mel = dlist_num(ml, "EXISTS", 0);

    /* sender stuff */
    if (email) {
	if (!sl) sl = dlist_list(data, "SENDER");
	if (!sel) {
	    sel = dlist_kvlist(sl, "SENDER");
	    dlist_atom(sel, "EMAIL", email);
	}
	enl = dlist_getchild(sel, "NAME");
	eel = dlist_getchild(sel, "EXISTS");
	if (!enl) enl = dlist_atom(sel, "NAME", addr.name ? addr.name : "");
	/* case: cached value no name and we have a name now */
	if (addr.name && !strcmp(enl->sval, "")) {
	    free(enl->sval);
	    enl->sval = xstrdup(addr.name);
	}
	if (!eel) eel = dlist_num(sel, "EXISTS", 0);
    }

    newh  = oldh  = dlist_modseqval(hl);
    newe  = olde  = dlist_nval(el);
    newu  = oldu  = dlist_nval(ul);
    newd  = oldd  = dlist_nval(dl);
    newmh = oldmh = dlist_modseqval(mhl);
    newme = oldme = dlist_nval(mel);
    if (email) newee = oldee = dlist_nval(eel);

    /* apply the changes */
    if (old) {
	/* decrease any relevent counts */
	if (!(old->system_flags & FLAG_EXPUNGED)) {
	    newe--;
	    newme--;
	    if (email) newee--;
	    if (!(old->system_flags & FLAG_SEEN))
		newu--;
	    if (old->system_flags & FLAG_DRAFT)
		newd--;
	}
	if (old->modseq > newh)  newh  = old->modseq;
	if (old->modseq > newmh) newmh = old->modseq;
    }
    /* add any counts */
    if (new) {
	if (!(new->system_flags & FLAG_EXPUNGED)) {
	    newe++;
	    newme++;
	    if (email) newee++;
	    if (!(new->system_flags & FLAG_SEEN))
		newu++;
	    if (new->system_flags & FLAG_DRAFT)
		newd++;
	}
	if (new->modseq > newh)  newh  = new->modseq;
	if (new->modseq > newmh) newmh = new->modseq;
    }

    /* XXX - handle removing zero-count senders, zero count mailboxes,
     * rather than just everything */
    if (newe == 0) {
	r = DB->delete(state->db,
		      bkey, strlen(bkey),
		      &state->txn, /*force*/1);
    }
    else if (newh != oldh || newe != olde || newu != oldu || newd != oldd ||
	     newmh != oldmh || newme != oldme || (email && newee != oldee)) {
	/* skanky in-house modifications */
	hl->nval = newh;
	hl->type = DL_MODSEQ;
	el->nval = newe;
	el->type = DL_NUM;
	ul->nval = newu;
	el->type = DL_NUM;
	dl->nval = newd;
	el->type = DL_NUM;
	mhl->nval = newmh;
	mhl->type = DL_MODSEQ;
	mel->nval = newme;
	mel->type = DL_NUM;
	if (email) {
	    eel->type = DL_NUM;
	    eel->nval = newee;
	}
	dlist_printbuf(data, 0, &buf);
	r = DB->store(state->db,
		      bkey, strlen(bkey),
		      buf.s, buf.len,
		      &state->txn);
    }

    free(env);
    free(email);
    dlist_free(&data);
    buf_free(&buf);
    return r;
}

int conversations_get_data(struct conversations_state *state,
			   conversation_id_t cid,
			   struct dlist **dptr)
{
    const char *bdata;
    int bdatalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    int r;

    if (!state->db)
	return IMAP_IOERROR;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);
    r = DB->fetch(state->db,
		  bkey, strlen(bkey),
		  &bdata, &bdatalen,
		  &state->txn);

    if (r == CYRUSDB_OK) {
	dlist_parsemap(dptr, 0, bdata, bdatalen);
    }
    else if (r == CYRUSDB_NOTFOUND)
	r = 0;

    return r;
}

struct prune_rock {
    struct conversations_state *state;
    time_t thresh;
    unsigned int nseen;
    unsigned int ndeleted;
};

static int prunecb(void *rock,
		   const char *key, int keylen,
		   const char *data, int datalen)
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

    return DB->delete(prock->state->db,
		      key, keylen,
		      &prock->state->txn,
		      /*force*/1);
}

int conversations_prune(struct conversations_state *state,
			time_t thresh, unsigned int *nseenp,
			unsigned int *ndeletedp)
{
    struct prune_rock rock = { state, thresh, 0, 0 };

    DB->foreach(state->db, "<", 1, NULL, prunecb, &rock, &state->txn);

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
		         const char *key, int keylen,
		         const char *data, int datalen)
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
			     conversation_id_t to_cid,
			     conversations_rename_cb_t renamecb,
			     void *rock)
{
    struct rename_rock rrock;
    const char *bdata = NULL;
    int bdatalen = 0;
    char bkey[CONVERSATION_ID_STRMAX+2];
    struct buf buf = BUF_INITIALIZER;
    struct dlist *dl = NULL;
    int r;

    if (!state->db)
	return IMAP_IOERROR;

    memset(&rrock, 0, sizeof(rrock));
    rrock.state = state;
    rrock.from_cid = from_cid;
    rrock.to_cid = to_cid;

    DB->foreach(state->db, "<", 1, NULL, do_one_rename, &rrock, &state->txn);

    syslog(LOG_NOTICE, "conversations_rename_cid: saw %lu entries, renamed %lu",
			rrock.entries_seen, rrock.entries_renamed);

    /* Use the B record to notify mailboxes of a CID rename
     * and rename the B record too */
    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, from_cid);
    r = DB->fetch(state->db,
		  bkey, strlen(bkey),
		  &bdata, &bdatalen,
		  &state->txn);
    if (r == CYRUSDB_NOTFOUND)
	return 0;

    if (r == CYRUSDB_OK && renamecb)
	dlist_parsemap(&dl, 0, bdata, bdatalen);

    r = DB->delete(state->db,
		   bkey, strlen(bkey),
		   &state->txn, /*force*/0);
    if (r)
	goto out;

    dlist_printbuf(dl, 0, &buf);

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, to_cid);

    r = DB->store(state->db,
		  bkey, strlen(bkey),
		  buf.s, buf.len,
		  &state->txn);
    if (r)
	goto out;

    if (dl) {
	struct dlist *fl;
	struct dlist *ditem;
	if (dlist_getlist(dl, "FOLDER", &fl)) {
	    for (ditem = fl->head; ditem; ditem = ditem->next) {
		const char *mboxname;
		if (dlist_getatom(ditem, "MBOXNAME", &mboxname)) {
		    renamecb(mboxname, from_cid, to_cid, rock);
		}
	    }
	}
    }

out:
    dlist_free(&dl);
    buf_free(&buf);
    return r;
}

int conversations_rename_cid_mb(const char *name,
			        conversation_id_t from_cid,
			        conversation_id_t to_cid,
				conversations_rename_cb_t renamecb,
				void *rock)
{
    struct conversations_state state;
    char *path;
    int r;

    path = conversations_getpath(name);
    r = conversations_open(&state, path);
    if (r)
	goto out;

    r = conversations_rename_cid(&state, from_cid, to_cid, renamecb, rock);
    conversations_close(&state);

out:
    free(path);
    return r;
}

void conversations_dump(struct conversations_state *state, FILE *fp)
{
    cyrusdb_dump(DB, state->db, "", 0, fp, &state->txn);
}

int conversations_truncate(struct conversations_state *state)
{
    return cyrusdb_truncate(DB, state->db, &state->txn);
}

int conversations_undump(struct conversations_state *state, FILE *fp)
{
    return cyrusdb_undump(DB, state->db, fp, &state->txn);
}

#undef DB
