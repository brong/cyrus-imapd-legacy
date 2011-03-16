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


/*
 * In-database format of conversations db record message-id
 * record, which is keyed on a message-id (including the <>
 * brackets), e.g. "<123.abc@example.com>".
 *
 * Note that the structure is stored in network order for
 * portability between architecture.  Note also, the structure
 * is carefully defined to avoid implicit padding which might
 * make it's binary format non-portable.
 *
 * Also note that we don't use bit64, as this would actually
 * increase sizeof(mrec) with an invisible 32b pad.
 */
struct conversations_rec {
    conversation_id_t cid; /* conversation ID */
    time_t stamp;	/* time_t insertion timestamp */
};

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
				  struct conversations_rec *rec)
{
    int r;
    struct buf buf;

    buf_init(&buf);

    if (state->db == NULL)
	return IMAP_IOERROR;

    buf_printf(&buf, CONV_FMT " %lu", rec->cid, rec->stamp);

    r = DB->store(state->db,
		  key, keylen,
		  buf.s, buf.len,
		  &state->txn);

    buf_free(&buf);
    if (r)
	return IMAP_IOERROR;

    return 0;
}

static int _conversations_set(struct conversations_state *state,
			      const char *msgid,
			      struct conversations_rec *rec)
{
    int keylen;
    int r;
    struct buf buf;

    buf_init(&buf);

    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    return _conversations_set_key(state, msgid, keylen, rec);
}

int conversations_set_cid(struct conversations_state *state,
			  const char *msgid,
			  conversation_id_t cid)
{
    struct conversations_rec rec;
    rec.cid = cid;
    rec.stamp = time(NULL);
    return _conversations_set(state, msgid, &rec);
}

static int _conversations_parse(const char *data, int datalen,
				struct conversations_rec *rec)
{ 
    const char *rest;
    int r;
    bit64 tval;

    r = parsehex(data, &rest, 16, &rec->cid);
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

    rec->stamp = tval;

    return 0;
}

static int _conversations_get(struct conversations_state *state,
			      const char *msgid,
			      struct conversations_rec *rec)
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

    if (!r) r = _conversations_parse(data, datalen, rec);

    if (r) {
	rec->cid = 0;
	rec->stamp = 0;
    }

    return 0;
}

int conversations_get_cid(struct conversations_state *state,
		          const char *msgid,
		          conversation_id_t *cidp)
{
    struct conversations_rec rec;
    int r;

    r = _conversations_get(state, msgid, &rec);
    if (r) return r;

    *cidp = rec.cid;

    return 0;
}

static void parse_conversation_folders(const char *base, int len,
				       modseq_t *highestmodseq,
				       strarray_t *mboxes)
{
    const char *end = base + len;
    const char *p;

    if (!base || !len)
	return;

    /* make sure strlen() isn't going to run off the end */
    if (base[len-1] != '\0')
	return;	    /* TODO: return an error */

    *highestmodseq = strtoull(base, NULL, 10);

    for (p = base + strlen(base) + 1; p < end; p += strlen(p) + 1)
	strarray_append(mboxes, p);
}

static void build_conversation_folders(modseq_t highestmodseq,
				       const strarray_t *mboxes,
				       struct buf *b)
{
    int i;

    buf_printf(b, "%llu", highestmodseq);
    buf_putc(b, '\0');

    for (i = 0 ; i < mboxes->count ; i++) {
	buf_appendcstr(b, mboxes->data[i]);
	buf_putc(b, '\0');
    }
}

int conversations_set_folder(struct conversations_state *state,
			     conversation_id_t cid,
			     modseq_t highestmodseq,
			     const char *mboxname)
{
    const char *bdata;
    int bdatalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    strarray_t mboxes = STRARRAY_INITIALIZER;
    modseq_t oldmodseq = 0;
    struct buf buf = BUF_INITIALIZER;
    int r = 0;
    int found = -1;

    if (!state->db)
	return IMAP_IOERROR;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);
    r = DB->fetch(state->db,
		  bkey, strlen(bkey),
		  &bdata, &bdatalen,
		  &state->txn);

    if (r == CYRUSDB_OK)
    {
	/* found an existing record */
	parse_conversation_folders(bdata, bdatalen, &oldmodseq, &mboxes);
	found = strarray_find(&mboxes, mboxname, 0);
    } else if (r != CYRUSDB_NOTFOUND) {
	return r;	/* some db error */
    }

    if (found >= 0) {
	if (oldmodseq == highestmodseq)
	    goto out;
    }
    else {
	/* folder not found */
	strarray_append(&mboxes, mboxname);
    }

    /* can't step back in time */
    if (highestmodseq < oldmodseq)
	highestmodseq = oldmodseq;

    build_conversation_folders(highestmodseq, &mboxes, &buf);

    r = DB->store(state->db,
		  bkey, strlen(bkey),
		  buf.s, buf.len,
		  &state->txn);

out:
    strarray_fini(&mboxes);
    buf_free(&buf);
    return r;
}

static int conversations_set_folders(struct conversations_state *state,
				     conversation_id_t cid,
				     modseq_t highestmodseq,
				     const strarray_t *mboxes)
{
    char bkey[CONVERSATION_ID_STRMAX+2];
    struct buf buf = BUF_INITIALIZER;
    int r;

    if (!state->db)
	return IMAP_IOERROR;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, cid);
    build_conversation_folders(highestmodseq, mboxes, &buf);

    r = DB->store(state->db,
		  bkey, strlen(bkey),
		  buf.s, buf.len,
		  &state->txn);

    buf_free(&buf);
    return r;
}

int conversations_get_folders(struct conversations_state *state,
			      conversation_id_t cid,
			      modseq_t *highestmodseqp,
			      strarray_t *sap)
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

    if (r == CYRUSDB_OK)
	parse_conversation_folders(bdata, bdatalen, highestmodseqp, sap);
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
    struct conversations_rec rec;
    int r;

    prock->nseen++;
    r = check_msgid(key, keylen, NULL);
    if (r) return r;

    r = _conversations_parse(data, datalen, &rec);
    if (r) return r;

    /* keep records newer than the threshold */
    if (rec.stamp >= prock->thresh)
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

static int dump_record_cb(void *rock,
		          const char *bkey, int bkeylen,
		          const char *data, int datalen)
{
    FILE *fp = rock;
    char *key = xstrndup(bkey, bkeylen);
    int r;

    switch (key[0])
    {
    case '<':	    /* msgid to cid mapping */
	{
	    struct conversations_rec rec;
	    char stampstr[32];

	    r = _conversations_parse(data, datalen, &rec);

	    time_to_iso8601(rec.stamp, stampstr, sizeof(stampstr));
	    fprintf(fp, "msgid_to_cid \"%s\" " CONV_FMT " %s\n",
		    key, rec.cid, stampstr);
	}
	break;
    case 'B':	    /* cid to folders mapping */
	{
	    modseq_t highestmodseq = 0;
	    strarray_t mboxes = STRARRAY_INITIALIZER;
	    int i;

	    parse_conversation_folders(data, datalen,
				       &highestmodseq, &mboxes);

	    fprintf(fp, "cid_to_folders %s %llu", key+1, highestmodseq);
	    for (i = 0 ; i < mboxes.count ; i++)
		fprintf(fp, " \"%s\"", mboxes.data[i]);
	    fprintf(fp, "\n");

	    strarray_fini(&mboxes);
	}
	break;
    default:
	fprintf(stderr, "Unknown record type: key=\"%s\"\n", key);
	break;
    }

    free(key);
    return 0;
}

void conversations_dump(struct conversations_state *state, FILE *fp)
{
    if (state->db)
	DB->foreach(state->db, "", 0, NULL, dump_record_cb, fp, &state->txn);
}

static int buf_getline(struct buf *buf,  FILE *fp)
{
    int c;

    buf_reset(buf);
    while ((c = fgetc(fp)) != EOF) {
	buf_putc(buf, c);
	if (c == '\n')
	    break;
    }
    buf_cstring(buf);
    return buf->len;
}

int conversations_undump(struct conversations_state *state, FILE *fp)
{
    struct buf line = BUF_INITIALIZER;
    struct buf w1 = BUF_INITIALIZER;
    struct buf w2 = BUF_INITIALIZER;
    struct protstream *prot = NULL;
    int c;
    int r;
    unsigned int lineno = 0;

    while (buf_getline(&line, fp)) {
	lineno++;
	/* set up to tokenize */
	prot = prot_readmap(buf_cstring(&line), line.len);
	if (!prot) {
	    r = IMAP_IOERROR;
	    goto out;
	}

	/* get the leading keyword */
	c = getastring(prot, NULL, &w1);
	if (c == EOF)
	    goto syntax_error;

	if (!strcmp(buf_cstring(&w1), "msgid_to_cid")) {
	    struct conversations_rec rec;

	    /* parse the msgid */
	    c = getastring(prot, NULL, &w1);
	    if (c == EOF)
		goto syntax_error;

	    /* parse the CID */
	    c = getastring(prot, NULL, &w2);
	    if (c == EOF)
		goto syntax_error;
	    if (!conversation_id_decode(&rec.cid, buf_cstring(&w2)))
		goto syntax_error;

	    /* parse the timestamp */
	    c = getastring(prot, NULL, &w2);
	    if (c == EOF)
		goto syntax_error;
	    if (time_from_iso8601(buf_cstring(&w2), &rec.stamp) < 0)
		goto syntax_error;

	    /* save into the database */
	    r = _conversations_set(state, buf_cstring(&w1), &rec);
	    if (r) {
		fprintf(stderr, "Error at line %u: %s\n", lineno, error_message(r));
		goto out;
	    }
	} else if (!strcmp(buf_cstring(&w1), "cid_to_folders")) {
	    conversation_id_t cid;
	    modseq_t highestmodseq;
	    strarray_t mboxes = STRARRAY_INITIALIZER;

	    /* parse the CID */
	    c = getastring(prot, NULL, &w1);
	    if (c == EOF)
		goto syntax_error;
	    if (!conversation_id_decode(&cid, buf_cstring(&w1)))
		goto syntax_error;

	    /* parse the list of mboxnames */
	    c = getastring(prot, NULL, &w1);
	    highestmodseq = strtoull(buf_cstring(&w1), NULL, 10);
	    r = 0;
	    while ((c = getastring(prot, NULL, &w1)) != EOF) {
		strarray_append(&mboxes, buf_cstring(&w1));
	    }
	    r = conversations_set_folders(state, cid, highestmodseq, &mboxes);
	    strarray_fini(&mboxes);
	    if (r)
		goto out;
	} else {
	    fprintf(stderr, "Unknown keyword \"%s\" at line %u\n",
		    buf_cstring(&w1), lineno);
	    r = IMAP_MAILBOX_BADFORMAT;
	    goto out;
	}

	prot_free(prot);
	prot = NULL;
    }

out:
    if (prot)
	prot_free(prot);
    buf_free(&line);
    buf_free(&w1);
    buf_free(&w2);
    return r;

syntax_error:
    fprintf(stderr, "Syntax error at line %u\n", lineno);
    r = IMAP_MAILBOX_BADFORMAT;
    goto out;
}

struct truncate_rock {
    struct conversations_state *state;
    int r;
};

static int delete_record_cb(void *rock,
		            const char *key, int keylen,
		            const char *data __attribute__((unused)),
			    int datalen __attribute__((unused)))
{
    struct truncate_rock *trock = rock;
    int r;

    r = DB->delete(trock->state->db,
		  key, keylen,
		  &trock->state->txn,
		  /*force*/1);
    if (r) {
	trock->r = r;
	return 1;   /* break the foreach() early */
    }

    return 0;
}

int conversations_truncate(struct conversations_state *state)
{
    struct truncate_rock trock = { state, 0 };
    int r = 0;

    /* Unfortunately, the libcyrusdb interface does not provide a
     * "delete every record" primitive like Berkerley's DB->truncate().
     * So we have to do it the hard way */

    if (state->db)
	DB->foreach(state->db, "", 0, NULL, delete_record_cb, &trock, &state->txn);
    return r;
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
    struct conversations_rec rec;
    int r;

    r = check_msgid(key, keylen, NULL);
    if (r) return r;

    r = _conversations_parse(data, datalen, &rec);
    if (r) return r;

    rrock->entries_seen++;

    if (rec.cid != rrock->from_cid)
	return 0;	/* nothing to see, move along */

    rrock->entries_renamed++;

    rec.cid = rrock->to_cid;
    return _conversations_set_key(rrock->state, key, keylen, &rec);
}

int conversations_rename_cid(struct conversations_state *state,
			     conversation_id_t from_cid,
			     conversation_id_t to_cid,
			     conversations_rename_cb_t renamecb,
			     void *rock)
{
    struct rename_rock rrock;
    const char *bdata;
    int bdatalen;
    char bkey[CONVERSATION_ID_STRMAX+2];
    modseq_t highestmodseq = 0;
    strarray_t mboxes = STRARRAY_INITIALIZER;
    struct buf buf = BUF_INITIALIZER;
    int i;
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

    parse_conversation_folders(bdata, bdatalen,
			       &highestmodseq, &mboxes);

    r = DB->delete(state->db,
		   bkey, strlen(bkey),
		   &state->txn, /*force*/0);
    if (r)
	goto out;

    snprintf(bkey, sizeof(bkey), "B" CONV_FMT, to_cid);
    build_conversation_folders(highestmodseq, &mboxes, &buf);

    r = DB->store(state->db,
		  bkey, strlen(bkey),
		  buf.s, buf.len,
		  &state->txn);
    if (r)
	goto out;

    if (renamecb) {
	for (i = 0 ; i < mboxes.count ; i++)
	    renamecb(mboxes.data[i], from_cid, to_cid, rock);
    }

out:
    strarray_fini(&mboxes);
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

#undef DB
