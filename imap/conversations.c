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
struct conversations_mrec {
    bit32   idhi;	/* low 32 bits of conversation id */
    bit32   idlo;	/* high 32 bits of conversation id */
    bit32   stamp;	/* time_t insertion timestamp */
};


/* basename of conversations db for shared namespace */
#define FNAME_SHARED "shared"
/* per user conversations db extension */
#define FNAME_CONVERSATIONS_SUFFIX ".conversations"

#define DB config_conversations_db


char *conversations_getpath(const char *mboxname)
{
    struct mboxname_parts parts;
    char c[2], d[2];
    char *fname;

    if (mboxname_to_parts(mboxname, &parts))
	return NULL;

    if (parts.userid) {
	/* have a userid: per-user conversations db */
	if (parts.domain)
	    fname = strconcat(config_dir,
			      FNAME_DOMAINDIR,
			      dir_hash_b(parts.domain, config_fulldirhash, d),
			      "/", parts.domain,
			      FNAME_USERDIR,
			      dir_hash_b(parts.userid, config_fulldirhash, c),
			      "/", parts.userid, FNAME_CONVERSATIONS_SUFFIX,
			      (char *)NULL);
	else
	    fname = strconcat(config_dir,
			      FNAME_USERDIR,
			      dir_hash_b(parts.userid, config_fulldirhash, c),
			      "/", parts.userid, FNAME_CONVERSATIONS_SUFFIX,
			      (char *)NULL);
    } else {
	/* no userid: global or per-domain conversations db for shared space */
	if (parts.domain)
	    fname = strconcat(config_dir,
			      FNAME_DOMAINDIR,
			      dir_hash_b(parts.domain, config_fulldirhash, d),
			      "/", parts.domain, "/",
			      FNAME_SHARED, FNAME_CONVERSATIONS_SUFFIX,
			      (char *)NULL);
	else
	    fname = strconcat(config_dir,
			      FNAME_SHARED, FNAME_CONVERSATIONS_SUFFIX,
			      (char *)NULL);
    }

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

int conversations_set(struct conversations_state *state,
		      const char *msgid,
		      conversation_id_t cid)
{
    int keylen;
    struct conversations_mrec mrec;
    int r;

    if (state->db == NULL)
	return IMAP_IOERROR;
    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    memset(&mrec, 0, sizeof(mrec));
    align_htonll(&mrec.idhi, cid);
    mrec.stamp = htonl(time(NULL));

    r = DB->store(state->db,
		  msgid, keylen,
		  (const char *)&mrec, sizeof(mrec),
		  &state->txn);
    if (r)
	return IMAP_IOERROR;
    return 0;
}

int conversations_get(struct conversations_state *state,
		      const char *msgid,
		      conversation_id_t *cidp)
{
    int keylen;
    struct conversations_mrec *mrec = NULL;
    int datalen = 0;
    int r;

    if (state->db == NULL)
	return IMAP_IOERROR;
    r = check_msgid(msgid, 0, &keylen);
    if (r)
	return r;

    r = DB->fetch(state->db,
		  msgid, keylen,
		  (const char **)&mrec, &datalen,
		  &state->txn);
    if (r == CYRUSDB_NOTFOUND) {
	*cidp = NULLCONVERSATION;
	return 0;
    }
    if (r || mrec == NULL || datalen != sizeof(*mrec))
	return IMAP_IOERROR;

    *cidp = align_ntohll(&mrec->idhi);
    return 0;
}

struct prune_rock {
    struct conversations_state *state;
    time_t thresh;
};

static int prunecb(void *rock,
		   const char *key, int keylen,
		   const char *data, int datalen)
{
    struct prune_rock *prock = (struct prune_rock *)rock;
    const struct conversations_mrec *mrec = (struct conversations_mrec *)data;
    time_t stamp;
    int r;

    r = check_msgid(key, keylen, NULL);
    if (r)
	return r;
    if (datalen != sizeof(*mrec))
	return IMAP_IOERROR;

    stamp = ntohl(mrec->stamp);
    if (stamp >= prock->thresh)
	return 0;

    return DB->delete(prock->state->db,
		      key, keylen,
		      &prock->state->txn,
		      /*force*/1);
}

int conversations_prune(struct conversations_state *state, time_t thresh)
{
    struct prune_rock rock = { state, thresh };

    DB->foreach(state->db, "<", 1, NULL, prunecb, &rock, &state->txn);

    return 0;
}

static int dumpcb(void *rock,
		  const char *key, int keylen,
		  const char *data, int datalen)
{
    FILE *fp = rock;
    const struct conversations_mrec *mrec = (struct conversations_mrec *)data;
    time_t stamp;
    char stampstr[32];

    stamp = ntohl(mrec->stamp);
    strftime(stampstr, sizeof(stampstr), "%Y-%m-%dT%H:%M:%SZ", gmtime(&stamp));
    fprintf(fp, "\"%*s\"\t%08x%08x\t%s\n",
	    keylen, key,
	    ntohl(mrec->idhi), ntohl(mrec->idlo), stampstr);
    return 0;
}

void conversations_dump(struct conversations_state *state, FILE *fp)
{
    if (state->db) {
	fprintf(fp, "MSGID\tCID\tSTAMP\n");
	fprintf(fp, "=====\t===\t=====\n");
	DB->foreach(state->db, NULL, 0, NULL, dumpcb, fp, &state->txn);
	fprintf(fp, "===============\n");
    }
}

const char *conversation_id_encode(conversation_id_t cid)
{
    static char text[2*sizeof(cid)+1];

    if (cid != NULLCONVERSATION) {
	cid = htonll(cid);
	bin_to_hex(&cid, sizeof(cid), text, BH_LOWER);
    } else {
	strncpy(text, "NIL", sizeof(text));
    }

    return text;
}

int conversation_id_decode(conversation_id_t *cid, const char *text)
{
    if (!strcmp(text, "NIL")) {
	*cid = NULLCONVERSATION;
	return 1;
    } else {
	int r = hex_to_bin(text, 0, cid);
	*cid = ntohll(*cid);
	return (r == sizeof(cid));
    }
}

#undef DB
