/* dlist.c - list protocol for dump and sync
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
 * $Id: sync_support.c,v 1.25 2010/01/06 17:01:41 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <syslog.h>
#include <string.h>
#include <sys/wait.h>
#include <errno.h>
#include <ctype.h>
#include <dirent.h>
#include <utime.h>

#include "global.h"
#include "assert.h"
#include "mboxlist.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "mailbox.h"
#include "quota.h"
#include "xmalloc.h"
#include "xstrlcat.h"
#include "xstrlcpy.h"
#include "acl.h"
#include "seen.h"
#include "mboxname.h"
#include "map.h"
#include "imapd.h"
#include "imparse.h"
#include "message.h"
#include "util.h"
#include "retry.h"
#include "cyr_lock.h"
#include "prot.h"

#include "dlist.h"

/* Parse routines */

const char *lastkey = NULL;

static void printfile(struct protstream *out, const struct dlist *dl)
{
    char buf[4096];
    struct stat sbuf;
    FILE *f;
    unsigned long size;

    assert(dlist_isfile(dl));

    f = fopen(dl->sval, "r");
    if (!f) {
	syslog(LOG_ERR, "IOERROR: Failed to read file %s", dl->sval);
	prot_printf(out, "NIL");
	return;
    }
    if (fstat(fileno(f), &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: Failed to stat file %s", dl->sval);
	prot_printf(out, "NIL");
	fclose(f);
	return;
    }
    size = sbuf.st_size;
    if (size != dl->nval) {
	syslog(LOG_ERR, "IOERROR: Size mismatch %s (%lu != " MODSEQ_FMT ")",
	       dl->sval, size, dl->nval);
	prot_printf(out, "NIL");
	fclose(f);
	return;
    }

    prot_printf(out, "%%{");
    prot_printastring(out, dl->part);
    prot_printf(out, " ");
    prot_printastring(out, message_guid_encode(dl->gval));
    prot_printf(out, " %lu}\r\n", size);
    while (size) {
	int n = fread(buf, 1, (size > 4096 ? 4096 : size), f);
	if (n <= 0) break;
	prot_write(out, buf, n);
	size -= n;
    }
    fclose(f);

    if (size) fatal("failed to finish reading file!", EC_IOERR);
}

/* XXX - these two functions should be out in append.c or reserve.c
 * or something more general */
const char *dlist_reserve_path(const char *part, struct message_guid *guid)
{
    static char buf[MAX_MAILBOX_PATH];
    snprintf(buf, MAX_MAILBOX_PATH, "%s/sync./%lu/%s", 
		  config_partitiondir(part), (unsigned long)getpid(),
		  message_guid_encode(guid));
    cyrus_mkdir(buf, 0755);
    return buf;
}

static int reservefile(struct protstream *in, const char *part,
		       struct message_guid *guid, unsigned long size,
		       const char **fname)
{
    FILE *file;
    char buf[8192+1];
    int r = 0, n;
    
    /* XXX - write to a temporary file then move in to place! */
    *fname = dlist_reserve_path(part, guid);

    file = fopen(*fname, "w+");
    if (!file) {
	syslog(LOG_ERR, "Failed to upload file %s", message_guid_encode(guid));
	r = IMAP_IOERROR;
	/* Note: we still read the file's data from the wire,
	 * to avoid losing protocol sync */
    }

    /* XXX - calculate sha1 on the fly? */
    while (size) {
	n = prot_read(in, buf, size > 8192 ? 8192 : size);
	if (!n) {
	    syslog(LOG_ERR,
		"IOERROR: reading message: unexpected end of file");
	    r = IMAP_IOERROR;
	    break;
	}
	size -= n;
	if (!r) fwrite(buf, 1, n, file);
    }

    if (r)
	goto error;

    /* Make sure that message flushed to disk just incase mmap has problems */
    fflush(file);
    if (ferror(file)) {
	r = IMAP_IOERROR;
	goto error;
    }

    if (fsync(fileno(file)) < 0) {
	r = IMAP_IOERROR;
	goto error;
    }

    fclose(file);

    return 0;

error:
    if (file) {
	fclose(file);
	unlink(*fname);
	*fname = NULL;
    }
    return r;
}

/* DLIST STUFF */

void dlist_stitch(struct dlist *parent, struct dlist *child)
{
    assert(!child->next);

    if (parent->tail) {
	parent->tail->next = child;
	parent->tail = child;
    }
    else {
	parent->head = parent->tail = child;
    }
}

void dlist_unstitch(struct dlist *parent, struct dlist *child)
{
    struct dlist *prev = NULL;
    struct dlist *replace = NULL;

    /* find old record */
    for (replace = parent->head; replace; replace = replace->next) {
	if (replace == child) break;
	prev = replace;
    }

    assert(replace);

    if (prev) prev->next = child->next;
    else (parent->head) = child->next;

    if (parent->tail == child) parent->tail = prev;

    child->next = NULL;
}

static struct dlist *dlist_child(struct dlist *dl, const char *name)
{
    struct dlist *i = xzmalloc(sizeof(struct dlist));
    if (name) i->name = xstrdup(name);
    i->type = DL_NIL;
    if (dl)
	dlist_stitch(dl, i);
    return i;
}

static void _dlist_free_children(struct dlist *dl)
{
    struct dlist *next;
    struct dlist *i;

    if (!dl) return;

    i = dl->head;
    while (i) {
	next = i->next;
	dlist_free(&i);
	i = next;
    }

    dl->head = dl->tail = NULL;
}

static void _dlist_clean(struct dlist *dl)
{
    if (!dl) return;

    /* remove any children */
    _dlist_free_children(dl);

    /* clean out values */
    free(dl->part);
    dl->part = NULL;
    free(dl->sval);
    dl->sval = NULL;
    free(dl->gval);
    dl->gval = NULL;
    dl->nval = 0;
}


void dlist_makeatom(struct dlist *dl, const char *val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_ATOM;
    dl->sval = val ? xstrdup(val) : NULL;
    dl->nval = strlen(dl->sval);
}

void dlist_makeflag(struct dlist *dl, const char *val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_FLAG;
    dl->sval = xstrdup(val);
    dl->nval = strlen(dl->sval);
}

void dlist_makenum32(struct dlist *dl, uint32_t val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_NUM;
    dl->nval = val;
}

void dlist_makenum64(struct dlist *dl, bit64 val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_NUM;
    dl->nval = val;
}

void dlist_makedate(struct dlist *dl, time_t val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_DATE;
    dl->nval = val;
}

void dlist_makehex64(struct dlist *dl, bit64 val)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_HEX;
    dl->nval = val;
}

void dlist_makeguid(struct dlist *dl, struct message_guid *guid)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_GUID,
    dl->gval = xzmalloc(sizeof(struct message_guid));
    message_guid_copy(dl->gval, guid);
}

void dlist_makefile(struct dlist *dl,
		    const char *part, struct message_guid *guid,
		    unsigned long size, const char *fname)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_FILE;
    dl->gval = xzmalloc(sizeof(struct message_guid));
    message_guid_copy(dl->gval, guid);
    dl->sval = xstrdup(fname);
    dl->nval = size;
    dl->part = xstrdup(part);
}

void dlist_makemap(struct dlist *dl, const char *val, size_t len)
{
    if (!dl) return;
    _dlist_clean(dl);
    dl->type = DL_BUF;
    /* WARNING - DO NOT replace this with xstrndup - the
     * data may be binary, and xstrndup does not copy
     * binary data correctly - but we still want to NULL
     * terminate for non-binary data */
    dl->sval = xmalloc(len+1);
    memcpy(dl->sval, val, len);
    dl->sval[len] = '\0'; /* make it string safe too */
    dl->nval = len;
}

struct dlist *dlist_newkvlist(struct dlist *parent, const char *name)
{
    struct dlist *dl = dlist_child(parent, name);
    dl->type = DL_KVLIST;
    return dl;
}

struct dlist *dlist_newlist(struct dlist *parent, const char *name)
{
    struct dlist *dl = dlist_child(parent, name);
    dl->type = DL_ATOMLIST;
    return dl;
}

struct dlist *dlist_newpklist(struct dlist *parent, const char *name)
{
    struct dlist *dl = dlist_child(parent, name);
    dl->type = DL_ATOMLIST;
    dl->nval = 1;
    return dl;
}

struct dlist *dlist_setatom(struct dlist *parent, const char *name, const char *val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makeatom(dl, val);
    return dl;
}

struct dlist *dlist_setflag(struct dlist *parent, const char *name, const char *val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makeflag(dl, val);
    return dl;
}

struct dlist *dlist_setnum64(struct dlist *parent, const char *name, bit64 val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makenum64(dl, val);
    return dl;
}

struct dlist *dlist_setnum32(struct dlist *parent, const char *name, uint32_t val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makenum32(dl, val);
    return dl;
}

struct dlist *dlist_setdate(struct dlist *parent, const char *name, time_t val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makedate(dl, val);
    return dl;
}

struct dlist *dlist_sethex64(struct dlist *parent, const char *name, bit64 val)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makehex64(dl, val);
    return dl;
}

struct dlist *dlist_setmap(struct dlist *parent, const char *name,
			   const char *val, unsigned long len)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makemap(dl, val, len);
    return dl;
}

struct dlist *dlist_setguid(struct dlist *parent, const char *name,
			    struct message_guid *guid)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makeguid(dl, guid);
    return dl;
}

struct dlist *dlist_setfile(struct dlist *parent, const char *name,
			    const char *part, struct message_guid *guid,
			    size_t size, const char *fname)
{
    struct dlist *dl = dlist_child(parent, name);
    dlist_makefile(dl, part, guid, size, fname);
    return dl;
}

struct dlist *dlist_updatechild(struct dlist *parent, const char *name)
{
    struct dlist *dl = dlist_getchild(parent, name);
    if (!dl) dl = dlist_child(parent, name);
    return dl;
}

struct dlist *dlist_updateatom(struct dlist *parent, const char *name, const char *val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makeatom(dl, val);
    return dl;
}

struct dlist *dlist_updateflag(struct dlist *parent, const char *name, const char *val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makeflag(dl, val);
    return dl;
}

struct dlist *dlist_updatenum64(struct dlist *parent, const char *name, bit64 val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makenum64(dl, val);
    return dl;
}

struct dlist *dlist_updatenum32(struct dlist *parent, const char *name, uint32_t val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makenum32(dl, val);
    return dl;
}

struct dlist *dlist_updatedate(struct dlist *parent, const char *name, time_t val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makedate(dl, val);
    return dl;
}

struct dlist *dlist_updatehex64(struct dlist *parent, const char *name, bit64 val)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makehex64(dl, val);
    return dl;
}

struct dlist *dlist_updatemap(struct dlist *parent, const char *name,
			   const char *val, unsigned long len)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makemap(dl, val, len);
    return dl;
}

struct dlist *dlist_updateguid(struct dlist *parent, const char *name,
			    struct message_guid *guid)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makeguid(dl, guid);
    return dl;
}

struct dlist *dlist_updatefile(struct dlist *parent, const char *name,
			    const char *part, struct message_guid *guid,
			    size_t size, const char *fname)
{
    struct dlist *dl = dlist_updatechild(parent, name);
    dlist_makefile(dl, part, guid, size, fname);
    return dl;
}

void dlist_print(const struct dlist *dl, int printkeys,
		 struct protstream *out)
{
    struct dlist *di;

    if (printkeys)
	prot_printf(out, "%s ", dl->name);

    switch (dl->type) {
    case DL_ATOM:
	prot_printastring(out, dl->sval);
	break;
    case DL_FLAG:
	prot_printf(out, "%s", dl->sval);
	break;
    case DL_NUM:
    case DL_DATE: /* for now, we will format it later */
	prot_printf(out, "%llu", dl->nval);
	break;
    case DL_FILE:
	printfile(out, dl);
	break;
    case DL_BUF:
	prot_printliteral(out, dl->sval, dl->nval);
	break;
    case DL_HEX:
	{
	    char buf[17];
	    snprintf(buf, 17, "%016llx", dl->nval);
	    prot_printf(out, "%s", buf);
	}
	break;
    case DL_KVLIST:
	prot_printf(out, "%%(");
	for (di = dl->head; di; di = di->next) {
	    dlist_print(di, 1, out);
	    if (di->next) {
		prot_printf(out, " ");
	    }
	}
	prot_printf(out, ")");
	break;
    case DL_ATOMLIST:
	prot_printf(out, "(");
	for (di = dl->head; di; di = di->next) {
	    dlist_print(di, dl->nval, out);
	    if (di->next)
		prot_printf(out, " ");
	}
	prot_printf(out, ")");
	break;
    }
}

void dlist_printbuf(const struct dlist *dl, int printkeys, struct buf *outbuf)
{
    struct protstream *outstream;

    outstream = prot_writebuf(outbuf);
    dlist_print(dl, printkeys, outstream);
    prot_flush(outstream);
    prot_free(outstream);
}

void dlist_free(struct dlist **dlp)
{
    if (!*dlp) return;
    _dlist_clean(*dlp);
    free((*dlp)->name);
    free(*dlp);
    *dlp = NULL;
}

static char next_nonspace(struct protstream *in, char c)
{
    if (c == ' ') c = prot_getc(in);
    return c;
}

char dlist_parse(struct dlist **dlp, int parsekey, struct protstream *in)
{
    struct dlist *dl = NULL;
    static struct buf kbuf;
    static struct buf vbuf;
    char c;

    /* handle the key if wanted */
    if (parsekey) {
	c = getword(in, &kbuf);
	c = next_nonspace(in, c);
    }
    else {
	buf_setcstr(&kbuf, "");
	c = prot_getc(in);
    }

    /* connection dropped? */
    if (c == EOF) goto fail;

    /* check what sort of value we have */
    if (c == '(') {
	dl = dlist_newlist(NULL, kbuf.s);
	c = next_nonspace(in, ' ');
	while (c != ')') {
	    struct dlist *di = NULL;
	    prot_ungetc(c, in);
	    c = dlist_parse(&di, 0, in);
	    if (di) dlist_stitch(dl, di);
	    c = next_nonspace(in, c);
	    if (c == EOF) goto fail;
	}
	c = prot_getc(in);
    }
    else if (c == '%') {
	/* no whitespace allowed here */
	c = prot_getc(in);
	if (c == '(') {
	    dl = dlist_newkvlist(NULL, kbuf.s);
	    c = next_nonspace(in, ' ');
	    while (c != ')') {
		struct dlist *di = NULL;
		prot_ungetc(c, in);
		c = dlist_parse(&di, 1, in);
		if (di) dlist_stitch(dl, di);
		c = next_nonspace(in, c);
		if (c == EOF) goto fail;
	    }
	}
	else if (c == '{') {
	    struct message_guid tmp_guid;
	    static struct buf pbuf, gbuf;
	    unsigned size = 0;
	    const char *fname;
	    c = getastring(in, NULL, &pbuf);
	    if (c != ' ') goto fail;
	    c = getastring(in, NULL, &gbuf);
	    if (c != ' ') goto fail;
	    c = getuint32(in, &size);
	    if (c != '}') goto fail;
	    c = prot_getc(in);
	    if (c == '\r') c = prot_getc(in);
	    if (c != '\n') goto fail;
	    if (!message_guid_decode(&tmp_guid, gbuf.s)) goto fail;
	    if (reservefile(in, pbuf.s, &tmp_guid, size, &fname)) goto fail;
	    dl = dlist_setfile(NULL, kbuf.s, pbuf.s, &tmp_guid, size, fname);
	    /* file literal */
	}
	else {
	    /* unknown percent type */
	    goto fail;
	}
	c = prot_getc(in);
    }
    else if (c == '{') {
	prot_ungetc(c, in);
	/* could be binary in a literal */
	c = getbastring(in, NULL, &vbuf);
	dl = dlist_setmap(NULL, kbuf.s, vbuf.s, vbuf.len);
    }
    else if (c == '\\') { /* special case for flags */
	prot_ungetc(c, in);
	c = getastring(in, NULL, &vbuf);
	dl = dlist_setflag(NULL, kbuf.s, vbuf.s);
    }
    else {
	prot_ungetc(c, in);
	c = getastring(in, NULL, &vbuf);
	dl = dlist_setatom(NULL, kbuf.s, vbuf.s);
    }

    /* success */
    *dlp = dl;
    return c;

fail:
    dlist_free(&dl);
    return EOF;
}

int dlist_parsemap(struct dlist **dlp, int parsekey,
		   const char *base, unsigned len)
{
    struct protstream *stream;
    char c;
    struct dlist *dl = NULL;

    stream = prot_readmap(base, len);
    prot_setisclient(stream, 1); /* don't sync literals */
    c = dlist_parse(&dl, parsekey, stream);
    prot_free(stream);

    if (c != EOF) {
	dlist_free(&dl);
	return IMAP_IOERROR; /* failed to slurp entire buffer */
    }

    *dlp = dl;

    return 0;
}

struct dlist *dlist_getchild(struct dlist *dl, const char *name)
{
    struct dlist *i;

    if (!dl) return NULL;

    for (i = dl->head; i; i = i->next) {
	if (i->name && !strcmp(name, i->name))
	    return i;
    }
    lastkey = name;
    return NULL;
}

struct dlist *dlist_getchildn(struct dlist *dl, int num)
{
    struct dlist *i;

    if (!dl) return NULL;

    for (i = dl->head; i && num; i = i->next)
	num--;

    return i;
}

struct dlist *dlist_getkvchild_bykey(struct dlist *dl,
				     const char *key, const char *val)
{
    struct dlist *i;
    struct dlist *tmp;

    if (!dl) return NULL;

    for (i = dl->head; i; i = i->next) {
	tmp = dlist_getchild(i, key);
	if (tmp && !strcmp(tmp->sval, val))
	    return i;
    }

    return NULL;
}

int dlist_toatom(struct dlist *dl, const char **valp)
{
    const char *str;
    size_t len;

    /* tomap always adds a trailing \0 */
    if (!dlist_tomap(dl, &str, &len))
	return 0;

    /* got NULLs? */
    if (dl->type == DL_BUF && strlen(str) != len)
	return 0;

    if (valp) *valp = str;

    return 1;
}

int dlist_tomap(struct dlist *dl, const char **valp, size_t *lenp)
{
    char tmp[30];

    if (!dl) return 0;

    switch (dl->type) {
    case DL_NUM:
    case DL_DATE:
	snprintf(tmp, 30, "%llu", dl->nval);
	dlist_makeatom(dl, tmp);
	break;

    case DL_HEX:
	snprintf(tmp, 30, "%016llx", dl->nval);
	dlist_makeatom(dl, tmp);
	break;

    case DL_GUID:
	dlist_makeatom(dl, message_guid_encode(dl->gval));
	break;

    case DL_ATOM:
    case DL_FLAG:
    case DL_BUF:
	break;

    default:
	return 0;
    }

    if (valp) *valp = dl->sval;
    if (lenp) *lenp = dl->nval;

    return 1;
}

/* ensure value is exactly one number */
int dlist_tonum64(struct dlist *dl, bit64 *valp)
{
    const char *end;
    bit64 newval;

    if (!dl) return 0;

    switch (dl->type) {
    case DL_ATOM:
    case DL_BUF:
	if (parsenum(dl->sval, &end, dl->nval, &newval))
	    return 0;
	if (end - dl->sval != (int)dl->nval)
	    return 0;
	/* successfully parsed - switch to a numeric value */
	dlist_makenum64(dl, newval);
	break;

    case DL_NUM:
    case DL_HEX:
    case DL_DATE:
	break;

    default:
	return 0;
    }

    if (valp) *valp = dl->nval;

    return 1;
}

int dlist_tonum32(struct dlist *dl, uint32_t *valp)
{
    bit64 v;

    if (dlist_tonum64(dl, &v)) {
	if (valp) *valp = (uint32_t)v;
	return 1;
    }

    return 0;
}

int dlist_todate(struct dlist *dl, time_t *valp)
{
    bit64 v;

    if (dlist_tonum64(dl, &v)) {
	if (valp) *valp = (time_t)v;
	dl->type = DL_DATE;
	return 1;
    }

    return 0;
}

int dlist_tohex64(struct dlist *dl, bit64 *valp)
{
    const char *end = NULL;
    bit64 newval;

    if (!dl) return 0;

    switch (dl->type) {
    case DL_ATOM:
    case DL_BUF:
	if (parsehex(dl->sval, &end, dl->nval, &newval))
	    return 0;
	if (end - dl->sval != (int)dl->nval)
	    return 0;
	/* successfully parsed - switch to a numeric value */
	dlist_makehex64(dl, newval);
	break;

    case DL_NUM:
    case DL_HEX:
    case DL_DATE:
	dl->type = DL_HEX;
	break;

    default:
	return 0;
    }

    if (valp) *valp = dl->nval;

    return 1;
}

int dlist_toguid(struct dlist *dl, struct message_guid **valp)
{
    struct message_guid tmpguid;

    if (!dl) return 0;

    switch (dl->type) {
    case DL_ATOM:
    case DL_BUF:
	if (dl->nval != 40)
	    return 0;
	if (!message_guid_decode(&tmpguid, dl->sval))
	    return 0;
	/* successfully parsed - switch to guid value */
	dlist_makeguid(dl, &tmpguid);
	break;

    case DL_GUID:
	break;

    default:
	return 0;
    }

    if (valp) *valp = dl->gval;

    return 0;
}

int dlist_tofile(struct dlist *dl,
		 const char **partp, struct message_guid **guidp,
		 unsigned long *sizep, const char **fnamep)
{
    if (!dlist_isfile(dl)) return 0;

    if (guidp) *guidp = dl->gval;
    if (sizep) *sizep = dl->nval;
    if (fnamep) *fnamep = dl->sval;
    if (partp) *partp = dl->part;

    return 1;
}

int dlist_isatomlist(const struct dlist *dl)
{
    if (!dl) return 0;
    return (dl->type == DL_ATOMLIST);
}

int dlist_iskvlist(const struct dlist *dl)
{
    if (!dl) return 0;

    return (dl->type == DL_KVLIST);
}

int dlist_isfile(const struct dlist *dl)
{
    if (!dl) return 0;

    return (dl->type == DL_FILE);
}

/* XXX - these ones aren't const, because they can change
 * things... */
int dlist_isnum(struct dlist *dl)
{
    bit64 tmp;

    if (!dl) return 0;

    /* see if it can be parsed as a number */
    return dlist_tonum64(dl, &tmp);
}

/* XXX - these ones aren't const, because they can change
 * things... */
int dlist_isguid(struct dlist *dl)
{
    struct message_guid *tmp;

    if (!dl) return 0;

    return dlist_toguid(dl, &tmp);
}

/* XXX - this stuff is all shitty, rationalise later */
bit64 dlist_num(struct dlist *dl)
{
    bit64 v;

    if (!dl) return 0;

    if (dlist_tonum64(dl, &v))
	return v;

    return 0;
}

/* XXX - this stuff is all shitty, rationalise later */
const char *dlist_cstring(struct dlist *dl)
{
    static char zerochar = '\0';

    if (dl) {
	const char *res = NULL;
	dlist_toatom(dl, &res);
	if (res) return res;
    }

    return &zerochar;
}

int dlist_getatom(struct dlist *parent, const char *name, const char **valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_toatom(child, valp);
}

int dlist_getnum32(struct dlist *parent, const char *name, uint32_t *valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_tonum32(child, valp);
}

int dlist_getnum64(struct dlist *parent, const char *name, bit64 *valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_tonum64(child, valp);
}

int dlist_getdate(struct dlist *parent, const char *name, time_t *valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_todate(child, valp);
}

int dlist_gethex64(struct dlist *parent, const char *name, bit64 *valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_tohex64(child, valp);
}

int dlist_getguid(struct dlist *parent, const char *name,
		  struct message_guid **valp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_toguid(child, valp);
}

int dlist_getmap(struct dlist *parent, const char *name,
		 const char **valp, size_t *lenp)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_tomap(child, valp, lenp);
}

int dlist_getfile(struct dlist *parent, const char *name,
		  const char **partp,
		  struct message_guid **guidp,
		  unsigned long *sizep,
		  const char **fnamep)
{
    struct dlist *child = dlist_getchild(parent, name);
    return dlist_tofile(child, partp, guidp, sizep, fnamep);
}

int dlist_getlist(struct dlist *dl, const char *name, struct dlist **valp)
{
    struct dlist *i = dlist_getchild(dl, name);
    if (!i) return 0;
    *valp = i;
    return 1;
}

const char *dlist_lastkey(void)
{
    return lastkey;
}
