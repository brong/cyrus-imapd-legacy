/* charset.c -- International character set support
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

#include <config.h>
#include <stdlib.h>
#include <string.h>

#include "charset.h"
#include "xmalloc.h"
#include "chartable.h"
#include "util.h"

#define U_REPLACEMENT	0xfffd

#define unicode_isvalid(c) \
	(!((c >= 0xd800 && c <= 0xdfff) || ((unsigned)c > 0x10ffff)))

char QPSAFECHAR[256] = {
/* control chars are unsafe */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
/* http://en.wikipedia.org/wiki/Quoted-printable */
/* All printable ASCII characters (decimal values between 33 and 126) */
/* may be represented by themselves, except "=" (decimal 61). */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
/* all high bits are unsafe */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

struct qp_state {
    int isheader;
    int bytesleft;
    int codepoint;
};

struct b64_state {
    int bytesleft;
    int codepoint;
};

struct table_state {
    const struct charmap (*curtable)[256];
    const struct charmap (*initialtable)[256];
    int bytesleft;
    int codepoint;
    int mode;
    int num_bits;
};

struct canon_state {
    int flags;
    int seenspace;
};

struct comp_pat_s {
    int max_start;
    size_t patlen;
};

struct search_state {
    ssize_t *starts;
    int max_start;
    int havematch;
    unsigned char *substr;
    size_t patlen;
    size_t offset;
};

struct convert_rock;

typedef void convertproc_t(struct convert_rock *rock, int c);
typedef void freeconvert_t(struct convert_rock *rock);

struct convert_rock {
    convertproc_t *f;
    freeconvert_t *cleanup;
    struct convert_rock *next;
    void *state;
};

#define GROWSIZE 100

#define XX 127
/*
 * Table for decoding hexadecimal in quoted-printable
 */
static const char index_hex[256] = {
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
     0, 1, 2, 3,  4, 5, 6, 7,  8, 9,XX,XX, XX,XX,XX,XX,
    XX,10,11,12, 13,14,15,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,10,11,12, 13,14,15,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
};
#define HEXCHAR(c)  (index_hex[(unsigned char)(c)])

/*
 * Table for decoding base64
 */
static const char index_64[256] = {
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,62, XX,XX,XX,63,
    52,53,54,55, 56,57,58,59, 60,61,XX,XX, XX,XX,XX,XX,
    XX, 0, 1, 2,  3, 4, 5, 6,  7, 8, 9,10, 11,12,13,14,
    15,16,17,18, 19,20,21,22, 23,24,25,XX, XX,XX,XX,XX,
    XX,26,27,28, 29,30,31,32, 33,34,35,36, 37,38,39,40,
    41,42,43,44, 45,46,47,48, 49,50,51,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
    XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX, XX,XX,XX,XX,
};
#define CHAR64(c)  (index_64[(unsigned char)(c)])

EXPORTED int encoding_lookupname(const char *s)
{
    switch (s[0]) {
    case '7':
	if (!strcasecmp(s, "7BIT"))
	    return ENCODING_NONE;
	break;
    case '8':
	if (!strcasecmp(s, "8BIT"))
	    return ENCODING_NONE;
	break;
    case 'B':
    case 'b':
	if (!strcasecmp(s, "BASE64"))
	    return ENCODING_BASE64;
	if (!strcasecmp(s, "BINARY"))
	    return ENCODING_NONE;
	break;
    case 'Q':
    case 'q':
	if (!strcasecmp(s, "QUOTED-PRINTABLE"))
	    return ENCODING_QP;
	break;
    }
    return ENCODING_UNKNOWN;
}

EXPORTED const char *encoding_name(int encoding)
{
    switch (encoding) {
    case ENCODING_NONE: return "NONE";
    case ENCODING_QP: return "QUOTED-PRINTABLE";
    case ENCODING_BASE64: return "BASE64";
    case ENCODING_UNKNOWN: return "UNKNOWN";
    default: return "WTF";
    }
}

static inline void convert_putc(struct convert_rock *rock, int c)
{
    rock->f(rock, c);
}

static void convert_cat(struct convert_rock *rock, const char *s)
{
    while (*s) {
	convert_putc(rock, (unsigned char)*s);
	s++;
    }
}

static void convert_catn(struct convert_rock *rock, const char *s, size_t len)
{
    while (len-- > 0) {
	convert_putc(rock, (unsigned char)*s);
	s++;
    }
}

/* convertproc_t conversion functions */

static void qp2byte(struct convert_rock *rock, int c)
{
    struct qp_state *s = (struct qp_state *)rock->state;
    int val;

    if (s->bytesleft) {
	s->bytesleft--;
	val = HEXCHAR(c);
	if (val == XX) {
	    /* mark invalid regardless */
	    s->codepoint = -1;
	    return;
	}
	if (s->codepoint != -1) {
	    /* don't blat the invalid marker, but still absorb
	     * the second char */
	    s->codepoint = (s->codepoint << 4) + val;
	}
	if (!s->bytesleft) {
	    if (s->codepoint == -1)
		convert_putc(rock->next, 0xfffd);
	    else
		convert_putc(rock->next, s->codepoint & 0xff);
	}
	return;
    }

    /* start an encoded byte */
    if (c == '=') {
	s->bytesleft = 2;
	s->codepoint = 0;
	return;
    }

    /* underscores are space in headers */
    if (s->isheader && c == '_') c = ' ';

    convert_putc(rock->next, c);
}

static void b64_2byte(struct convert_rock *rock, int c)
{
    struct b64_state *s = (struct b64_state *)rock->state;
    char b = CHAR64(c);

    /* could just be whitespace, ignore it */
    if (b == XX) return;

    switch (s->bytesleft) {
    case 0:
        s->codepoint = b;
	s->bytesleft = 3;
	break;
    case 3:
	convert_putc(rock->next, ((s->codepoint << 2) | (b >> 4)) & 0xff);
	s->codepoint = b;
	s->bytesleft = 2;
	break;
    case 2:
	convert_putc(rock->next, ((s->codepoint << 4) | (b >> 2)) & 0xff);
	s->codepoint = b;
	s->bytesleft = 1;
	break;
    case 1:
	convert_putc(rock->next, ((s->codepoint << 6) | b) & 0xff);
	s->codepoint = 0;
	s->bytesleft = 0;
    }
}

static void stripnl2uni(struct convert_rock *rock, int c)
{
    if (c != '\r' && c != '\n')
	convert_putc(rock->next, c);
}

static void table2uni(struct convert_rock *rock, int c)
{
    struct table_state *s = (struct table_state *)rock->state;
    struct charmap *map = (struct charmap *)&s->curtable[0][c & 0xff];

    /* propagate errors */
    if (c == 0xfffd) {
	convert_putc(rock->next, c);
	return;
    }

    if (map->c)
	convert_putc(rock->next, map->c);

    s->curtable = s->initialtable + map->next;
}

static void utf8_2uni(struct convert_rock *rock, int c)
{
    struct table_state *s = (struct table_state *)rock->state;

    /* propagate errors */
    if (c == 0xfffd) {
	convert_putc(rock->next, c);
	return;
    }

    if ((c & 0xf8) == 0xf0) { /* 11110xxx */
	/* first of a 4 char sequence */
	s->bytesleft = 3;
	s->codepoint = c & 0x07; /* 00000111 */
    }
    else if ((c & 0xf0) == 0xe0) { /* 1110xxxx */
	/* first of a 3 char sequence */
	s->bytesleft = 2;
	s->codepoint = c & 0x0f; /* 00001111 */
    }
    else if ((c & 0xe0) == 0xc0) { /* 110xxxxx */
	/* first of a 2 char sequence */
	s->bytesleft = 1;
	s->codepoint = c & 0x1f; /* 00011111 */
    }
    else if ((c & 0xc0) == 0x80) { /* 10xxxxxx */
	/* continuation char, handle only if expected */
	if (s->bytesleft > 0) {
	    s->codepoint = (s->codepoint << 6) + (c & 0x3f); /* 00111111 */
	    s->bytesleft--;
	    if (!s->bytesleft) {
	        convert_putc(rock->next, s->codepoint);
		s->codepoint = 0;
	    }
	}
    }
    else { /* plain ASCII char */
	convert_putc(rock->next, c);
	s->bytesleft = 0;
	s->codepoint = 0;
    }
}

static void utf7_2uni (struct convert_rock *rock, int c)
{
    struct table_state *s = (struct table_state *)rock->state;

    /* propagate errors */
    if (c == 0xfffd) {
	convert_putc(rock->next, c);
	return;
    }

    if (c & 0x80) { /* skip 8-bit chars */
	convert_putc(rock->next, 0xfffd);
	return;
    }

    /* Inside a base64 encoded unicode fragment */
    if (s->mode) {
	/* '-' marks the end of a fragment */
	if (c == '-') {
	    /* special case: sequence +- creates output '+' */
	    if (s->mode == 1)
		convert_putc(rock->next, '+');
	    /* otherwise no output for the '-' */
	    s->mode = 0;
	    s->num_bits = 0;
	    s->codepoint = 0;
	}
	/* a normal char drops us out of base64 mode */
	else if (CHAR64(c) == XX) {
	    /* pass on the char */
	    convert_putc(rock->next, c);
	    /* and switch back to ASCII mode */
	    s->mode = 0;
	    /* XXX: warn if num_bits > 4 or codepoint != 0 */
	    s->num_bits = 0;
	    s->codepoint = 0;
	}
	/* base64 char - process it into the state machine */
	else {
	    s->mode = 2; /* we have some content, so don't process special +- */
	    /* add the 6 bits of value from this character */
	    s->codepoint = (s->codepoint << 6) + CHAR64(c);
	    s->num_bits += 6;
	    /* if we've got a full character's worth of bits, send it down 
	     * the line and keep the remainder for the next character */
	    if (s->num_bits >= 16) {
		s->num_bits -= 16;
		convert_putc(rock->next, (s->codepoint >> s->num_bits) & 0x7fff);
		s->codepoint &= ((1 << s->num_bits) - 1); /* avoid overflow by trimming */
	    }
	}
    }

    /* regular ASCII mode */
    else {
	/* '+' switches to base64 unicode mode */
	if (c == '+') {
	    s->mode = 1; /* switch mode, but no content processed yet */
	    s->codepoint = 0;
	    s->num_bits = 0;
	}
	/* regular ASCII char */
	else {
	    convert_putc(rock->next, c);
	}
    }
}

static void uni2searchform(struct convert_rock *rock, int c)
{
    struct canon_state *s = (struct canon_state *)rock->state;
    int i;
    int code;
    unsigned char table16, table8;

    /* invalid character becomes an Oxff - that's illegal utf-8,
     * so it won't match */
    if (c == 0xfffd) {
	convert_putc(rock->next, 0xff);
	return;
    }

    table16 = chartables_translation_block16[(c>>16) & 0xff];

    /* no translations */
    if (table16 == 255) {
	convert_putc(rock->next, c);
	return;
    }

    table8 = chartables_translation_block8[table16][(c>>8) & 0xff];

    /* no translations */
    if (table8 == 255) {
	convert_putc(rock->next, c);
	return;
    }

    /* use the xlate table */
    code = chartables_translation[table8][c & 0xff];

    /* case - zero length output */
    if (code == 0) {
	return;
    }

    /* special case: whitespace or control characters */
    if (code == ' ' || code == '\r' || code == '\n') {
	if (s->flags & CHARSET_SKIPSPACE) {
	    return;
	}
	if (s->flags & CHARSET_MERGESPACE) {
	    if (s->seenspace)
		return;
	    s->seenspace = 1;
	    code = ' '; /* one SPACE char */
	}
    }
    else
	s->seenspace = 0;

    /* case - one character output */
    if (code > 0) {
	convert_putc(rock->next, code);
	return;
    }

    /* case - multiple characters */
    for (i = -code; chartables_translation_multichar[i]; i++) {
	int c = chartables_translation_multichar[i];
	/* diacritical character range.  This duplicates the
	 * behaviour of Cyrus versions before 2.5 */
	if (s->flags & CHARSET_SKIPDIACRIT) {
	    if ((c & ~0xff) == 0x300)
		continue;
	}
	/* note: whitespace already stripped from multichar sequences... */
	convert_putc(rock->next, c);
    }
}

static void uni2utf8(struct convert_rock *rock, int c)
{
    if (c > 0xffff) {
	convert_putc(rock->next, 0xF0 + ((c >> 18) & 0x07));
	convert_putc(rock->next, 0x80 + ((c >> 12) & 0x3f));
	convert_putc(rock->next, 0x80 + ((c >>  6) & 0x3f));
	convert_putc(rock->next, 0x80 + ( c        & 0x3f));
    }
    else if (c > 0x7ff) {
	convert_putc(rock->next, 0xE0 + ((c >> 12) & 0x0f));
	convert_putc(rock->next, 0x80 + ((c >>  6) & 0x3f));
	convert_putc(rock->next, 0x80 + ( c        & 0x3f));
    }
    else if (c > 0x7f) {
	convert_putc(rock->next, 0xC0 + ((c >>  6) & 0x1f));
	convert_putc(rock->next, 0x80 + ( c        & 0x3f));
    }
    else {
	convert_putc(rock->next, c);
    }
}

static void byte2search(struct convert_rock *rock, int c)
{
    struct search_state *s = (struct search_state *)rock->state;
    int i, cur;
    unsigned char b = (unsigned char)c;

    if (c == 0xfffd) {
	c = 0xff; /* searchable by invalid character! */
    }

    /* check our "in_progress" matches to see if they're still valid */
    for (i = 0, cur = 0; i < s->max_start; i++) {
	/* no more active offsets */
	if (s->starts[i] == -1)
	    break;

	/* if we've passed one that's not ongoing, copy back */
	if (cur < i)
	    s->starts[cur] = s->starts[i];

	/* check that the substring is still maching */
	if (b == s->substr[s->offset - s->starts[i]]) {
	    if (s->offset - s->starts[i] == s->patlen - 1) {
		/* we're there! */
		s->havematch = 1;
	    }
	    else {
		/* keep this one, it's ongoing */
		cur++;
	    }
	}
    }
    /* starting a new one! */
    if (b == s->substr[0]) {
	/* have to treat this one specially! */
	if (s->patlen == 1)
	    s->havematch = 1;
	else
	    s->starts[cur++] = s->offset;
    }
    /* empty out any others that aren't being kept */
    while (cur < i) s->starts[cur++] = -1;

    /* increment the offset counter */
    s->offset++;
}

static void byte2buffer(struct convert_rock *rock, int c)
{
    struct buf *buf = (struct buf *)rock->state;

    buf_putc(buf, c & 0xff);
}

/* convert_rock manipulation routines */

static void table_switch(struct convert_rock *rock, int charset_num)
{
    struct table_state *state = (struct table_state *)rock->state;

    /* wipe any current state */
    memset(state, 0, sizeof(struct table_state)); 

    /* it's a table based lookup */
    if (chartables_charset_table[charset_num].table) {
	/* set up the initial table */
	state->curtable = state->initialtable
	    = chartables_charset_table[charset_num].table;
	rock->f = table2uni;
    }

    /* special case UTF-8 */
    else if (strstr(chartables_charset_table[charset_num].name, "utf-8")) {
	rock->f = utf8_2uni;
    }

    /* special case UTF-7 */
    else if (strstr(chartables_charset_table[charset_num].name, "utf-7")) {
	rock->f = utf7_2uni;
    }

    /* should never happen */
    else {
	exit(1);
	/* do something fatal here! */
    }
}

/* Extract a cstring from a buffer.  NOTE: caller must free the memory
 * themselves once this is called.  Resets the state.  If you don't
 * call this function then buffer_free will clean up */
static char *buffer_cstring(struct convert_rock *rock)
{
    struct buf *buf = (struct buf *)rock->state;

    return buf_release(buf);
}

static inline int search_havematch(struct convert_rock *rock)
{
    struct search_state *s = (struct search_state *)rock->state;
    return s->havematch;
}

/* conversion cleanup routines */

static void basic_free(struct convert_rock *rock)
{
    if (rock) {
	if (rock->state) free(rock->state);
	free(rock);
    }
}

static void search_free(struct convert_rock *rock)
{
    if (rock && rock->state) {
	struct search_state *s = (struct search_state *)rock->state;
	if (s->starts) free(s->starts);
    }
    basic_free(rock);
}

static void buffer_free(struct convert_rock *rock)
{
    if (rock && rock->state) {
	struct buf *buf = (struct buf *)rock->state;
	buf_free(buf);
    }
    basic_free(rock);
}

static void convert_free(struct convert_rock *rock) {
    struct convert_rock *next;
    while (rock) {
	next = rock->next;
	if (rock->cleanup)
	    rock->cleanup(rock);
	else 
	    basic_free(rock);
	rock = next;
    }
}

/* converter initialisation routines */

static struct convert_rock *qp_init(int isheader, struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    struct qp_state *s = xzmalloc(sizeof(struct qp_state));
    s->isheader = isheader;
    rock->state = (void *)s;
    rock->f = qp2byte;
    rock->next = next;
    return rock;
}

static struct convert_rock *b64_init(struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    rock->state = xzmalloc(sizeof(struct b64_state));
    rock->f = b64_2byte;
    rock->next = next;
    return rock;
}

static struct convert_rock *stripnl_init(struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    rock->f = stripnl2uni;
    rock->next = next;
    return rock;
}

static struct convert_rock *canon_init(int flags, struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    struct canon_state *s = xzmalloc(sizeof(struct canon_state));
    s->flags = flags;
    rock->f = uni2searchform;
    rock->state = s;
    rock->next = next;
    return rock;
}

static struct convert_rock *uni_init(struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    rock->f = uni2utf8;
    rock->next = next;
    return rock;
}

static struct convert_rock *table_init(int charset_num, struct convert_rock *next)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    rock->state = xzmalloc(sizeof(struct table_state));
    rock->next = next;
    table_switch(rock, charset_num);
    return rock;
}

static struct convert_rock *search_init(const char *substr, comp_pat *pat) {
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    struct search_state *s = xzmalloc(sizeof(struct search_state));
    struct comp_pat_s *p = (struct comp_pat_s *)pat;
    int i;

    /* copy in tracking vars */
    s->max_start = p->max_start;
    s->patlen = p->patlen;
    s->substr = (unsigned char *)substr;

    /* allocate tracking space and initialise to "no match" */
    s->starts = xmalloc(s->max_start * sizeof(size_t));
    for (i = 0; i < s->max_start; i++) {
	s->starts[i] = -1;
    }

    /* set up the rock */
    rock->f = byte2search;
    rock->cleanup = search_free;
    rock->state = (void *)s;

    return rock;
}

static struct convert_rock *buffer_init(void)
{
    struct convert_rock *rock = xzmalloc(sizeof(struct convert_rock));
    struct buf *buf = xzmalloc(sizeof(struct buf));

    rock->f = byte2buffer;
    rock->cleanup = buffer_free;
    rock->state = (void *)buf;

    return rock;
}

/* API */

/*
 * Return the name of the given character set number, or NULL if
 * not known.
 */
EXPORTED const char *charset_name(charset_index i)
{
    return (i >= 0 && i < chartables_num_charsets ?
	    chartables_charset_table[i].name : "unknown");
}

/*
 * Lookup the character set 'name'.  Returns the character set number
 * or -1 if there is no matching character set.
 */
EXPORTED int charset_lookupname(const char *name)
{
    int i;

    /* translate to canonical name */
    for (i = 0; charset_aliases[i].name; i++) {
	if (!strcasecmp(name, charset_aliases[i].name)) {
	    name = charset_aliases[i].canon_name;
	    break;
	}
    }

    /* look up canonical name */
    for (i = 0; i < chartables_num_charsets; i++) {
	if (!strcasecmp(name, chartables_charset_table[i].name)) 
	    return i;
    }

    return -1;
}

static int lookup_buf(const char *buf, int len)
{
    char *name = xstrndup(buf, len);
    int res = charset_lookupname(name);
    free(name);
    return res;
}

/*
 * Convert the string 's' in the character set numbered 'charset'
 * into canonical searching form.  Returns a newly allocated string
 * which must be free()d by the caller.
 */
EXPORTED char *charset_convert(const char *s, int charset, int flags)
{
    struct convert_rock *input, *tobuffer;
    char *res;

    if (!s) return 0;

    if (charset < 0 || charset >= chartables_num_charsets) 
	return xstrdup("X");

    /* set up the conversion path */
    tobuffer = buffer_init();
    input = uni_init(tobuffer);
    input = canon_init(flags, input);
    input = table_init(charset, input);

    /* do the conversion */
    convert_cat(input, s);

    /* extract the result */
    res = buffer_cstring(tobuffer);

    /* clean up */
    convert_free(input);

    return res;
}

EXPORTED char *charset_utf8_to_searchform(const char *s, int flags)
{
    int charset = charset_lookupname("utf-8");
    return charset_convert(s, charset, flags);
}

/* Convert from a given charset and encoding into utf8 */
EXPORTED char *charset_to_utf8(const char *msg_base, size_t len, int charset, int encoding)
{
    struct convert_rock *input, *tobuffer;
    char *res;

    /* Initialize character set mapping */
    if (charset < 0 || charset >= chartables_num_charsets) 
	return 0;

    /* check for trivial search */
    if (len == 0)
	return xstrdup("");

    /* set up the conversion path */
    tobuffer = buffer_init();
    input = uni_init(tobuffer);
    input = table_init(charset, input);

    /* choose encoding extraction if needed */
    switch (encoding) {
    case ENCODING_NONE:
	break;

    case ENCODING_QP:
	input = qp_init(0, input);
	break;

    case ENCODING_BASE64:
	input = b64_init(input);
	/* XXX have to have nl-mapping base64 in order to
	 * properly count \n as 2 raw characters
	 */
	break;

    default:
	/* Don't know encoding--nothing can match */
	convert_free(input);
	return 0;
    }

    convert_catn(input, msg_base, len);
    res = buffer_cstring(tobuffer);
    convert_free(input);

    return res;
}

static void mimeheader_cat(struct convert_rock *target, const char *s)
{
    struct convert_rock *input, *stripnl;
    int eatspace = 0;
    const char *start, *endcharset, *encoding, *end;
    int len;
    int charset;
    const char *p;

    if (!s) return;

    /* set up the conversion path */
    input = table_init(0, target);
    /* note: we assume the caller of this function has already 
     * determined that all newlines are followed by whitespace */
    stripnl = stripnl_init(input);

    start = s;
    while ((start = (const char*) strchr(start, '=')) != 0) {
	start++;
	if (*start != '?') continue;
	encoding = (const char*) strchr(start+1, '?');
	if (!encoding) continue;
	endcharset =
	    (const char*) strchr(start+1, '*'); /* Language code delimiter */
	if (!endcharset || endcharset > encoding) endcharset = encoding;
	if (encoding[1] != 'b' && encoding[1] != 'B' &&
	    encoding[1] != 'q' && encoding[1] != 'Q') continue;
	if (encoding[2] != '?') continue;
	end = (const char*) strchr(encoding+3, '?');
	if (!end || end[1] != '=') continue;

	/*
	 * We have recognized a valid 1522-word.
	 * Copy over leading text, unless it consists entirely of 
	 * whitespace and is between two 1522-words.
	 */
	if (eatspace) {
	    for (p = s; p < (start-1) && Uisspace(*p); p++);
	    if (p < (start-1)) eatspace = 0;
	}
	if (!eatspace) {
	    len = start - s - 1;
	    table_switch(input, 0); /* US_ASCII */
	    convert_catn(stripnl, s, len);
	}

	/*
	 * Get the 1522-word's character set
	 */
	start++;
	charset = lookup_buf(start, endcharset-start);
	if (charset < 0) {
	    /* Unrecognized charset, nothing will match here */
	    convert_putc(input, 0xfffd); /* unknown character */
	}
	else {
	    struct convert_rock *extract;

	    table_switch(input, charset);

	    /* choose decoder */
	    if (encoding[1] == 'q' || encoding[1] == 'Q') {
		extract = qp_init(1, input);
	    }
	    else {
		extract = b64_init(input);
	    }
	    /* convert */
	    p = encoding+3;
	    convert_catn(extract, p, end - p);
	    /* clean up */
	    basic_free(extract);
	}

	/* Prepare for the next iteration */
	s = start = end+2;
	eatspace = 1;
    }

    /* Copy over the tail part of the input string */
    if (*s) {
	table_switch(input, 0); /* US_ASCII */
	convert_cat(stripnl, s);
    }

    /* just free these ones, the rest can be cleaned up by the sender */
    basic_free(stripnl);
    basic_free(input);
}

/*
 * Decode MIME strings (per RFC 2047) in 's'.  Returns a newly allocated
 * string, contining 's' in canonical searching form, which must be
 * free()d by the caller.
 */
EXPORTED char *charset_decode_mimeheader(const char *s, int flags)
{
    struct convert_rock *tobuffer, *input;
    char *res;

    if (!s) return NULL;

    tobuffer = buffer_init();
    input = uni_init(tobuffer);
    input = canon_init(flags, input);

    mimeheader_cat(input, s);
 
    res = buffer_cstring(tobuffer);

    convert_free(input);

    return res;
}

/*
 * Decode MIME strings (per RFC 2047) in 's'.  Returns a newly allocated
 * string, containing the decoded string, which must be free()d by the
 * caller.
 */
EXPORTED char *charset_parse_mimeheader(const char *s)
{
    struct convert_rock *tobuffer, *input;
    char *res;

    if (!s) return NULL;

    tobuffer = buffer_init();
    input = uni_init(tobuffer);

    mimeheader_cat(input, s);
 
    res = buffer_cstring(tobuffer);

    convert_free(input);

    return res;
}

EXPORTED int charset_search_mimeheader(const char *substr, comp_pat *pat,
			      const char *s, int flags)
{
    struct convert_rock *input, *tosearch;
    int res;

    tosearch = search_init(substr, pat);
    input = uni_init(tosearch);
    input = canon_init(flags, input);

    mimeheader_cat(input, s);
 
    res = search_havematch(tosearch);

    convert_free(input);

    return res;
}

/* Compile a search pattern for later comparison.  We just count
 * how long the string is, and how many times the first character
 * occurs.  Later optimisation could reduce the max_start by
 * deeper analysis of the possible paths through the string, but
 * this is a good absolute maximum, and it just means a few more
 * bytes get allocated... */
EXPORTED comp_pat *charset_compilepat(const char *s)
{
    struct comp_pat_s *pat = xzmalloc(sizeof(struct comp_pat_s));
    const char *p = s;
    /* count occurances */
    while (*p) {
	if (*p == *s) pat->max_start++; 
	pat->patlen++;
	p++;
    }
    return (comp_pat *)pat;
}

/*
 * Free the compiled pattern 'pat'
 */
EXPORTED void charset_freepat(comp_pat *pat)
{
    free((struct comp_pat_s *)pat);
}

/*
 * Search for the string 'substr', with compiled pattern 'pat'
 * in the string 's', with length 'len'.  Return nonzero if match
 *
 * Uses the to_search target directly.  Assumes 's' is already
 * in search normal form (i.e. from a cache file)
 */
EXPORTED int charset_searchstring(const char *substr, comp_pat *pat,
			 const char *s, size_t len, int flags)
{
    struct convert_rock *tosearch;
    struct convert_rock *input;
    int charset = charset_lookupname("utf-8");
    int res;

    if (!substr[0])
	return 1; /* zero length string always matches */

    /* set up the search handler */
    tosearch = search_init(substr, pat);

    /* and the input stream */
    input = uni_init(tosearch);
    input = canon_init(flags, input);
    input = table_init(charset, input);

    /* feed the handler */
    while (len-- > 0) {
	convert_putc(input, (unsigned char)*s++);
	if (search_havematch(tosearch)) break; /* shortcut if there's a match */
    }

    /* copy the value */
    res = search_havematch(tosearch);

    /* clean up */
    convert_free(input);

    return res;
}

/*
 * Search for the string 'substr' in the next 'len' bytes of 
 * 'msg_base'.  
 * 'charset' and 'encoding' specify the character set and 
 * content transfer encoding of the data, respectively.
 * Returns nonzero iff the string was found.
 */
EXPORTED int charset_searchfile(const char *substr, comp_pat *pat,
		       const char *msg_base, size_t len,
		       int charset, int encoding, int flags)
{
    struct convert_rock *input, *tosearch;
    size_t i;
    int res;

    /* Initialize character set mapping */
    if (charset < 0 || charset >= chartables_num_charsets) 
	return 0;

    /* check for trivial search */
    if (strlen(substr) == 0)
	return 1;

    /* set up the conversion path */
    tosearch = search_init(substr, pat);
    input = uni_init(tosearch);
    input = canon_init(flags, input);
    input = table_init(charset, input);

    /* choose encoding extraction if needed */
    switch (encoding) {
    case ENCODING_NONE:
	break;

    case ENCODING_QP:
	input = qp_init(0, input);
	break;

    case ENCODING_BASE64:
	input = b64_init(input);
	/* XXX have to have nl-mapping base64 in order to
	 * properly count \n as 2 raw characters
	 */
	break;

    default:
	/* Don't know encoding--nothing can match */
	convert_free(input);
	return 0;
    }

    /* implement the loop here so we can check on the search each time */
    for (i = 0; i < len; i++) {
	convert_putc(input, msg_base[i]);
	if (search_havematch(tosearch)) break;
    }

    res = search_havematch(tosearch); /* copy before we free it */

    convert_free(input);

    return res;
}

/* This is based on charset_searchfile above. */
EXPORTED int charset_extract(search_text_receiver_t *receiver,
			     const struct buf *data,
			     int charset, int encoding, int flags)
{
    struct convert_rock *input, *tobuffer;
    struct buf *out;
    size_t i;

    /* Initialize character set mapping */
    if (charset < 0 || charset >= chartables_num_charsets) 
	return 0;

    /* set up the conversion path */
    tobuffer = buffer_init();
    input = uni_init(tobuffer);
    input = canon_init(flags, input);
    input = table_init(charset, input);

    switch (encoding) {
    case ENCODING_NONE:
	break;

    case ENCODING_QP:
	input = qp_init(0, input);
	break;

    case ENCODING_BASE64:
	input = b64_init(input);
	/* XXX have to have nl-mapping base64 in order to
	 * properly count \n as 2 raw characters
	 */
	break;

    default:
	/* Don't know encoding--nothing can match */
	convert_free(input);
	return 0;
    }

    /* point to the buffer for easy block sending */
    out = (struct buf *)tobuffer->state;

    for (i = 0; i < data->len; i++) {
	convert_putc(input, data->s[i]);

	/* process a block of output every so often */
	if (buf_len(out) > 4096) {
	    receiver->append_text(receiver, out);
	    buf_reset(out);
	}
    }
    if (out->len) { /* finish it */
	receiver->append_text(receiver, out);
    }

    convert_free(input);

    return 1;
}

/*
 * Decode the MIME body part (per RFC 2045) of @len bytes located at
 * @msg_base having the content transfer @encoding.  Returns a pointer
 * to decoded bytes.  The number of decoded bytes is returned in
 * *@outlen.  Depending on the encoding, a newly allocated buffer may be
 * written to *@decbuf, which should be free()d by the caller if it not
 * zero.  Note that the return value may point to either @msg_base or
 * @decbuf, so @decbuf should not be free()d until the return value has
 * been used.
 */
EXPORTED const char *charset_decode_mimebody(const char *msg_base, size_t len, int encoding,
				    char **decbuf, size_t *outlen)
{
    struct convert_rock *input, *tobuffer;

    *decbuf = NULL;
    *outlen = 0;

    switch (encoding) {
    case ENCODING_NONE:
	*outlen = len;
	return msg_base;

    case ENCODING_QP:
	tobuffer = buffer_init();
	input = qp_init(0, tobuffer);
	break;

    case ENCODING_BASE64:
	tobuffer = buffer_init();
	input = b64_init(tobuffer);
	break;

    default:
	/* Don't know encoding--nothing can match */
	return NULL;
    }

    convert_catn(input, msg_base, len);

    /* extract the string from the buffer */
    {
	struct buf *buf = (struct buf *)tobuffer->state;
	*outlen = buf->len;
	*decbuf = buf_release(buf);
    }

    convert_free(input);

    if (!*decbuf) {
	/* didn't get a result - maybe blank input, don't return NULL */
	*outlen = len;
	return msg_base;
    }

    return *decbuf;
}

/*
 * Base64 encode the MIME body part (per RFC 2045) of 'len' bytes located at
 * 'msg_base'.  Encodes into 'retval' which must large enough to
 * accomodate the encoded data.  Returns the number of encoded bytes in
 * 'outlen' and the number of encoded lines in 'outlines'.
 *
 * May be called with 'msg_base' as NULL to get the number of encoded
 * bytes for allocating 'retval' of the proper size.
 */
#define BASE64_MAX_LINE_LEN  72

static char base_64[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

EXPORTED char *charset_encode_mimebody(const char *msg_base, size_t len,
    char *retval, size_t *outlen, int *outlines)
{
    const unsigned char *s;
    unsigned char s0, s1, s2;
    char *d;
    int b64_len, b64_lines, cnt;

    b64_len = ((len + 2) / 3) * 4;
    b64_lines = (b64_len + BASE64_MAX_LINE_LEN - 1) / BASE64_MAX_LINE_LEN;

    /* account for CRLF added to each line */
    b64_len += 2 * b64_lines;

    if (outlen) *outlen = b64_len;
    if (outlines) *outlines = b64_lines;

    if (!msg_base) return NULL;

    for (s = (const unsigned char*) msg_base, d = retval, cnt = 0; len;
	 s += 3, d += 4, cnt += 4) { /* process tuplets */
	if (cnt == BASE64_MAX_LINE_LEN) {
	    /* reset line len count, add CRLF */
	    cnt = 0;
	    *d++ = '\r';
	    *d++ = '\n';
	}

	s0 = s[0];
	s1 = --len ? s[1] : 0;
	/* byte 1: high 6 bits (1) */
	d[0] = base_64[s0 >> 2];
	/* byte 2: low 2 bits (1), high 4 bits (2) */
	d[1] = base_64[((s0 & 0x3) << 4) | ((s1 & 0xf0) >> 4)];
	if (len) {
	    s2 = --len ? s[2] : 0;
	    /* byte 3: low 4 bits (2), high 2 bits (3) */
	    d[2] = base_64[((s1 & 0xf) << 2) | ((s2 & 0xc0) >> 6)];
	} else {
	    /* byte 3: pad */
	    d[2] = '=';
	}
	if (len) {
	    --len;
	    /* byte 4: low 6 bits (3) */
	    d[3] = base_64[s2 & 0x3f];
	} else {
	    /* byte 4: pad */
	    d[3] = '=';
	}
    }

    /* add final CRLF */
    *d++ = '\r';
    *d++ = '\n';

    return (b64_len ? retval : NULL);
}

/* returns a buffer which the caller must free */
EXPORTED char *charset_encode_mimeheader(const char *header, size_t len)
{
    struct buf buf = BUF_INITIALIZER;
    size_t n;
    int need_quote = 0;

    if (!header) return NULL;

    if (!len) len = strlen(header);

    for (n = 0; n < len; n++) {
	unsigned char this = header[n];
	if (QPSAFECHAR[this] || this == ' ') continue;
	need_quote = 1;
	break;
    }

    if (need_quote) {
	buf_printf(&buf, "=?UTF-8?Q?");
	for (n = 0; n < len; n++) {
	    unsigned char this = header[n];
	    if (QPSAFECHAR[this]) {
		buf_putc(&buf, (char)this);
	    }
	    else {
		buf_printf(&buf, "=%02X", this);
	    }
	}
	buf_printf(&buf, "?=");
    }
    else {
	buf_setmap(&buf, header, len);
    }

    return buf_release(&buf);
}

