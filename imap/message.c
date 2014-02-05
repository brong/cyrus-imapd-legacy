/* message.c -- Message manipulation/parsing
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

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <stdlib.h>

#include "arrayu64.h"
#include "assert.h"
#include "crc32.h"
#include "dlist.h"
#include "exitcodes.h"
#include "imap/imap_err.h"
#include "prot.h"
#include "hash.h"
#include "map.h"
#include "mailbox.h"
#include "message.h"
#include "message_priv.h"
#include "message_guid.h"
#include "parseaddr.h"
#include "charset.h"
#include "stristr.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "strarray.h"
#include "ptrarray.h"
#include "global.h"
#include "retry.h"
#include "imap/rfc822_header.h"
#include "rfc822tok.h"
#include "times.h"

#define DEBUG 0

/* Message being parsed */
struct msg {
    const char *base;
    unsigned long len;
    unsigned long offset;
    int encode;
};

#define MAX_FIELDNAME_LENGTH   256

/* (draft standard) MIME tspecials */
#define TSPECIALS "()<>@,;:\\\"/[]?="

/* Default MIME Content-type */
#define DEFAULT_CONTENT_TYPE "TEXT/PLAIN; CHARSET=us-ascii"

static int message_parse_body(struct msg *msg,
				 struct body *body,
				 const char *defaultContentType,
				 strarray_t *boundaries);

static int message_parse_headers(struct msg *msg,
				    struct body *body,
				    const char *defaultContentType,
				    strarray_t *boundaries);
static void message_parse_address(const char *hdr, struct address **addrp);
static void message_parse_encoding(const char *hdr, char **hdrp);
static void message_parse_charset(const struct body *body,
				  int *encoding, int *charset);
static void message_parse_string(const char *hdr, char **hdrp);
static void message_parse_header(const char *hdr, struct buf *buf);
static void message_parse_type(const char *hdr, struct body *body);
static void message_parse_disposition(const char *hdr, struct body *body);
static void message_parse_params(const char *hdr, struct param **paramp);
static void message_fold_params(struct param **paramp);
static void message_parse_language(const char *hdr, struct param **paramp);
static void message_parse_rfc822space(const char **s);
static void message_parse_received_date(const char *hdr, char **hdrp);

static void message_parse_multipart(struct msg *msg,
				       struct body *body,
				       strarray_t *boundaries);
static void message_parse_content(struct msg *msg,
				     struct body *body,
				     strarray_t *boundaries);

static char *message_getline(struct buf *, struct msg *msg);
static int message_pendingboundary(const char *s, int slen, strarray_t *);

static void message_write_envelope(struct buf *buf, const struct body *body);
static void message_write_address(struct buf *buf,
				  const struct address *addrlist);
static void message_write_text_lcase(struct buf *buf, const char *s);
static void message_write_section(struct buf *buf, const struct body *body);
static void message_write_charset(struct buf *buf, const struct body *body);
static void message_write_searchaddr(struct buf *buf,
				     const struct address *addrlist);
static int message_need(message_t *m, unsigned int need);
static void message_yield(message_t *m, unsigned int yield);
static int message2_parse_header(part_t *p, const struct buf *map);
static int message2_parse_multipart(part_t *p, segment_t *body);
static int message2_map_segment(message_t *m, segment_t *s, struct buf *buf);
static int message2_expand_segment(message_t *m, segment_t *seg);
static int message2_map_file(message_t *m, const char *fname);
static int message2_parse_cheader(message_t *m);
static int message2_parse_cenvelope(message_t *m);
static int message2_parse_csections(message_t *m);
static int message2_parse_cbodystructure(message_t *m);

static segment_t unfinished_seg = {
    .id = ID_UNFINISHED, .children = &unfinished_seg
};
static hash_table descs_by_name = HASH_TABLE_INITIALIZER;
static ptrarray_t descs_by_id = PTRARRAY_INITIALIZER;
static unsigned int next_field_id = ID_PREALLOCATED_LAST+1;

/*
 * Convert a string to uppercase.  Returns the string.
 *
 * This differs from the ucase() function in lib/util.c by using the
 * libc tolower() instead of our hardcoded builtin lookup table.
 * Whether this is a good thing is unclear, but that's what the old code
 * did so I'm going to preserve it - gnb
 */
static char *message_ucase(char *s)
{
    char *p;

    for (p = s ; *p ; p++)
	if (Uislower(*p))
	    *p = toupper((int) *p);
    return s;
}

/*
 * Copy a message of 'size' bytes from 'from' to 'to',
 * ensuring minimal RFC-822 compliance.
 *
 * Caller must have initialized config_* routines (with cyrus_init) to read
 * imapd.conf before calling.
 */
EXPORTED int message_copy_strict(struct protstream *from, FILE *to,
				 unsigned size, int allow_null)
{
    char buf[4096+1];
    unsigned char *p, *endp;
    int r = 0;
    size_t n;
    int sawcr = 0, sawnl;
    int reject8bit = config_getswitch(IMAPOPT_REJECT8BIT);
    int munge8bit = config_getswitch(IMAPOPT_MUNGE8BIT);
    int inheader = 1, blankline = 1;

    while (size) {
	n = prot_read(from, buf, size > 4096 ? 4096 : size);
	if (!n) {
	    syslog(LOG_ERR, "IOERROR: reading message: unexpected end of file");
	    return IMAP_IOERROR;
	}

	buf[n] = '\0';

	/* Quick check for NUL in entire buffer, if we're not allowing it */
	if (!allow_null && (n != strlen(buf))) {
	    r = IMAP_MESSAGE_CONTAINSNULL;
	}

	size -= n;
	if (r) continue;

	for (p = (unsigned char *)buf, endp = p + n; p < endp; p++) {
	    if (!*p && inheader) {
		/* NUL in header is always bad */
		r = IMAP_MESSAGE_CONTAINSNULL;
	    }
	    else if (*p == '\n') {
		if (!sawcr && (inheader || !allow_null))
		    r = IMAP_MESSAGE_CONTAINSNL;
		sawcr = 0;
		if (blankline) {
		    inheader = 0;
		}
		blankline = 1;
	    }
	    else if (*p == '\r') {
		sawcr = 1;
	    }
	    else {
		sawcr = 0;
		blankline = 0;
		if (inheader && *p >= 0x80) {
		    if (reject8bit) {
			/* We have been configured to reject all mail of this
			   form. */
			if (!r) r = IMAP_MESSAGE_CONTAINS8BIT;
		    } else if (munge8bit) {
			/* We have been configured to munge all mail of this
			   form. */
			*p = 'X';
		    }
		}
	    }
	}

	fwrite(buf, 1, n, to);
    }

    if (r) return r;
    fflush(to);
    if (ferror(to) || fsync(fileno(to))) {
	syslog(LOG_ERR, "IOERROR: writing message: %m");
	return IMAP_IOERROR;
    }
    rewind(to);

    /* Go back and check headers */
    sawnl = 1;
    for (;;) {
	if (!fgets(buf, sizeof(buf), to)) {
	    return sawnl ? 0 : IMAP_MESSAGE_BADHEADER;
	}

	/* End of header section */
	if (sawnl && buf[0] == '\r') return 0;

	/* Check for valid header name */
	if (sawnl && buf[0] != ' ' && buf[0] != '\t') {
	    if (buf[0] == ':') return IMAP_MESSAGE_BADHEADER;
      if (strstr(buf, "From ") != buf)
	    for (p = (unsigned char *)buf; *p != ':'; p++) {
		if (*p <= ' ') return IMAP_MESSAGE_BADHEADER;
	    }
	}

	/* Used to be some 8bit checks here but those were moved above so that 
	   we could do something other than refuse the message.
	   Unfortunately, we still need to look for the end of the string. */
	for(p = (unsigned char*) buf; *p; p++);
	
	sawnl = (p > (unsigned char *)buf) && (p[-1] == '\n');
    }
}

EXPORTED int message_parse(const char *fname, struct index_record *record)
{
    struct body *body = NULL;
    FILE *f;
    int r;

    f = fopen(fname, "r");
    if (!f) return IMAP_IOERROR;

    r = message_parse_file(f, NULL, NULL, &body);
    if (!r) r = message_create_record(record, body);

    fclose(f);

    if (body) {
	message_free_body(body);
	free(body);
    }

    return r;
}

/*
 * Parse the message 'infile'.
 *
 * The caller MUST free the allocated body struct.
 *
 * If msg_base/msg_len are non-NULL, the file will remain memory-mapped
 * and returned to the caller.  The caller MUST unmap the file.
 */
EXPORTED int message_parse_file(FILE *infile,
		       const char **msg_base, size_t *msg_len,
		       struct body **body)
{
    int fd = fileno(infile);
    struct stat sbuf;
    const char *tmp_base;
    size_t tmp_len;
    int unmap = 0, r;

    if (!msg_base) {
	unmap = 1;
	msg_base = &tmp_base;
	msg_len = &tmp_len;
    }
    *msg_base = NULL;
    *msg_len = 0;

    if (fstat(fd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on new message in spool: %m");
	fatal("can't fstat message file", EC_OSFILE);
    }
    map_refresh(fd, 1, msg_base, msg_len, sbuf.st_size,
		"new message", 0);

    if (!*msg_base || !*msg_len)
	return IMAP_IOERROR; /* zero length file? */

    if (!*body) *body = (struct body *) xmalloc(sizeof(struct body));
    r = message_parse_mapped(*msg_base, *msg_len, *body);

    if (unmap) map_free(msg_base, msg_len);

    return r;
}


/*
 * Parse the message 'infile'.
 *
 * The caller MUST free the allocated body struct.
 *
 * This function differs from message_parse_file() in that we create a
 * writable buffer rather than memory-mapping the file, so that binary
 * data can be encoded into the buffer.  The file is rewritten upon
 * completion.
 *
 * XXX can we do this with mmap()?
 */
EXPORTED int message_parse_binary_file(FILE *infile, struct body **body)
{
    int fd = fileno(infile);
    struct stat sbuf;
    struct msg msg;
    size_t n;

    if (fstat(fd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on new message in spool: %m");
	fatal("can't fstat message file", EC_OSFILE);
    }
    msg.len = sbuf.st_size;
    msg.base = xmalloc(msg.len);
    msg.offset = 0;
    msg.encode = 1;

    lseek(fd, 0L, SEEK_SET);

    n = retry_read(fd, (char*) msg.base, msg.len);
    if (n != msg.len) {
	syslog(LOG_ERR, "IOERROR: reading binary file in spool: %m");
	return IMAP_IOERROR;
    }

    if (!*body) *body = (struct body *) xmalloc(sizeof(struct body));
    message_parse_body(&msg, *body,
		       DEFAULT_CONTENT_TYPE, (strarray_t *)0);

    message_guid_generate(&(*body)->guid, msg.base, msg.len);

    lseek(fd, 0L, SEEK_SET);
    n = retry_write(fd, msg.base, msg.len);

    free((char*) msg.base);

    if (n != msg.len || fsync(fd)) {
	syslog(LOG_ERR, "IOERROR: rewriting binary file in spool: %m");
	return IMAP_IOERROR;
    }

    return 0;
}


/*
 * Parse the message at 'msg_base' of length 'msg_len'.
 */
EXPORTED int message_parse_mapped(const char *msg_base, unsigned long msg_len,
			 struct body *body)
{
    struct msg msg;

    msg.base = msg_base;
    msg.len = msg_len;
    msg.offset = 0;
    msg.encode = 0;

    message_parse_body(&msg, body,
		       DEFAULT_CONTENT_TYPE, (strarray_t *)0);

    message_guid_generate(&body->guid, msg_base, msg_len);

    return 0;
}

/*
 * Prune the header section in buf to include only those headers
 * listed in headers or (if headers_not is non-empty) those headers
 * not in headers_not.
 */
void message_pruneheader(char *buf, const strarray_t *headers,
			 const strarray_t *headers_not)
{
    char *p, *colon, *nextheader;
    int goodheader;
    char *endlastgood = buf;
    char **l;
    int count = 0;
    int maxlines = config_getint(IMAPOPT_MAXHEADERLINES);

    p = buf;
    while (*p && *p != '\r') {
	colon = strchr(p, ':');
	if (colon && headers_not && headers_not->count) {
	    goodheader = 1;
	    for (l = headers_not->data ; *l ; l++) {
		if ((size_t) (colon - p) == strlen(*l) &&
		    !strncasecmp(p, *l, colon - p)) {
		    goodheader = 0;
		    break;
		}
	    }
	} else {
	    goodheader = 0;
	}
	if (colon && headers && headers->count) {
	    for (l = headers->data ; *l ; l++) {
		if ((size_t) (colon - p) == strlen(*l) &&
		    !strncasecmp(p, *l, colon - p)) {
		    goodheader = 1;
		    break;
		}
	    }
	}

	nextheader = p;
	do {
	    nextheader = strchr(nextheader, '\n');
	    if (nextheader) nextheader++;
	    else nextheader = p + strlen(p);
	} while (*nextheader == ' ' || *nextheader == '\t');

	if (goodheader) {
	    if (endlastgood != p) {
		/* memmove and not strcpy since this is all within a
		 * single buffer */
		memmove(endlastgood, p, strlen(p) + 1);
		nextheader -= p - endlastgood;
	    }
	    endlastgood = nextheader;
	}
	p = nextheader;

	/* stop giant headers causing massive loops */
	if (maxlines) {
	    count++;
	    if (count > maxlines) break;
	}
    }

    *endlastgood = '\0';
}

static void message_find_part(struct body *body, const char *section,
			      const char **content_types,
			      const char *msg_base, unsigned long msg_len,
			      struct bodypart ***parts, int *n)
{
    int match;
    const char **type;
    char nextsection[128];

    for (match = 0, type = content_types; !match && *type; type++) {
	const char *subtype = strchr(*type, '/');
	size_t tlen = subtype ? (size_t) (subtype++ - *type) : strlen(*type);

	if ((!(*type)[0] || (tlen == strlen(body->type) &&
			     !strncasecmp(body->type, *type, tlen))) &&
	    (!subtype || !subtype[0] || !strcasecmp(body->subtype, subtype))) {
	    match = 1;
	}
    }

    if (match) {
	/* matching part, sanity check the size against the mmap'd file */
	if ((unsigned long) body->content_offset + body->content_size > msg_len) {
	    syslog(LOG_ERR, "IOERROR: body part exceeds size of message file");
	    fatal("body part exceeds size of message file", EC_OSFILE);
	}

	if (!body->decoded_body) {
	    int encoding, charset;
	    message_parse_charset(body, &encoding, &charset);
	    if (charset < 0) charset = 0; /* unknown, try ASCII */
	    body->decoded_body = charset_to_utf8(
		msg_base + body->content_offset, body->content_size,
		charset, encoding); /* returns a cstring */
	}

	/* grow the array and add the new part */
	*parts = xrealloc(*parts, (*n+2)*sizeof(struct bodypart *));
	(*parts)[*n] = xmalloc(sizeof(struct bodypart));
	strlcpy((*parts)[*n]->section, section, sizeof((*parts)[*n]->section));
	(*parts)[*n]->decoded_body = body->decoded_body;
	(*parts)[++(*n)] = NULL;
    }
    else if (!strcmp(body->type, "MULTIPART")) {
	int i;

	for (i = 0; i < body->numparts; i++) {
	    snprintf(nextsection, sizeof(nextsection), "%s.%d", section, i+1);
	    message_find_part(&body->subpart[i], nextsection, content_types,
			      msg_base, msg_len, parts, n);
	}
    }
    else if (!strcmp(body->type, "MESSAGE") &&
	     !strcmp(body->subtype, "RFC822")) {
	snprintf(nextsection, sizeof(nextsection), "%s.1", section);
	message_find_part(body->subpart, nextsection, content_types,
			  msg_base, msg_len, parts, n);
    }
}

/*
 * Fetch the bodypart(s) which match the given content_type and return
 * them as an allocated array.
 *
 * The caller MUST free the array of allocated bodypart(s).
 */
EXPORTED void message_fetch_part(struct message_content *msg,
				 const char **content_types,
				 struct bodypart ***parts)
{
    int n = 0;  /* running count of the number of matching parts */

    *parts = NULL;
    message_find_part(msg->body, "1", content_types,
		      msg->base, msg->len, parts, &n);
}

/*
 * Appends the message's cache information to the cache file
 * and fills in appropriate information in the index record pointed to
 * by 'record'.
 */
HIDDEN int message_create_record(struct index_record *record,
			  const struct body *body)
{
    if (!record->internaldate) {
	if (body->received_date &&
		config_getenum(IMAPOPT_INTERNALDATE_HEURISTIC) 
		== IMAP_ENUM_INTERNALDATE_HEURISTIC_RECEIVEDHEADER)
	    time_from_rfc822(body->received_date, &record->internaldate);
    }

    /* used for sent time searching, truncated to day with no TZ */
    if (day_from_rfc822(body->date, &record->sentdate) < 0)
	record->sentdate = 0;

    /* used for sent time sorting, full gmtime of Date: header */
    if (time_from_rfc822(body->date, &record->gmtime) < 0)
	record->gmtime = 0;

    record->size = body->header_size + body->content_size;
    record->header_size = body->header_size;
    record->content_lines = body->content_lines;
    message_guid_copy(&record->guid, &body->guid);

    message_write_cache(record, body);

    return 0;
}

static enum rfc822_header
message_header_lookup(const char *buf, const char **valp)
{
    unsigned int len = strcspn(buf, ":\r\n");
    if (buf[len] != ':')
	return RFC822_BAD;
    if (valp)
	*valp = buf+len+1;
    return rfc822_header_from_string_len(buf, len);
}


/*
 * Parse a body-part
 */
static int message_parse_body(struct msg *msg, struct body *body,
			      const char *defaultContentType,
			      strarray_t *boundaries)
{
    strarray_t newboundaries = STRARRAY_INITIALIZER;
    int sawboundary;

    memset(body, 0, sizeof(struct body));
    buf_init(&body->cacheheaders);

    /* No passed-in boundary structure, create a new, empty one */
    if (!boundaries) {
	boundaries = &newboundaries;
	/* We're at top-level--preallocate space to store cached headers */
	buf_ensure(&body->cacheheaders, 1024);
    }

    sawboundary = message_parse_headers(msg, body, defaultContentType,
					boundaries);

    /* Recurse according to type */
    if (strcmp(body->type, "MULTIPART") == 0) {
	if (!sawboundary) {
	    message_parse_multipart(msg, body, boundaries);
	}
    }
    else if (strcmp(body->type, "MESSAGE") == 0 &&
	strcmp(body->subtype, "RFC822") == 0) {
	body->subpart = (struct body *)xmalloc(sizeof(struct body));

	if (sawboundary) {
	    memset(body->subpart, 0, sizeof(struct body));
	    message_parse_type(DEFAULT_CONTENT_TYPE, body->subpart);
	}
	else {
	    message_parse_body(msg, body->subpart,
			       DEFAULT_CONTENT_TYPE, boundaries);

	    /* Calculate our size/lines information */
	    body->content_size = body->subpart->header_size +
	      body->subpart->content_size;
	    body->content_lines = body->subpart->header_lines +
	      body->subpart->content_lines;

	    /* Move any enclosing boundary information up to our level */
	    body->boundary_size = body->subpart->boundary_size;
	    body->boundary_lines = body->subpart->boundary_lines;
	}
    }
    else {
	if (!sawboundary) {
	    message_parse_content(msg, body, boundaries);
	}
    }

    /* Free up boundary storage if necessary */
    strarray_fini(&newboundaries);

    return 0;
}

/*
 * Parse the headers of a body-part
 */
static int message_parse_headers(struct msg *msg, struct body *body,
				 const char *defaultContentType,
				 strarray_t *boundaries)
{
    struct buf headers = BUF_INITIALIZER;
    char *next;
    int len;
    int sawboundary = 0;
    int maxlines = config_getint(IMAPOPT_MAXHEADERLINES);
    int have_max = 0;
    const char *value;

    body->header_offset = msg->offset;

    buf_putc(&headers, '\n');	/* Leading newline to prime the pump */

    /* Slurp up all of the headers into 'headers' */
    while ((next = message_getline(&headers, msg)) &&
	   (next[-1] != '\n' ||
	    (*next != '\r' || next[1] != '\n'))) {

	len = strlen(next);

	if (next[-1] == '\n' && *next == '-' &&
	    message_pendingboundary(next, len, boundaries)) {
	    body->boundary_size = len;
	    body->boundary_lines++;
	    if (next - 1 > headers.s) {
		body->boundary_size += 2;
		body->boundary_lines++;
		next[-2] = '\0';
	    }
	    else {
		*next = '\0';
	    }
	    sawboundary = 1;
	    break;
	}
    }

    body->content_offset = msg->offset;
    body->header_size = strlen(headers.s+1);

    /* Scan over the slurped-up headers for interesting header information */
    body->header_lines = -1;	/* Correct for leading newline */
    for (next = headers.s; *next; next++) {
	if (*next == '\n') {
	    body->header_lines++;

	    /* if we're skipping, skip now */
	    if (have_max) continue;

	    /* check if we've hit a limit and flag it */
	    if (maxlines && body->header_lines > maxlines) {
		syslog(LOG_ERR, "ERROR: message has more than %d header lines, not caching any more",
		       maxlines);
		have_max = 1;
		continue;
	    }

	    if (/* space preallocated, i.e. must be top-level body */
		body->cacheheaders.s &&
		/* this is not a continuation line */
		(next[1] != ' ') && (next[1] != '\t') &&
		/* this header is supposed to be cached */
		mailbox_cached_header_inline(next+1) != BIT32_MAX) {
		    /* append to the headers cache */
		    message_parse_header(next+1, &body->cacheheaders);
	    }

	    switch (message_header_lookup(next+1, &value)) {
	    case RFC822_BCC:
		message_parse_address(value, &body->bcc);
		break;
	    case RFC822_CC:
		message_parse_address(value, &body->cc);
		break;
	    case RFC822_CONTENT_DESCRIPTION:
		message_parse_string(value, &body->description);
		break;
	    case RFC822_CONTENT_DISPOSITION:
		message_parse_disposition(value, body);
		break;
	    case RFC822_CONTENT_ID:
		message_parse_string(value, &body->id);
		break;
	    case RFC822_CONTENT_LANGUAGE:
		message_parse_language(value, &body->language);
		break;
	    case RFC822_CONTENT_LOCATION:
		message_parse_string(value, &body->location);
		break;
	    case RFC822_CONTENT_MD5:
		message_parse_string(value, &body->md5);
		break;
	    case RFC822_CONTENT_TRANSFER_ENCODING:
		message_parse_encoding(value, &body->encoding);

		/* If we're encoding binary, replace "binary"
		   with "base64" in CTE header body */
		if (msg->encode &&
		    !strcmp(body->encoding, "BINARY")) {
		    char *p = (char*)
			stristr(msg->base + body->header_offset +
				(next - headers.s) + 27,
				"binary");
		    memcpy(p, "base64", 6);
		}
		break;
	    case RFC822_CONTENT_TYPE:
		message_parse_type(value, body);
		break;
	    case RFC822_DATE:
		message_parse_string(value, &body->date);
		break;
	    case RFC822_FROM:
		message_parse_address(value, &body->from);
		break;
	    case RFC822_IN_REPLY_TO:
		message_parse_string(value, &body->in_reply_to);
		break;
	    case RFC822_MESSAGE_ID:
		message_parse_string(value, &body->message_id);
		break;
	    case RFC822_REPLY_TO:
		message_parse_address(value, &body->reply_to);
		break;
	    case RFC822_RECEIVED:
		message_parse_received_date(value, &body->received_date);
		break;
	    case RFC822_REFERENCES:
		message_parse_string(value, &body->references);
		break;
	    case RFC822_SUBJECT:
		message_parse_string(value, &body->subject);
		break;
	    case RFC822_SENDER:
		message_parse_address(value, &body->sender);
		break;
	    case RFC822_TO:
		message_parse_address(value, &body->to);
		break;
	    case RFC822_X_DELIVEREDINTERNALDATE:
		/* Explicit x-deliveredinternaldate overrides received: headers */
		if (body->received_date) {
		    free(body->received_date);
		    body->received_date = 0;
		}
		message_parse_string(value, &body->received_date);
		break;
	    case RFC822_X_ME_MESSAGE_ID:
		message_parse_string(value, &body->x_me_message_id);
		break;
	    default:
		break;
	    } /* switch() */
	} /* if (*next == '\n') */
    }

    /* If didn't find Content-Type: header, use the passed-in default type */
    if (!body->type) {
	message_parse_type(defaultContentType, body);
    }
    buf_free(&headers);
    return sawboundary;
}

/*
 * Parse a list of RFC-822 addresses from a header, appending them
 * to the address list pointed to by 'addrp'.
 */
static void message_parse_address(const char *hdr, struct address **addrp)
{
    char *hdrend, hdrendchar = '\0';

    /* Find end of header */
    hdrend = (char *)hdr;
    do {
	hdrend = strchr(hdrend+1, '\n');
    } while (hdrend && (hdrend[1] == ' ' || hdrend[1] == '\t'));

    /* Put a NUL character at the end of header */
    /* gnb:TODO this is evil and should be stopped */
    if (hdrend) {
	if (hdrend > hdr && hdrend[-1] == '\r') hdrend--;
	hdrendchar = *hdrend;
	*hdrend = '\0';
    }

    parseaddr_list(hdr, addrp);

    /* Put character at end of header back */
    if (hdrend) *hdrend = hdrendchar;
}

/*
 * Parse a Content-Transfer-Encoding from a header.
 */
static void message_parse_encoding(const char *hdr, char **hdrp)
{
    int len;
    const char *p;

    /* Ignore if we already saw one of these headers */
    if (*hdrp) return;

    /* Skip leading whitespace, ignore header if blank */
    message_parse_rfc822space(&hdr);
    if (!hdr) return;

    /* Find end of encoding token */
    for (p = hdr; *p && !Uisspace(*p) && *p != '('; p++) {
	if (*p < ' ' || strchr(TSPECIALS, *p)) return;
    }
    len = p - hdr;

    /* Skip trailing whitespace, ignore header if trailing garbage */
    message_parse_rfc822space(&p);
    if (p) return;

    /* Save encoding token */
    *hdrp = message_ucase(xstrndup(hdr, len));
}

/* 
 * parse a charset and encoding out of a body structure
 */
static void message_parse_charset(const struct body *body,
				  int *e_ptr, int *c_ptr)
{
    int encoding = ENCODING_NONE;
    int charset = 0;
    struct param *param;

    if (body->encoding) {
	switch (body->encoding[0]) {
	case '7':
	case '8':
	    if (!strcmp(body->encoding+1, "BIT")) 
		encoding = ENCODING_NONE;
	    else 
		encoding = ENCODING_UNKNOWN;
	    break;

	case 'B':
	    if (!strcmp(body->encoding, "BASE64")) 
		encoding = ENCODING_BASE64;
	    else if (!strcmp(body->encoding, "BINARY"))
		encoding = ENCODING_NONE;
	    else 
		encoding = ENCODING_UNKNOWN;
	    break;

	case 'Q':
	    if (!strcmp(body->encoding, "QUOTED-PRINTABLE"))
		encoding = ENCODING_QP;
	    else 
		encoding = ENCODING_UNKNOWN;
	    break;

	default:
	    encoding = ENCODING_UNKNOWN;
	}
    }

    if (!body->type || !strcmp(body->type, "TEXT")) {
	for (param = body->params; param; param = param->next) {
	    if (!strcasecmp(param->attribute, "charset")) {
		if (param->value && *param->value)
		    charset = charset_lookupname(param->value);
		break;
	    }
	}
    }
    else if (!strcmp(body->type, "MESSAGE")) {
	if (!strcmp(body->subtype, "RFC822"))
	    charset = -1;
	encoding = ENCODING_NONE;
    }
    else
	charset = -1;

    if (e_ptr) *e_ptr = encoding;
    if (c_ptr) *c_ptr = charset;
}

/*
 * Parse an uninterpreted header
 */
static void message_parse_string(const char *hdr, char **hdrp)
{
    const char *hdrend;
    char *he;

    /* Ignore if we already saw one of these headers */
    if (*hdrp) return;

    /* Skip initial whitespace */
    while (*hdr == ' ' || *hdr == '\t') hdr++;

    /* Find end of header */
    hdrend = hdr;
    do {
	hdrend = strchr(hdrend+1, '\n');
    } while (hdrend && (hdrend[1] == ' ' || hdrend[1] == '\t'));
    if (hdrend) {
	if (hdrend > hdr && hdrend[-1] == '\r') hdrend--;
    }
    else {
	hdrend = hdr + strlen(hdr);
    }

    /* Save header value */
    *hdrp = xstrndup(hdr, (hdrend - hdr));

    /* Un-fold header (overlapping buffers, use memmove) */
    he = *hdrp;
    while ((he = strchr(he, '\n'))!=NULL) {
	if (he > *hdrp && he[-1] == '\r') {
	    he--;
	    memmove(he, he+2, strlen(he+2)+1);
	}
	else {
	    memmove(he, he+1, strlen(he+1)+1);
	}
    }
}

/*
 * Cache a header
 */
static void
message_parse_header(const char *hdr, struct buf *buf)
{
    int len;
    const char *hdrend;

    /* Find end of header */
    hdrend = hdr;
    do {
	hdrend = strchr(hdrend+1, '\n');
    } while (hdrend && (hdrend[1] == ' ' || hdrend[1] == '\t'));
    if (hdrend) {
	if (hdrend > hdr && hdrend[-1] == '\r') hdrend--;
    }
    else {
	hdrend = hdr + strlen(hdr);
    }

    /* Save header value */
    len = hdrend - hdr;
    buf_appendmap(buf, hdr, len);
    buf_putc(buf, '\r');
    buf_putc(buf, '\n');
}

/*
 * Parse a Content-Type from a header.
 */
static void message_parse_type(const char *hdr, struct body *body)
{
    const char *type;
    int typelen;
    const char *subtype;
    int subtypelen;

    /* Ignore if we already saw one of these headers */
    if (body->type) return;

    /* Skip leading whitespace, ignore header if blank */
    message_parse_rfc822space(&hdr);
    if (!hdr) return;

    /* Find end of type token */
    type = hdr;
    for (; *hdr && !Uisspace(*hdr) && *hdr != '/' && *hdr != '('; hdr++) {
	if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) return;
    }
    typelen = hdr - type;

    /* Skip whitespace after type */
    message_parse_rfc822space(&hdr);
    if (!hdr) return;

    /* Ignore header if no '/' character */
    if (*hdr++ != '/') return;

    /* Skip whitespace before subtype, ignore header if no subtype */
    message_parse_rfc822space(&hdr);
    if (!hdr) return;

    /* Find end of subtype token */
    subtype = hdr;
    for (; *hdr && !Uisspace(*hdr) && *hdr != ';' && *hdr != '('; hdr++) {
	if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) return;
    }
    subtypelen = hdr - subtype;

    /* Skip whitespace after subtype */
    message_parse_rfc822space(&hdr);

    /* Ignore header if not at end of header or parameter delimiter */
    if (hdr && *hdr != ';') return;

    /* Save content type & subtype */
    body->type = message_ucase(xstrndup(type, typelen));
    body->subtype = message_ucase(xstrndup(subtype, subtypelen));

    /* Parse parameter list */
    if (hdr) {
	message_parse_params(hdr+1, &body->params);
	message_fold_params(&body->params);
    }
}

/*
 * Parse a Content-Disposition from a header.
 */
static void message_parse_disposition(const char *hdr, struct body *body)
{
    const char *disposition;
    int dispositionlen;

    /* Ignore if we already saw one of these headers */
    if (body->disposition) return;

    /* Skip leading whitespace, ignore header if blank */
    message_parse_rfc822space(&hdr);
    if (!hdr) return;

    /* Find end of disposition token */
    disposition = hdr;
    for (; *hdr && !Uisspace(*hdr) && *hdr != ';' && *hdr != '('; hdr++) {
	if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) return;
    }
    dispositionlen = hdr - disposition;

    /* Skip whitespace after type */
    message_parse_rfc822space(&hdr);

    /* Ignore header if not at end of header or parameter delimiter */
    if (hdr && *hdr != ';') return;

    /* Save content disposition */
    body->disposition = message_ucase(xstrndup(disposition, dispositionlen));

    /* Parse parameter list */
    if (hdr) {
	message_parse_params(hdr+1, &body->disposition_params);
	message_fold_params(&body->disposition_params);
    }
}

/*
 * Parse a parameter list from a header.
 *
 * 'hdr' points into the message, and is not expected to
 * be nul-terminated.  Handles continuation headers.
 *
 * Malformed parameters are handled by skipping to the
 * next ';' or end of line, which should mark the next
 * parameter.
 */
static void message_parse_params(const char *hdr, struct param **paramp)
{
    struct param *param;
    const char *attribute;
    int attributelen;
    const char *value;
    int valuelen;
    char *p;

    for (;;) {
	/* Skip over leading whitespace */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Find end of attribute */
	attribute = hdr;
	for (; *hdr && !Uisspace(*hdr) && *hdr != '=' && *hdr != '('; hdr++) {
	    if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) goto skip;
	}
	attributelen = hdr - attribute;

	/* Skip whitespace after attribute */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Ignore param if no '=' character */
	if (*hdr++ != '=') goto skip;

	/* Skip whitespace before value */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Find end of value */
	value = hdr;
	if (*hdr == '\"') {
	    hdr++;
	    while (*hdr && *hdr != '\"') {
		if (*hdr == '\\') {
		    hdr++;
		    if (!*hdr) return;
		}
		if (*hdr == '\r') {
		    /* check for continuation headers */
		    if (hdr[1] == '\n' && (hdr[2] == ' ' || hdr[2] == '\t')) hdr += 2;
		    else return;    /* end of header field */
		}
		hdr++;
	    }
	    if (!*hdr++) return;
	}
	else {
	    for (; *hdr && !Uisspace(*hdr) && *hdr != ';' && *hdr != '('; hdr++) {
		if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) goto skip;
	    }
	}
	valuelen = hdr - value;

	/* Skip whitespace after value */
	message_parse_rfc822space(&hdr);

	/* Ignore parameter if not at end of header or parameter delimiter */
	if (hdr && *hdr++ != ';') {
skip:
	    hdr += strcspn(hdr, ";\r\n");
	    if (*hdr == ';') hdr++;
	    continue;
	}
		  
	/* Save attribute/value pair */
	*paramp = param = (struct param *)xzmalloc(sizeof(struct param));
	param->attribute = message_ucase(xstrndup(attribute, attributelen));
	param->value = xmalloc(valuelen + 1);
	if (*value == '\"') {
	    p = param->value;
	    value++;
	    while (*value != '\"') {
		if (*value == '\\') value++;
		else if (*value == '\r') value += 2;
		*p++ = *value++;
	    }
	    *p = '\0';
	}
	else {
	    strlcpy(param->value, value, valuelen + 1);
	}

	/* Get ready to parse the next parameter */
	paramp = &param->next;
    }
}

/*
 * Decode RFC-2231 parameter continuations
 *
 * Algorithm: Run down the list of parameters looking for
 * an attribute of the form "foo*0" or "foo*0*".  When we find 
 * such an attribute, we look for "foo*1"/"foo*1*", "foo*2"/"foo*2*"
 * etc, appending each value to that of "foo*0" and then removing the
 * parameter we just appended from the list.  When appending values,
 * if either parameter has extended syntax, we have to convert the other
 * value from simple to extended syntax.  At the end, we change the name
 * of "foo*0"/"foo*0*" to either "foo" or "foo*", depending on whether
 * the value has extended syntax or not.
 */
static void message_fold_params(struct param **params)
{
    struct param *thisparam;	/* The "foo*1" param we're folding */
    struct param **continuation; /* Pointer to the "foo*2" param */
    struct param *tmpparam;	/* Placeholder for removing "foo*2" */
    char *asterisk;
    int section;
    int is_extended;
    char sectionbuf[5];
    int attributelen, sectionbuflen;
    char *from, *to;

    for (thisparam = *params; thisparam; thisparam = thisparam->next) {
	asterisk = strchr(thisparam->attribute, '*');
	if (asterisk && asterisk[1] == '0' &&
	    (!asterisk[2] || (asterisk[2] == '*' && !asterisk[3]))) {
	    /* An initial section.  Find and collect the rest */
	    is_extended = (asterisk[2] == '*');
	    *asterisk = '\0';
	    attributelen = asterisk - thisparam->attribute;
	    section = 1;
	    for (;;) {
		if (section == 100) break;
		sectionbuf[0] = '*';
		if (section > 9) {
		    sectionbuf[1] = section/10 + '0';
		    sectionbuf[2] = section%10 + '0';
		    sectionbuf[3] = '\0';
		    sectionbuflen = 3;
		}
		else {
		    sectionbuf[1] = section + '0';
		    sectionbuf[2] = '\0';
		    sectionbuflen = 2;
		}

		/* Find the next continuation */
		for (continuation = params; *continuation;
		     continuation = &((*continuation)->next)) {
		    if (!strncmp((*continuation)->attribute, thisparam->attribute,
				 attributelen) &&
			!strncmp((*continuation)->attribute + attributelen,
				 sectionbuf, sectionbuflen) &&
			((*continuation)->attribute[attributelen+sectionbuflen] == '\0' ||
			 ((*continuation)->attribute[attributelen+sectionbuflen] == '*' && (*continuation)->attribute[attributelen+sectionbuflen+1] == '\0'))) {
			break;
		    }
		}

		/* No more continuations to find */
		if (!*continuation) break;
		
		if ((*continuation)->attribute[attributelen+sectionbuflen] == '\0') {
		    /* Continuation is simple */
		    if (is_extended) {
			/* Have to re-encode continuation value */
			thisparam->value =
			    xrealloc(thisparam->value,
				     strlen(thisparam->value) +
				     3*strlen((*continuation)->value) + 1);
			from = (*continuation)->value;
			to = thisparam->value + strlen(thisparam->value);
			while (*from) {
			    if (*from <= ' ' || *from >= 0x7f ||
				*from == '*' || *from == '\'' ||
				*from == '%' || strchr(TSPECIALS, *from)) {
				*to++ = '%';
				to += bin_to_hex(from, 1, to, BH_UPPER);
			    } else {
				*to++ = *from;
			    }
			    from++;
			}
			*to++ = '\0';
		    }
		    else {
			thisparam->value =
			    xrealloc(thisparam->value,
				     strlen(thisparam->value) +
				     strlen((*continuation)->value) + 1);
			from = (*continuation)->value;
			to = thisparam->value + strlen(thisparam->value);
			while ((*to++ = *from++)!= 0)
			    { }
		    }
		}
		else {
		    /* Continuation is extended */
		    if (is_extended) {
			thisparam->value =
			    xrealloc(thisparam->value,
				     strlen(thisparam->value) +
				     strlen((*continuation)->value) + 1);
			from = (*continuation)->value;
			to = thisparam->value + strlen(thisparam->value);
			while ((*to++ = *from++) != 0)
			    { }
		    }
		    else {
			/* Have to re-encode thisparam value */
			char *tmpvalue =
			    xmalloc(2 + 3*strlen(thisparam->value) +
				    strlen((*continuation)->value) + 1);

			from = thisparam->value;
			to = tmpvalue;
			*to++ = '\''; /* Unspecified charset */
			*to++ = '\''; /* Unspecified language */
			while (*from) {
			    if (*from <= ' ' || *from >= 0x7f ||
				*from == '*' || *from == '\'' ||
				*from == '%' || strchr(TSPECIALS, *from)) {
				*to++ = '%';
				to += bin_to_hex(from, 1, to, BH_UPPER);
			    } else {
				*to++ = *from;
			    }
			    from++;
			}
			from = (*continuation)->value;

			while ((*to++ = *from++)!=0)
			    { }

			free(thisparam->value);
			thisparam->value = tmpvalue;
			is_extended = 1;
		    }
		}

		/* Remove unneeded continuation */
		free((*continuation)->attribute);
		free((*continuation)->value);
		tmpparam = *continuation;
		*continuation = (*continuation)->next;
		free(tmpparam);
		section++;
	    }

	    /* Fix up attribute name */
	    if (is_extended) {
		asterisk[0] = '*';
		asterisk[1] = '\0';
	    } else {
		asterisk[0] = '\0';
	    }
	}
    }
}	 


/*
 * Parse a language list from a header
 */
static void message_parse_language(const char *hdr, struct param **paramp)
{
    struct param *param;
    const char *value;
    int valuelen;

    for (;;) {
	/* Skip over leading whitespace */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Skip whitespace before value */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Find end of value */
	value = hdr;
	for (; *hdr && !Uisspace(*hdr) && *hdr != ',' && *hdr != '('; hdr++) {
	    if (*hdr != '-' && !Uisalpha((*hdr))) return;
	}
	valuelen = hdr - value;

	/* Skip whitespace after value */
	message_parse_rfc822space(&hdr);

	/* Ignore parameter if not at end of header or language delimiter */
	if (hdr && *hdr++ != ',') return;
		  
	/* Save value pair */
	*paramp = param = (struct param *)xzmalloc(sizeof(struct param));
	param->value = message_ucase(xstrndup(value, valuelen));

	/* Get ready to parse the next parameter */
	paramp = &param->next;
    }
}

/*
 * Skip over RFC-822 whitespace and comments
 */
static void message_parse_rfc822space(const char **s)
{
    const char *p = *s;
    int commentlevel = 0;

    if (!p) return;
    while (*p && (Uisspace(*p) || *p == '(')) {
	if (*p == '\n') {
	    p++;
	    if (*p != ' ' && *p != '\t') {
		*s = 0;	    /* end of header field, no continuation */
		return;
	    }
	}
	else if (*p == '(') {
	    p++;
	    commentlevel++;
	    while (commentlevel) {
		switch (*p) {
		case '\n':
		    p++;
		    if (*p == ' ' || *p == '\t') break;
		    /* FALL THROUGH */
		case '\0':
		    *s = 0;
		    return;
		    
		case '\\':
		    p++;
		    break;

		case '(':
		    commentlevel++;
		    break;

		case ')':
		    commentlevel--;
		    break;
		}
		p++;
	    }
	}
	else p++;
    }
    if (*p == 0) {
	*s = 0;	    /* embedded NUL */
    }
    else {
	*s = p;
    }
}

/*
 * Parse the content of a MIME multipart body-part
 */
static void message_parse_multipart(struct msg *msg, struct body *body,
				    strarray_t *boundaries)
{
    struct body preamble, epilogue;
    struct param *boundary;
    const char *defaultContentType = DEFAULT_CONTENT_TYPE;
    int i, depth;
    int limit = config_getint(IMAPOPT_BOUNDARY_LIMIT);

    memset(&preamble, 0, sizeof(struct body));
    memset(&epilogue, 0, sizeof(struct body));
    if (strcmp(body->subtype, "DIGEST") == 0) {
	defaultContentType = "MESSAGE/RFC822";
    }

    /* Find boundary id */
    boundary = body->params;
    while(boundary && strcmp(boundary->attribute, "BOUNDARY") != 0) {
	boundary = boundary->next;
    }
    
    if (!boundary) {
	/* Invalid MIME--treat as zero-part multipart */
	message_parse_content(msg, body, boundaries);
	return;
    }

    /* Add the new boundary id */
    strarray_append(boundaries, boundary->value);
    depth = boundaries->count;

    /* Parse preamble */
    message_parse_content(msg, &preamble, boundaries);

    /* Parse the component body-parts */
    while (boundaries->count == depth &&
	    (limit == 0 ? 1 : boundaries->count < limit)) {
	body->subpart = (struct body *)xrealloc((char *)body->subpart,
				 (body->numparts+1)*sizeof(struct body));
	message_parse_body(msg, &body->subpart[body->numparts++],
			   defaultContentType, boundaries);
	if (msg->offset == msg->len &&
	    body->subpart[body->numparts-1].boundary_size == 0) {
	    /* hit the end of the message, therefore end all pending
	       multiparts */
	    strarray_truncate(boundaries, 0);
	}
    }

    if (boundaries->count == depth-1) {
	/* Parse epilogue */
	message_parse_content(msg, &epilogue, boundaries);
    }
    else if (body->numparts) {
	/*
	 * We hit the boundary of an enclosing multipart while parsing
	 * a component body-part.  Move the enclosing boundary information
	 * up to our level.
	 */
	body->boundary_size = body->subpart[body->numparts-1].boundary_size;
	body->boundary_lines = body->subpart[body->numparts-1].boundary_lines;
	body->subpart[body->numparts-1].boundary_size = 0;
	body->subpart[body->numparts-1].boundary_lines = 0;
    }
    else {
	/*
	 * We hit the boundary of an enclosing multipart while parsing
	 * the preamble.  Move the enclosing boundary information
	 * up to our level.
	 */
	body->boundary_size = preamble.boundary_size;
	body->boundary_lines = preamble.boundary_lines;
	preamble.boundary_size = 0;
	preamble.boundary_lines = 0;
    }

    /*
     * Calculate our size/lines information
     */
    body->content_size = preamble.content_size + preamble.boundary_size;
    body->content_lines = preamble.content_lines + preamble.boundary_lines;
    for (i=0; i< body->numparts; i++) {
	body->content_size += body->subpart[i].header_size +
	  body->subpart[i].content_size +
	  body->subpart[i].boundary_size;
	body->content_lines += body->subpart[i].header_lines +
	  body->subpart[i].content_lines +
	  body->subpart[i].boundary_lines;
    }
    body->content_size += epilogue.content_size;
    body->content_lines += epilogue.content_lines;

    /*
     * Move any enclosing boundary information up to our level.
     */
    body->boundary_size += epilogue.boundary_size;
    body->boundary_lines += epilogue.boundary_lines;

    /* check if we've hit a limit and flag it */
    if (limit && depth == limit) {
	syslog(LOG_ERR, "ERROR: mime boundary limit %i exceeded, not parsing anymore", limit);
    }
}

/*
 * Parse the content of a generic body-part
 */
static void message_parse_content(struct msg *msg, struct body *body,
				  strarray_t *boundaries)
{
    const char *line, *endline;
    unsigned long s_offset = msg->offset;
    int encode;
    int len;

    /* Should we encode a binary part? */
    encode = msg->encode &&
	body->encoding && !strcasecmp(body->encoding, "binary");

    while (msg->offset < msg->len) {
	line = msg->base + msg->offset;
	endline = memchr(line, '\n', msg->len - msg->offset);
	if (endline) {
	    endline++;
	}
	else {
	    endline = msg->base + msg->len;
	}
	len = endline - line;
	msg->offset += len;

	if (line[0] == '-' && line[1] == '-' &&
	    message_pendingboundary(line, len, boundaries)) {
	    body->boundary_size = len;
	    body->boundary_lines++;
	    if (body->content_lines) {
		body->content_lines--;
		body->boundary_lines++;
	    }
	    if (body->content_size) {
		body->content_size -= 2;
		body->boundary_size += 2;
	    }
	    break;
	}

	body->content_size += len;

	/* Count the content lines, unless we're encoding
	   (we always count blank lines) */
	if (endline[-1] == '\n' &&
	    (!encode || line[0] == '\r')) {
	    body->content_lines++;
	}
    }

    if (encode) {
	size_t b64_size;
	int b64_lines, delta;

	/* Determine encoded size */
	charset_encode_mimebody(NULL, body->content_size, NULL,
				&b64_size, NULL);

	delta = b64_size - body->content_size;

	/* Realloc buffer to accomodate encoding overhead */
	msg->base = xrealloc((char*) msg->base, msg->len + delta);

	/* Shift content and remaining data by delta */
	memmove((char*) msg->base + s_offset + delta, msg->base + s_offset,
		msg->len - s_offset);

	/* Encode content into buffer at current position */
	charset_encode_mimebody(msg->base + s_offset + delta,
				body->content_size,
				(char*) msg->base + s_offset,
				NULL, &b64_lines);

	/* Adjust buffer position and length to account for encoding */
	msg->offset += delta;
	msg->len += delta;

	/* Adjust body structure to account for encoding */
	strcpy(body->encoding, "BASE64");
	body->content_size = b64_size;
	body->content_lines += b64_lines;
    }
}

static void message_parse_received_date(const char *hdr, char **hdrp)
{
  char *curp, *hdrbuf = 0;

  /* Ignore if we already saw one of these headers */
  if (*hdrp) return;

  /* Copy header to temp buffer */
  message_parse_string(hdr, &hdrbuf);

  /* From rfc2822, 3.6.7
   *   received = "Received:" name-val-list ";" date-time CRLF
   * So scan backwards for ; and assume everything after is a date.
   * Failed parsing will return 0, and we'll use time() elsewhere
   * instead anyway
   */
  curp = hdrbuf + strlen(hdrbuf) - 1;
  while (curp > hdrbuf && *curp != ';')
    curp--;

  /* Didn't find ; - fill in hdrp so we don't look at next received header */
  if (curp == hdrbuf) {
    *hdrp = hdrbuf;
    return;
  }

  /* Found it, copy out date string part */
  curp++;
  message_parse_string(curp, hdrp);
  free(hdrbuf);
}


/*
 * Read a line from @msg into @buf.  Returns a pointer to the start of
 * the line inside @buf, or NULL at the end of @msg.
 */
static char *message_getline(struct buf *buf, struct msg *msg)
{
    unsigned int oldlen = buf_len(buf);
    int c;

    while (msg->offset < msg->len) {
	c = msg->base[msg->offset++];
	buf_putc(buf, c);
	if (c == '\n')
	    break;
    }
    buf_cstring(buf);

    if (buf_len(buf) == oldlen)
	return 0;
    return buf->s + oldlen;
}


/*
 * Return nonzero if s is an enclosing boundary delimiter.
 * If we hit a terminating boundary, the integer pointed to by
 * 'boundaryct' is modified appropriately.
 */
static int message_pendingboundary(const char *s, int slen,
				   strarray_t *boundaries)
{
    int i, len;
    int rfc2046_strict = config_getswitch(IMAPOPT_RFC2046_STRICT);
    const char *bbase;
    int blen;

    /* skip initial '--' */
    if (slen < 2) return 0;
    if (s[0] != '-' || s[1] != '-') return 0;
    bbase = s + 2;
    blen = slen - 2;

    for (i = 0; i < boundaries->count ; ++i) {
	len = strlen(boundaries->data[i]);
	/* basic sanity check and overflow protection */
	if (blen < len) continue;

	if (!strncmp(bbase, boundaries->data[i], len)) {
	    /* trailing '--', it's the end of this part */
	    if (blen >= len+2 && bbase[len] == '-' && bbase[len+1] == '-')
		strarray_truncate(boundaries, i);
	    else if (!rfc2046_strict && blen > len+1 &&
		     bbase[len] && !Uisspace(bbase[len])) {
		/* Allow substring matches in the boundary.
		 *
		 * If rfc2046_strict is enabled, boundaries containing
		 * other boundaries as substrings will be treated as identical
		 * (per RFC 2046 section 5.1.1).  Note that this will
		 * break some messages created by Eudora 5.1 (and earlier).
		 */
		continue;
	    }
	    return 1;
	}
    }
    return 0;
}


/*
 * Write the cache information for the message parsed to 'body'
 * to 'outfile'.
 */
int message_write_cache(struct index_record *record, const struct body *body)
{
    static struct buf cacheitem_buffer;
    struct buf ib[NUM_CACHE_FIELDS];
    struct body toplevel;
    char *subject;
    int len;
    int i;

    /* initialise data structures */
    buf_reset(&cacheitem_buffer);
    for (i = 0; i < NUM_CACHE_FIELDS; i++)
	buf_init(&ib[i]);

    toplevel.type = "MESSAGE";
    toplevel.subtype = "RFC822";
    /* we cast away const because we know that we're only using
     * toplevel.subpart as const in message_write_section(). */
    toplevel.subpart = (struct body *)body;

    subject = charset_parse_mimeheader(body->subject);

    /* copy into bufs */
    message_write_envelope(&ib[CACHE_ENVELOPE], body);
    message_write_body(&ib[CACHE_BODYSTRUCTURE], body, 1);
    buf_copy(&ib[CACHE_HEADERS], &body->cacheheaders);
    message_write_body(&ib[CACHE_BODY], body, 0);
    message_write_section(&ib[CACHE_SECTION], &toplevel);
    message_write_searchaddr(&ib[CACHE_FROM], body->from);
    message_write_searchaddr(&ib[CACHE_TO], body->to);
    message_write_searchaddr(&ib[CACHE_CC], body->cc);
    message_write_searchaddr(&ib[CACHE_BCC], body->bcc);
    message_write_nstring(&ib[CACHE_SUBJECT], subject);

    free(subject);

    /* append the records to the buffer */
    for (i = 0; i < NUM_CACHE_FIELDS; i++) {
	record->crec.item[i].len = buf_len(&ib[i]);
	record->crec.item[i].offset = buf_len(&cacheitem_buffer) + sizeof(uint32_t);
	message_write_xdrstring(&cacheitem_buffer, &ib[i]);
	buf_free(&ib[i]);
    }

    len = buf_len(&cacheitem_buffer);

    /* copy the fields into the message */
    record->cache_offset = 0; /* calculate on write! */
    record->cache_version = MAILBOX_CACHE_MINOR_VERSION;
    record->cache_crc = crc32_map(cacheitem_buffer.s, len);
    record->crec.base = &cacheitem_buffer;
    record->crec.offset = 0; /* we're at the start of the buffer */
    record->crec.len = len;

    return 0;
}


/*
 * Write the IMAP envelope for 'body' to 'buf'
 */
static void message_write_envelope(struct buf *buf, const struct body *body)
{
    buf_putc(buf, '(');
    message_write_nstring(buf, body->date);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->subject);
    buf_putc(buf, ' ');
    message_write_address(buf, body->from);
    buf_putc(buf, ' ');
    message_write_address(buf, body->sender ? body->sender : body->from);
    buf_putc(buf, ' ');
    message_write_address(buf, body->reply_to ? body->reply_to : body->from);
    buf_putc(buf, ' ');
    message_write_address(buf, body->to);
    buf_putc(buf, ' ');
    message_write_address(buf, body->cc);
    buf_putc(buf, ' ');
    message_write_address(buf, body->bcc);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->in_reply_to);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->message_id);
    buf_putc(buf, ')');
}

/*
 * Write the BODY (if 'newformat' is zero) or BODYSTRUCTURE
 * (if 'newformat' is nonzero) for 'body' to 'buf'.
 */
HIDDEN void message_write_body(struct buf *buf, const struct body *body,
			       int newformat)
{
    struct param *param;

    if (strcmp(body->type, "MULTIPART") == 0) {
	int i;

	/* 0-part multiparts are illegal--convert to 0-len text parts */
	if (body->numparts == 0) {
	    static struct body zerotextbody;

	    if (!zerotextbody.type) {
		message_parse_type(DEFAULT_CONTENT_TYPE, &zerotextbody);
	    }
	    message_write_body(buf, &zerotextbody, newformat);
	    return;
	}

	/* Multipart types get a body_multipart */
	buf_putc(buf, '(');
	for (i = 0; i < body->numparts; i++) {
	    message_write_body(buf, &body->subpart[i], newformat);
	}
	buf_putc(buf, ' ');
	message_write_nstring(buf, body->subtype);

	if (newformat) {
	    buf_putc(buf, ' ');
	    if ((param = body->params)!=NULL) {
		buf_putc(buf, '(');
		while (param) {
		    message_write_nstring(buf, param->attribute);
		    buf_putc(buf, ' ');
		    message_write_nstring(buf, param->value);
		    if ((param = param->next)!=NULL) {
			buf_putc(buf, ' ');
		    }
		}
		buf_putc(buf, ')');
	    }
	    else message_write_nstring(buf, (char *)0);
	    buf_putc(buf, ' ');
	    if (body->disposition) {
		buf_putc(buf, '(');
		message_write_nstring(buf, body->disposition);
		buf_putc(buf, ' ');
		if ((param = body->disposition_params)!=NULL) {
		    buf_putc(buf, '(');
		    while (param) {
			message_write_nstring(buf, param->attribute);
			buf_putc(buf, ' ');
			message_write_nstring(buf, param->value);
			if ((param = param->next)!=NULL) {
			    buf_putc(buf, ' ');
			}
		    }
		    buf_putc(buf, ')');
		}
		else message_write_nstring(buf, (char *)0);
		buf_putc(buf, ')');
	    }
	    else {
		message_write_nstring(buf, (char *)0);
	    }
	    buf_putc(buf, ' ');
	    if ((param = body->language)!=NULL) {
		buf_putc(buf, '(');
		while (param) {
		    message_write_nstring(buf, param->value);
		    if ((param = param->next)!=NULL) {
			buf_putc(buf, ' ');
		    }
		}
		buf_putc(buf, ')');
	    }
	    else message_write_nstring(buf, (char *)0);
	    buf_putc(buf, ' ');
	    message_write_nstring(buf, body->location);
	}

	buf_putc(buf, ')');
	return;
    }

    buf_putc(buf, '(');
    message_write_nstring(buf, body->type);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->subtype);
    buf_putc(buf, ' ');

    if ((param = body->params)!=NULL) {
	buf_putc(buf, '(');
	while (param) {
	    message_write_nstring(buf, param->attribute);
	    buf_putc(buf, ' ');
	    message_write_nstring(buf, param->value);
	    if ((param = param->next)!=NULL) {
		buf_putc(buf, ' ');
	    }
	}
	buf_putc(buf, ')');
    }
    else message_write_nstring(buf, (char *)0);
    buf_putc(buf, ' ');

    message_write_nstring(buf, body->id);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->description);
    buf_putc(buf, ' ');
    message_write_nstring(buf, body->encoding ? body->encoding : "7BIT");
    buf_putc(buf, ' ');
    buf_printf(buf, "%lu", body->content_size);

    if (strcmp(body->type, "TEXT") == 0) {
	/* Text types get a line count */
	buf_putc(buf, ' ');
	buf_printf(buf, "%lu", body->content_lines);
    }
    else if (strcmp(body->type, "MESSAGE") == 0
	     && strcmp(body->subtype, "RFC822") == 0) {
	/* Message/rfc822 gets a body_msg */
	buf_putc(buf, ' ');
	message_write_envelope(buf, body->subpart);
	buf_putc(buf, ' ');
	message_write_body(buf, body->subpart, newformat);
	buf_putc(buf, ' ');
	buf_printf(buf, "%lu", body->content_lines);
    }

    if (newformat) {
	/* Add additional fields for BODYSTRUCTURE */
	buf_putc(buf, ' ');
	message_write_nstring(buf, body->md5);
	buf_putc(buf, ' ');
	if (body->disposition) {
	    buf_putc(buf, '(');
	    message_write_nstring(buf, body->disposition);
	    buf_putc(buf, ' ');
	    if ((param = body->disposition_params)!=NULL) {
		buf_putc(buf, '(');
		while (param) {
		    message_write_nstring(buf, param->attribute);
		    buf_putc(buf, ' ');
		    message_write_nstring(buf, param->value);
		    if ((param = param->next)!=NULL) {
			buf_putc(buf, ' ');
		    }
		}
		buf_putc(buf, ')');
	    }
	    else message_write_nstring(buf, (char *)0);
	    buf_putc(buf, ')');
	}
	else {
	    message_write_nstring(buf, (char *)0);
	}
	buf_putc(buf, ' ');
	if ((param = body->language)!=NULL) {
	    buf_putc(buf, '(');
	    while (param) {
		message_write_nstring(buf, param->value);
		if ((param = param->next)!=NULL) {
		    buf_putc(buf, ' ');
		}
	    }
	    buf_putc(buf, ')');
	}
	else message_write_nstring(buf, (char *)0);
	buf_putc(buf, ' ');
	message_write_nstring(buf, body->location);

	if (newformat > 1 && !body->numparts) {
	    /* even newer extension fields for annotation callout */
	    buf_printf(buf, " (OFFSET %lu HEADERSIZE %lu)",
		       body->content_offset,
		       body->header_size);
	}
    }

    buf_putc(buf, ')');
}

/*
 * Write the address list 'addrlist' to 'buf'
 */
static void message_write_address(struct buf *buf,
				  const struct address *addrlist)
{
    /* If no addresses, write out NIL */
    if (!addrlist) {
	message_write_nstring(buf, (char *)0);
	return;
    }

    buf_putc(buf, '(');

    while (addrlist) {
	buf_putc(buf, '(');
	message_write_nstring(buf, addrlist->name);
	buf_putc(buf, ' ');
	message_write_nstring(buf, addrlist->route);
	buf_putc(buf, ' ');
	message_write_nstring(buf, addrlist->mailbox);
	buf_putc(buf, ' ');
	message_write_nstring(buf, addrlist->domain);
	buf_putc(buf, ')');
	addrlist = addrlist->next;
    }

    buf_putc(buf, ')');
}

/*
 * Write the nil-or-string 's' to 'buf'
 */
EXPORTED void message_write_nstring(struct buf *buf, const char *s)
{
    message_write_nstring_map(buf, s, (s ? strlen(s) : 0));
}

EXPORTED void message_write_nstring_map(struct buf *buf,
			       const char *s,
			       unsigned int len)
{
    const char *p;
    int is_literal = 0;

    /* Write null pointer as NIL */
    if (!s) {
	buf_appendcstr(buf, "NIL");
	return;
    }

    if (len >= 1024)
    {
	is_literal = 1;
    }
    else
    {
	/* Look for any non-QCHAR characters */
	for (p = s; (unsigned)(p-s) < len ; p++) {
	    if (!*p || *p & 0x80 || *p == '\r' || *p == '\n'
		|| *p == '\"' || *p == '%' || *p == '\\') {
		is_literal = 1;
		break;
	    }
	}
    }

    if (is_literal) {
	/* Write out as literal */
	buf_printf(buf, "{%u}\r\n", len);
	buf_appendmap(buf, s, len);
    }
    else {
	/* Write out as quoted string */
	buf_putc(buf, '"');
	buf_appendmap(buf, s, len);
	buf_putc(buf, '"');
    }
}

/*
 * Append the string @s to the buffer @buf in a binary
 * format almost exactly
 */
EXPORTED void message_write_xdrstring(struct buf *buf, const struct buf *s)
{
    unsigned padlen;

    /* 32b string length in network order */
    buf_appendbit32(buf, buf_len(s));
    /* bytes of string */
    buf_appendmap(buf, s->s, s->len);
    /* 0 to 3 bytes padding */
    padlen = (4 - (s->len & 3)) & 3;
    buf_appendmap(buf, "\0\0\0", padlen);
}

/*
 * Write the text 's' to 'buf', converting to lower case as we go.
 */
static void message_write_text_lcase(struct buf *buf, const char *s)
{
    const char *p;

    for (p = s; *p; p++) buf_putc(buf, TOLOWER(*p));
}

/*
 * Write out the FETCH BODY[section] location/size information to 'buf'.
 */
static void message_write_section(struct buf *buf, const struct body *body)
{
    int part;

    if (strcmp(body->type, "MESSAGE") == 0
	&& strcmp(body->subtype, "RFC822") == 0) {
	if (body->subpart->numparts) {
	    /*
	     * Part 0 of a message/rfc822 is the message header/text.
	     * Nested parts of a message/rfc822 containing a multipart
	     * are the sub-parts of the multipart.
	     */
	    buf_appendbit32(buf, body->subpart->numparts+1);
	    buf_appendbit32(buf, body->subpart->header_offset);
	    buf_appendbit32(buf, body->subpart->header_size);
	    buf_appendbit32(buf, body->subpart->content_offset);
	    buf_appendbit32(buf, body->subpart->content_size);
	    buf_appendbit32(buf, (-1<<16)|ENCODING_NONE);
	    for (part = 0; part < body->subpart->numparts; part++) {
		buf_appendbit32(buf, body->subpart->subpart[part].header_offset);
		buf_appendbit32(buf, body->subpart->subpart[part].header_size);
		buf_appendbit32(buf, body->subpart->subpart[part].content_offset);
		if (body->subpart->subpart[part].numparts == 0 &&
		    strcmp(body->subpart->subpart[part].type, "MULTIPART") == 0) {
		    /* Treat 0-part multipart as 0-length text */
		    buf_appendbit32(buf, 0);
		}
		else {
		    buf_appendbit32(buf, body->subpart->subpart[part].content_size);
		}
		message_write_charset(buf, &body->subpart->subpart[part]);
	    }
	    for (part = 0; part < body->subpart->numparts; part++) {
		message_write_section(buf, &body->subpart->subpart[part]);
	    }
	}
	else {
	    /*
	     * Part 0 of a message/rfc822 is the message header/text.
	     * Part 1 of a message/rfc822 containing a non-multipart
	     * is the message body.
	     */
	    buf_appendbit32(buf, 2);
	    buf_appendbit32(buf, body->subpart->header_offset);
	    buf_appendbit32(buf, body->subpart->header_size);
	    buf_appendbit32(buf, body->subpart->content_offset);
	    buf_appendbit32(buf, body->subpart->content_size);
	    buf_appendbit32(buf, (-1<<16)|ENCODING_NONE);
	    buf_appendbit32(buf, body->subpart->header_offset);
	    buf_appendbit32(buf, body->subpart->header_size);
	    buf_appendbit32(buf, body->subpart->content_offset);
	    if (strcmp(body->subpart->type, "MULTIPART") == 0) {
		/* Treat 0-part multipart as 0-length text */
		buf_appendbit32(buf, 0);
		buf_appendbit32(buf, (-1<<16)|ENCODING_NONE);
	    }
	    else {
		buf_appendbit32(buf, body->subpart->content_size);
		message_write_charset(buf, body->subpart);
	    }
	    message_write_section(buf, body->subpart);
	}
    }
    else if (body->numparts) {
	/*
	 * Cannot fetch part 0 of a multipart.
	 * Nested parts of a multipart are the sub-parts.
	 */
	buf_appendbit32(buf, body->numparts+1);	
	buf_appendbit32(buf, 0);
	buf_appendbit32(buf, -1);
	buf_appendbit32(buf, 0);
	buf_appendbit32(buf, -1);
	buf_appendbit32(buf, (-1<<16)|ENCODING_NONE);
	for (part = 0; part < body->numparts; part++) {
	    buf_appendbit32(buf, body->subpart[part].header_offset);
	    buf_appendbit32(buf, body->subpart[part].header_size);
	    buf_appendbit32(buf, body->subpart[part].content_offset);
	    if (body->subpart[part].numparts == 0 &&
		strcmp(body->subpart[part].type, "MULTIPART") == 0) {
		/* Treat 0-part multipart as 0-length text */
		buf_appendbit32(buf, 0);
		buf_appendbit32(buf, (-1<<16)|ENCODING_NONE);
	    }
	    else {
		buf_appendbit32(buf, body->subpart[part].content_size);
		message_write_charset(buf, &body->subpart[part]);
	    }
	}
	for (part = 0; part < body->numparts; part++) {
	    message_write_section(buf, &body->subpart[part]);
	}
    }
    else {
	/*
	 * Leaf section--no part 0 or nested parts
	 */
	buf_appendbit32(buf, 0);
    }
}

/*
 * Write the 32-bit charset/encoding value for section 'body' to 'buf'
 */
static void message_write_charset(struct buf *buf, const struct body *body)
{
    int encoding, charset;

    message_parse_charset(body, &encoding, &charset);

    buf_appendbit32(buf, (charset<<16)|encoding);
}

/*
 * Unparse the address list 'addrlist' to 'buf'
 */
static void message_write_searchaddr(struct buf *buf,
				     const struct address *addrlist)
{
    int prevaddr = 0;
    char* tmp;

    while (addrlist) {

	/* Handle RFC-822 group addresses */
	if (!addrlist->domain) {
	    if (addrlist->mailbox) {
		if (prevaddr) buf_putc(buf, ',');
		
		tmp = charset_parse_mimeheader(addrlist->mailbox);
		buf_appendcstr(buf, tmp);
		free(tmp);
		tmp = NULL;
		buf_putc(buf, ':');
	
		/* Suppress a trailing comma */
		prevaddr = 0;
	    }
	    else {
		buf_putc(buf, ';');
		prevaddr = 1;
	    }
	}
	else {
	    if (prevaddr) buf_putc(buf, ',');

	    if (addrlist->name) {
		tmp = charset_parse_mimeheader(addrlist->name);
		buf_appendcstr(buf, tmp);
		free(tmp); tmp = NULL;
		buf_putc(buf, ' ');
	    }

	    buf_putc(buf, '<');
	    if (addrlist->route) {
		message_write_text_lcase(buf, addrlist->route);
		buf_putc(buf, ':');
	    }

	    message_write_text_lcase(buf, addrlist->mailbox);
	    buf_putc(buf, '@');

	    message_write_text_lcase(buf, addrlist->domain);
	    buf_putc(buf, '>');
	    prevaddr = 1;
	}

	addrlist = addrlist->next;
    }
}

/*
 * Free the parsed body-part 'body'
 */
EXPORTED void message_free_body(struct body *body)
{
    struct param *param, *nextparam;
    int part;

    if (!body) return;

    if (body->type) {
	free(body->type);
	free(body->subtype);
	for (param = body->params; param; param = nextparam) {
	    nextparam = param->next;
	    free(param->attribute);
	    free(param->value);
	    free(param);
	}
    }
    if (body->id) free(body->id);
    if (body->description) free(body->description);
    if (body->encoding) free(body->encoding);
    if (body->md5) free(body->md5);
    if (body->disposition) {
	free(body->disposition);
	for (param = body->disposition_params; param; param = nextparam) {
	    nextparam = param->next;
	    free(param->attribute);
	    free(param->value);
	    free(param);
	}
    }
    for (param = body->language; param; param = nextparam) {
	nextparam = param->next;
	free(param->value);
	free(param);
    }
    if (body->location) free(body->location);
    if (body->date) free(body->date);
    if (body->subject) free(body->subject);
    if (body->from) parseaddr_free(body->from);
    if (body->sender) parseaddr_free(body->sender);
    if (body->reply_to) parseaddr_free(body->reply_to);
    if (body->to) parseaddr_free(body->to);
    if (body->cc) parseaddr_free(body->cc);
    if (body->bcc) parseaddr_free(body->bcc);
    if (body->in_reply_to) free(body->in_reply_to);
    if (body->message_id) free(body->message_id);
    if (body->x_me_message_id) free(body->x_me_message_id);
    if (body->references) free(body->references);
    if (body->received_date) free(body->received_date);

    if (body->subpart) {
	if (body->numparts) {
	    for (part=0; part < body->numparts; part++) {
		message_free_body(&body->subpart[part]);
	    }
	}
	else {
	    message_free_body(body->subpart);
	}
	free(body->subpart);
    }

    buf_free(&body->cacheheaders);

    if (body->decoded_body) free(body->decoded_body);
}

/*
 * Parse a cached envelope into individual tokens
 *
 * When inside a list (ncom > 0), we parse the individual tokens but don't
 * isolate them -- we return the entire list as a single token.
 */
HIDDEN void parse_cached_envelope(char *env, char *tokens[], int tokens_size)
{
    char *c;
    int i = 0, ncom = 0, len;

    /*
     * We have no way of indicating that we parsed less than
     * the requested number of tokens, but we can at least
     * ensure that the array is correctly initialised to NULL.
     */
    memset(tokens, 0, tokens_size*sizeof(char*));

    c = env;
    while (*c != '\0') {
	switch (*c) {
	case ' ':			/* end of token */
	    if (!ncom) *c = '\0';	/* mark end of token */
	    c++;
	    break;
	case 'N':			/* "NIL" */
	case 'n':
	    if (!ncom) {
		if(i>=tokens_size) break;
		tokens[i++] = NULL;	/* empty token */
	    }
	    c += 3;			/* skip "NIL" */
	    break;
	case '"':			/* quoted string */
	    c++;			/* skip open quote */
	    if (!ncom) {
		if(i>=tokens_size) break;
		tokens[i++] = c;	/* start of string */
	    }
	    while (*c && *c != '"') {		/* find close quote */
		if (*c == '\\') c++;	/* skip quoted-specials */
		if (*c) c++;
	    }
	    if (*c) {
		if (!ncom) *c = '\0';	/* end of string */
		c++;			/* skip close quote */
	    }
	    break;
	case '{':			/* literal */
	    c++;			/* skip open brace */
	    len = 0;			/* determine length of literal */
	    while (cyrus_isdigit((int) *c)) {
		len = len*10 + *c - '0';
		c++;
	    }
	    c += 3;			/* skip close brace & CRLF */
	    if (!ncom){
		if(i>=tokens_size) break;
		tokens[i++] = c;	/* start of literal */
	    }
	    c += len;			/* skip literal */
	    break;
	case '(':			/* start of address */
	    c++;			/* skip open paren */
	    if (!ncom) {
		if(i>=tokens_size) break;
		tokens[i++] = c;	/* start of address list */
	    }
	    ncom++;			/* new open - inc counter */
	    break;
	case ')':			/* end of address */
	    c++;			/* skip close paren */
	    if (ncom) {			/* paranoia */
		ncom--;			/* close - dec counter */
		if (!ncom)		/* all open paren are closed */
		    *(c-1) = '\0';	/* end of list - trim close paren */
	    }
	    break;
	default:
	    /* yikes! unparsed junk, just skip it */
	    c++;
	    break;
	}
    }
}

EXPORTED char *parse_nstring(char **str)
{
    char *cp = *str, *val;

    if (*cp == '"') { /* quoted string */
	val = cp+1; /* skip " */
	do {
	    cp = strchr(cp+1, '"');
	    if (!cp) return NULL; /* whole thing is broken */
	} while (*(cp-1) == '\\'); /* skip escaped " */
	*cp++ = '\0';
    }
    else if (*cp == '{') {
	int len = 0;
	/* yeah, it may be a literal too */
	cp++;
	while (cyrus_isdigit((int) *cp)) {
	    len = len*10 + *cp - '0';
	    cp++;
	}
	cp += 3;		/* skip close brace & CRLF */
	val = cp;
	val[len] = '\0';
	cp += len;
    }
    else { /* NIL */
	val = NULL;
	cp += 3;
    }

    *str = cp;
    return val;
}

HIDDEN void message_parse_env_address(char *str, struct address *addr)
{
    if (*str == '(') str++; /* skip ( */
    addr->name = parse_nstring(&str);
    str++; /* skip SP */
    addr->route = parse_nstring(&str);
    str++; /* skip SP */
    addr->mailbox = parse_nstring(&str);
    str++; /* skip SP */
    addr->domain = parse_nstring(&str);
}

/*
 * Read an nstring from cached bodystructure.
 * Analog to mesage_write_nstring().
 * If 'copy' is set, returns a freshly allocated copy of the string,
 * otherwise is returns a pointer to the string which will be overwritten
 * on the next call to message_read_nstring()
 */
static int message_read_nstring(struct protstream *strm, char **str, int copy)
{
    static struct buf buf = BUF_INITIALIZER;
    int c;

    c = getnstring(strm, NULL, &buf);

    if (str) {
	if (!buf.s) *str = NULL;
	else if (copy) *str = xstrdup(buf.s);
	else *str = buf.s;
    }

    return c;
}

/*
 * Read a parameter list from cached bodystructure.
 * If withattr is set, attribute/value pairs will be read,
 * otherwise, just values are read.
 */
static int message_read_params(struct protstream *strm, struct param **paramp,
			       int withattr)
{
    int c;

    if ((c = prot_getc(strm)) == '(') {
	/* parse list */
	struct param *param;

	do {
	    *paramp = param = (struct param *) xzmalloc(sizeof(struct param));

	    if (withattr) {
		/* attribute */
		c = message_read_nstring(strm, &param->attribute, 1);
	    }

	    /* value */
	    c = message_read_nstring(strm, &param->value, 1);

	    /* get ready to append the next parameter */
	    paramp = &param->next;

	} while (c == ' ');

	if (c == ')') c = prot_getc(strm);
    }
    else {
	/* NIL */
	prot_ungetc(c, strm);
	c = message_read_nstring(strm, NULL, 0);
    }

    return c;
}

/*
 * Read an address part from cached bodystructure.
 * The string is appended to 'buf' (including NUL).
 */
static int message_read_addrpart(struct protstream *strm,
				 const char **part, unsigned *off, struct buf *buf)
{
    int c;

    c = message_read_nstring(strm, (char **)part, 0);
    if (*part) {
	*off = buf->len;
	buf_appendmap(buf, *part, strlen(*part)+1);
    }

    return c;
}

/*
 * Read an address list from cached bodystructure.
 * Analog to mesage_write_address()
 */
static int message_read_address(struct protstream *strm, struct address **addrp)
{
    int c;

    if ((c = prot_getc(strm)) == '(') {
	/* parse list */
	struct address *addr;
	struct buf buf;
	unsigned nameoff = 0, rtoff = 0, mboxoff = 0, domoff = 0;

	do {
	    *addrp = addr = (struct address *) xzmalloc(sizeof(struct address));
	    buf_init(&buf);

	    /* opening '(' */
	    c = prot_getc(strm);

	    /* name */
	    c = message_read_addrpart(strm, &addr->name, &nameoff, &buf);

	    /* route */
	    c = message_read_addrpart(strm, &addr->route, &rtoff, &buf);

	    /* mailbox */
	    c = message_read_addrpart(strm, &addr->mailbox, &mboxoff, &buf);

	    /* host */
	    c = message_read_addrpart(strm, &addr->domain, &domoff, &buf);

	    /* addr parts must now point into our freeme string */
	    if (buf.len) {
		char *freeme = addr->freeme = buf.s;

		if (addr->name) addr->name = freeme+nameoff;
		if (addr->route) addr->route = freeme+rtoff;
		if (addr->mailbox) addr->mailbox = freeme+mboxoff;
		if (addr->domain) addr->domain = freeme+domoff;
	    }

	    /* get ready to append the next address */
	    addrp = &addr->next;

	} while (((c = prot_getc(strm)) == '(') && prot_ungetc(c, strm));

	if (c == ')') c = prot_getc(strm);
    }
    else {
	/* NIL */
	prot_ungetc(c, strm);
	c = message_read_nstring(strm, NULL, 0);
    }

    return c;
}

/*
 * Read a cached envelope response.
 * Analog to mesage_write_envelope()
 */
static int message_read_envelope(struct protstream *strm, struct body *body)
{
    int c;

    /* opening '(' */
    c = prot_getc(strm);

    /* date */
    c = message_read_nstring(strm, &body->date, 1);

    /* subject */
    c = message_read_nstring(strm, &body->subject, 1);

    /* from */
    c = message_read_address(strm, &body->from);

    /* sender */
    c = message_read_address(strm, &body->sender);

    /* reply-to */
    c = message_read_address(strm, &body->reply_to);

    /* to */
    c = message_read_address(strm, &body->to);

    /* cc */
    c = message_read_address(strm, &body->cc);

    /* bcc */
    c = message_read_address(strm, &body->bcc);

    /* in-reply-to */
    c = message_read_nstring(strm, &body->in_reply_to, 1);

    /* message-id */
    c = message_read_nstring(strm, &body->message_id, 1);

    if (c == ')') c = prot_getc(strm);

    return c;
}

/*
 * Read cached bodystructure response.
 * Analog to mesage_write_body()
 */
static int message_read_body(struct protstream *strm, struct body *body)
{
#define prot_peek(strm) prot_ungetc(prot_getc(strm), strm)

    int c;

    /* opening '(' */
    c = prot_getc(strm);

    /* check for multipart */
    if ((c = prot_peek(strm)) == '(') {

	body->type = xstrdup("MULTIPART");
	do {
	    body->subpart =
		(struct body *)xrealloc((char *)body->subpart,
					(body->numparts+1)*sizeof(struct body));
	    memset(&body->subpart[body->numparts], 0, sizeof(struct body));
	    c = message_read_body(strm, &body->subpart[body->numparts++]);

	} while (((c = prot_getc(strm)) == '(') && prot_ungetc(c, strm));

	/* body subtype */
	c = message_read_nstring(strm, &body->subtype, 1);

	/* extension data */

	/* body parameters */
	c = message_read_params(strm, &body->params, 1);
    }
    else {
	/* non-multipart */

	/* body type */
	c = message_read_nstring(strm, &body->type, 1);

	/* body subtype */
	c = message_read_nstring(strm, &body->subtype, 1);

	/* body parameters */
	c = message_read_params(strm, &body->params, 1);

	/* body id */
	c = message_read_nstring(strm, &body->id, 1);

	/* body description */
	c = message_read_nstring(strm, &body->description, 1);

	/* body encoding */
	c = message_read_nstring(strm, &body->encoding, 1);

	/* body size */
	c = getint32(strm, (int32_t *) &body->content_size);

	if (!strcmp(body->type, "TEXT")) {
	    /* body lines */
	    c = getint32(strm, (int32_t *) &body->content_lines);
	}
	else if (!strcmp(body->type, "MESSAGE") &&
		 !strcmp(body->subtype, "RFC822")) {

	    body->subpart = (struct body *) xzmalloc(sizeof(struct body));

	    /* envelope structure */
	    c = message_read_envelope(strm, body->subpart);

	    /* body structure */
	    c = message_read_body(strm, body->subpart);
	    c = prot_getc(strm); /* trailing SP */

	    /* body lines */
	    c = getint32(strm, (int32_t *) &body->content_lines);
	}

	/* extension data */

	/* body MD5 */
	c = message_read_nstring(strm, &body->md5, 1);
    }

    /* common extension data */

    /* body disposition */
    if ((c = prot_getc(strm)) == '(') {
	c = message_read_nstring(strm, &body->disposition, 1);

	c = message_read_params(strm, &body->disposition_params, 1);
	if (c == ')') c = prot_getc(strm); /* trailing SP */
    }
    else {
	/* NIL */
	prot_ungetc(c, strm);
	c = message_read_nstring(strm, &body->disposition, 1);
    }

    /* body language */
    if ((c = prot_peek(strm)) == '(') {
	c = message_read_params(strm, &body->language, 0);
    }
    else {
	char *lang;

	c = message_read_nstring(strm, &lang, 1);
	if (lang) {
	    body->language = (struct param *) xzmalloc(sizeof(struct param));
	    body->language->value = lang;
	}
    }

    /* body location */
    c = message_read_nstring(strm, &body->location, 1);

    /* XXX  We currently don't store any other extension data.
            MUST keep in sync with message_write_body() */

    return c;
}

/*
 * Read cached binary bodystructure.
 * Analog to mesage_write_section()
 */
static void message_read_binarybody(struct body *body, const char **sect)
{
    bit32 n, i;
    const char *p = *sect;
    struct body *subpart;

    n = CACHE_ITEM_BIT32(*sect);
    p = *sect += CACHE_ITEM_SIZE_SKIP;
    if (!n) return;

    if (!strcmp(body->type, "MESSAGE") && !strcmp(body->subtype, "RFC822") &&
	body->subpart->numparts) {
	subpart = body->subpart->subpart;
	body = body->subpart;
    }
    else {
	/* If a message/rfc822 contains a non-multipart,
	   we don't care about part 0 (message header) */
	subpart = body->subpart;
	body = NULL;
    }

    if (!body) {
	/* skip header part */
	p += 5 * CACHE_ITEM_SIZE_SKIP;
    }
    else {
	/* read header part */
	body->header_offset = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	body->header_size = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	body->content_offset = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	body->content_size = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	body->charset_cte = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
    }

    /* read body parts */
    for (i = 0; i < n-1; i++) {
	subpart[i].header_offset = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	subpart[i].header_size = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	subpart[i].content_offset = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	subpart[i].content_size = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
	subpart[i].charset_cte = CACHE_ITEM_BIT32(p);
	p += CACHE_ITEM_SIZE_SKIP;
    }

    /* read sub-parts */
    for (*sect = p, i = 0; i < n-1; i++) {
	message_read_binarybody(&subpart[i], sect);
    }

}

/*
 * Read cached envelope, binary bodystructure response and binary bodystructure
 * of the specified record.  Populates 'body' which must be freed by the caller.
 */
EXPORTED void message_read_bodystructure(struct index_record *record, struct body **body)
{
    struct protstream *strm;
    struct body toplevel;
    const char *binbody;

    memset(&toplevel, 0, sizeof(struct body));
    toplevel.type = "MESSAGE";
    toplevel.subtype = "RFC822";
    toplevel.subpart = *body = xzmalloc(sizeof(struct body));

    /* Read envelope response from cache */
    strm = prot_readmap(cacheitem_base(record, CACHE_ENVELOPE),
			cacheitem_size(record, CACHE_ENVELOPE));
    prot_setisclient(strm, 1);  /* no-sync literals */

    message_read_envelope(strm, *body);
    prot_free(strm);

    /* Read bodystructure response from cache */
    strm = prot_readmap(cacheitem_base(record, CACHE_BODYSTRUCTURE),
			cacheitem_size(record, CACHE_BODYSTRUCTURE));
    prot_setisclient(strm, 1);  /* no-sync literals */

    message_read_body(strm, *body);
    prot_free(strm);

    /* Read binary bodystructure from cache */
    binbody = cacheitem_base(record, CACHE_SECTION);
    message_read_binarybody(&toplevel, &binbody);
}

static void de_nstring_buf(struct buf *src, struct buf *dst)
{
    char *p, *q;

    if (src->s && src->len == 3 && !memcmp(src->s, "NIL", 3)) {
	buf_free(dst);
	return;
    }
    q = src->s;
    p = parse_nstring(&q);
    buf_setmap(dst, p, q-p);
    buf_cstring(dst);
}

static void message1_get_subject(struct index_record *record, struct buf *buf)
{
    struct buf tmp = BUF_INITIALIZER;
    buf_copy(&tmp, cacheitem_buf(record, CACHE_SUBJECT));
    de_nstring_buf(&tmp, buf);
    buf_free(&tmp);
}

/*
 * Generate a conversation id from the given message.
 * The conversation id is defined as the first 64b of
 * the SHA1 of the message, except that an all-zero
 * conversation id is not valid.
 */
static conversation_id_t generate_conversation_id(
			    const struct index_record *record)
{
    conversation_id_t cid = 0;
    size_t i;

    assert(record->guid.status == GUID_NONNULL);

    for (i = 0 ; i < sizeof(cid) ; i++) {
	cid <<= 8;
	cid |= record->guid.value[i];
    }

    /*
     * We carefully avoid returning NULLCONVERSATION as
     * a new cid, as that would confuse matters no end.
     */
    if (cid == NULLCONVERSATION)
	cid = 1;

    return cid;
}

/*
 * In RFC2822, the In-Reply-To field is explicitly required to contain
 * only message-ids, whitespace and commas.  The old RFC822 was less
 * well specified and allowed all sorts of stuff.  We used to be equally
 * liberal here in parsing the field.  Sadly some versions of the NMH
 * mailer will generate In-Reply-To containing email addresses which we
 * cannot tell from message-ids, leading to massively confused
 * threading.  So we have to be slightly stricter.
 */
static int is_valid_rfc2822_inreplyto(const char *p)
{
    if (!p)
	return 1;

    /* skip any whitespace */
    while (*p && (isspace(*p) || *p == ','))
	p++;

    return (!*p || *p == '<');
}

/*
 * Update the conversations database for the given
 * mailbox, to account for the given message.
 * @body may be NULL, in which case we get everything
 * we need out of the cache item in @record.
 */
EXPORTED int message_update_conversations(struct conversations_state *state,
					  struct index_record *record,
					  conversation_t **convp)
{
    char *hdrs[4];
    char *c_refs = NULL, *c_env = NULL, *c_me_msgid = NULL;
    struct buf msubject = BUF_INITIALIZER;
    strarray_t msgidlist = STRARRAY_INITIALIZER;
    arrayu64_t matchlist = ARRAYU64_INITIALIZER;
    arrayu64_t emptylist = ARRAYU64_INITIALIZER;
    arrayu64_t cids = ARRAYU64_INITIALIZER;
    conversation_t *conv = NULL;
    const char *msubj = NULL;
    int i;
    int j;
    int r = 0;
    char *msgid = NULL;

    /*
     * Gather all the msgids mentioned in the message, starting with
     * the oldest message in the References: header, then any mesgids
     * mentioned in the In-Reply-To: header, and finally the message's
     * own Message-Id:.  In general this will result in duplicates (a
     * correct References: header will contain as its last entry the
     * msgid in In-Reply-To:), so we weed those out before proceeding
     * to the database.
     */
    if (cache_len(record)) {
	/* we have cache loaded, get what we need there */
	strarray_t want = STRARRAY_INITIALIZER;
	char *envtokens[NUMENVTOKENS];

	/* get References from cached headers */
	c_refs = xstrndup(cacheitem_base(record, CACHE_HEADERS),
			  cacheitem_size(record, CACHE_HEADERS));
	strarray_append(&want, "references");
	message_pruneheader(c_refs, &want, 0);
	hdrs[0] = c_refs;

	/* get In-Reply-To, Message-ID out of the envelope
	 *
	 * get a working copy; strip outer ()'s
	 * +1 -> skip the leading paren
	 * -2 -> don't include the size of the outer parens
	 */
	c_env = xstrndup(cacheitem_base(record, CACHE_ENVELOPE) + 1,
			 cacheitem_size(record, CACHE_ENVELOPE) - 2);
	parse_cached_envelope(c_env, envtokens, NUMENVTOKENS);
	hdrs[1] = envtokens[ENV_INREPLYTO];
	hdrs[2] = envtokens[ENV_MSGID];

	/* get X-ME-Message-ID from cached headers */
	c_me_msgid = xstrndup(cacheitem_base(record, CACHE_HEADERS),
			      cacheitem_size(record, CACHE_HEADERS));
	strarray_set(&want, 0, "x-me-message-id");
	message_pruneheader(c_me_msgid, &want, 0);
	hdrs[3] = c_me_msgid;

	strarray_fini(&want);

	message1_get_subject(record, &msubject);

	/* work around stupid message_guid API */
	message_guid_isnull(&record->guid);
    }
    else {
	/* nope, now we're screwed */
	return IMAP_INTERNAL;
    }

    if (!is_valid_rfc2822_inreplyto(hdrs[1]))
	hdrs[1] = NULL;

    /* Note that a NULL subject, e.g. due to a missing Subject: header
     * field in the original message, is normalised to "" not NULL */
    conversation_normalise_subject(&msubject);
    msubj = buf_cstring(&msubject);

    for (i = 0 ; i < 4 ; i++) {
	while ((msgid = find_msgid(hdrs[i], &hdrs[i])) != NULL) {
	    /*
	     * The issue of case sensitivity of msgids is curious.
	     * RFC2822 seems to imply they're case-insensitive,
	     * without explicitly stating so.  So here we punt
	     * on that being the case.
	     *
	     * Note that the THREAD command elsewhere in Cyrus
	     * assumes otherwise.
	     */
	    msgid = lcase(msgid);

	    /* already seen this one? */
	    if (strarray_find(&msgidlist, msgid, 0) >= 0) {
		free(msgid);
		continue;
	    }

	    strarray_appendm(&msgidlist, msgid);

	    /* Lookup the conversations database to work out which
	     * conversation ids that message belongs to. */
	    r = conversations_get_msgid(state, msgid, &cids);
	    if (r) goto out;

	    for (j = 0; j < cids.count; j++) {
		conversation_id_t cid = arrayu64_nth(&cids, j);
		r = conversation_load(state, cid, &conv);
		if (r) goto out;
		if (!conv)
		    arrayu64_add(&emptylist, cid);
		/* [IRIS-1576] if X-ME-Message-ID says the messages are
		* linked, ignore any difference in Subject: header fields. */
		else if (i == 3 || !strcmpsafe(conv->subject, msubj))
		    arrayu64_add(&matchlist, cid);
	    }

	    conversation_free(conv);
	    conv = NULL;
	}
    }

    if (!record->silent) {
	conversation_id_t newcid = record->cid;
	conversation_id_t val;

	/* Work out the new CID this message will belong to.
	 * Use the MAX of any CIDs found - as NULLCONVERSATION is
	 * numerically zero this will be the only non-NULL CID or
	 * the MAX of two or more non-NULL CIDs */
	val = arrayu64_max(&matchlist);
	if (val > newcid) newcid = val;

	val = arrayu64_max(&emptylist);
	if (val > newcid) newcid = val;

	if (!newcid)
	    newcid = generate_conversation_id(record);

	/* Mark any CID renames */
	for (i = 0 ; i < matchlist.count ; i++)
	    conversations_rename_cid(state, arrayu64_nth(&matchlist, i), newcid);

	if (record->cid) conversations_rename_cid(state, record->cid, newcid);
	else record->cid = newcid;
    }

    if (!record->cid) goto out;

    /* for CIDs with no 'B' record (hence, no existing members) it is
     * safe to rename all the entries for that CID to the higher numbered
     * cid.  In both master and replica cases, this will execute once the
     * last message has its CID renamed */
    for (i = 0; i < emptylist.count; i++) {
	conversation_id_t item = arrayu64_nth(&emptylist, i);
	conversations_rename_cidentry(state, item, record->cid);
    }

    r = conversation_load(state, record->cid, &conv);
    if (r) goto out;

    if (!conv) conv = conversation_new(state);

    /* Create the subject header if not already set */
    if (!conv->subject)
	conv->subject = xstrdupnull(msubj);

    /*
     * Update the database to add records for all the message-ids
     * not already mentioned.  Note that add_msgid does the right
     * thing[tm] when the cid already exists.
     */
    for (i = 0 ; i < msgidlist.count ; i++) {
	r = conversations_add_msgid(state, strarray_nth(&msgidlist, i), record->cid);
	if (r) goto out;
    }

out:
    free(msgid);
    strarray_fini(&msgidlist);
    arrayu64_fini(&matchlist);
    arrayu64_fini(&emptylist);
    arrayu64_fini(&cids);
    free(c_refs);
    free(c_env);
    free(c_me_msgid);
    buf_free(&msubject);

    if (r)
	conversation_free(conv);
    else if (convp)
	*convp = conv;
    else {
	r = conversation_save(state, record->cid, conv);
	conversation_free(conv);
    }

    return r;
}


/*

  Format of the CACHE_SECTION cache item is a binary encoding
  tree of MIME sections.  In something like rpcgen notation
  (see RFC 4506):

    struct part {
	uint32_t header_offset;
	uint32_t header_size;
	uint32_t content_offset;
	uint32_t content_size;
	uint16_t charset;
	uint16_t encoding;
    };

    struct section {
	unsigned int numparts;
	struct part parts[numparts];
	struct section[numparts-1];
    };

*/

/*
 * Iterate 'proc' over all the MIME parts of the message defined
 * by `record' and 'msg'.  Uses the SECTION information from the
 * cyrus.cache, so 'record' needs to have had mailbox_cacherecord()
 * called on it beforehand.
 *
 * Parameters passed to 'proc' are:
 *
 *    partno - part number within the innermost MIME space being
 *             iterated.  Most useful for telling whether we are
 *             being given a header (partno=0) or a body part (>0).
 *    charset - a charset number, as returned from charse_lookupname()
 *    encoding - one of the ENCODING_* constants e.g. ENCODING_QP.
 *    data - read-only struct buf pointing to the mapped raw (i.e.
 *           not decoded) section data.
 *    rock - the 'rock' parameter passed in.
 *
 * If 'proc' returns non-zero, the iteration finishes early and the
 * return value of 'proc' is returned.  Otherwise returns 0.
 */
int message_foreach_part(struct index_record *record,
			 const struct buf *msg,
			 int (*proc)(int partno, int charset, int encoding,
				     struct buf *data, void *rock),
			 void *rock)
{
    int partsleft = 1;
    int subparts;
    unsigned long start;
    int partno, encoding, charset;
    int len;
    int r;
    const char *cachestr = cacheitem_base(record, CACHE_SECTION);
    struct buf data = BUF_INITIALIZER;

    /* Won't find anything in a truncated file */
    if (!msg || !msg->s || !msg->len) return 0;

    while (partsleft--) {
	subparts = CACHE_ITEM_BIT32(cachestr);
	cachestr += 4;
	if (subparts) {
	    partsleft += subparts-1;

	    for (partno = 0 ; partno < subparts ; partno++) {
		if (!partno) {
		    start = CACHE_ITEM_BIT32(cachestr+0*4);
		    len = CACHE_ITEM_BIT32(cachestr+1*4);
		}
		else {
		    start = CACHE_ITEM_BIT32(cachestr+2*4);
		    len = CACHE_ITEM_BIT32(cachestr+3*4);
		}
		charset = CACHE_ITEM_BIT32(cachestr+4*4) >> 16;
		encoding = CACHE_ITEM_BIT32(cachestr+4*4) & 0xff;
		cachestr += 5*4;

		if (len <= 0)
		    continue;	    /* may be a validly nonexistant section */

		/* trim the range [start,start+len) */
		if (start > msg->len) {
		    start = msg->len;
		    len = 0;
		}
		else if (start + len > msg->len) {
		    len = msg->len - start;
		}
		if (len == 0)
		    continue;	    /* probably corrupt data */

		buf_init_ro(&data, msg->s + start, len);
		r = proc(partno, charset, encoding, &data, rock);
		buf_free(&data);
		if (r) return r;
	    }
	}
    }

    return 0;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

/*
 * Handling field descriptors.  Every header field encountered
 * has it's own field_desc_t* object, some pre-defined and some
 * dynamically added as we encounter them in raw message data
 * or in cached header data.  The field_desc_t tells us a number
 * of useful things about how to handle the field, e.g. is it
 * cached, and can it be found in the cached ENVELOPE.
 */

static void field_desc_insert(field_desc_t *desc)
{
    void *old;
    int idx;

    if (!desc->id)
	desc->id = next_field_id++;
    idx = (desc->id & ID_MASK);

    if (!descs_by_name.size)
	construct_hash_table(&descs_by_name, 128, 0);
    old = hash_insert(desc->name, (void *)desc, &descs_by_name);
    /* names must be unique */
    assert(old == NULL || old == (void *)desc);

    /* ids must be unique too */
    assert(ptrarray_nth(&descs_by_id, idx) == NULL);
#if 1
    /* HACK: work around a bug in ptrarray where set() past the end
     * fails to expand the array sparsely */
    while (descs_by_id.count < idx)
	ptrarray_append(&descs_by_id, NULL);
    if (descs_by_id.count == idx)
	ptrarray_append(&descs_by_id, desc);
    else
	ptrarray_set(&descs_by_id, idx, desc);
    /* END HACK */
#else
    ptrarray_set(&descs_by_id, idx, desc);
#endif
    assert(ptrarray_nth(&descs_by_id, idx) == (void *)desc);
}

/* Add and return a dynamic field_desc.  Takes over 'name'. */
static field_desc_t *field_desc_add(char *name)
{
    field_desc_t *desc;

    desc = xzmalloc(sizeof(*desc));
    desc->name = (const char *)name;
    desc->min_cache_version = BIT32_MAX;
    desc->cache_idx = -1;
    desc->env_idx = -1;
    field_desc_insert(desc);
    return desc;
}

static void field_desc_init_builtins(void)
{
    field_desc_t *desc;

    /* Note: these are deliberately not const, so we can use
     * them read-write at runtime */
    static field_desc_t builtins[] = {
	/* things we have always cached */
	{ "priority", 0, 0, -1, -1 },
	{ "references", 0, ID_REFERENCES, -1, -1 },
	{ "resent-from", 0, 0, -1, -1 },
	{ "newsgroups", 0, 0, -1, -1 },
	{ "followup-to", 0, 0, -1, -1 },

	/* x headers that we may want to cache anyway */
	{ "x-mailer", 1, 0, -1, -1 },
	{ "x-trace", 1, 0, -1, -1 },

	/* outlook express seems to want these */
	{ "x-ref", 2, 0, -1, -1 },
	{ "x-priority", 2, 0, -1, -1 },
	{ "x-msmail-priority", 2, 0, -1, -1 },
	{ "x-msoesrec", 2, 0, -1, -1 },

	/* for efficient FastMail interface display */
	{ "x-spam-score", 3, 0, -1, -1 },
	{ "x-spam-hits", 3, 0, -1, -1 },
	{ "x-spam-source", 3, 0, -1, -1 },
	{ "x-resolved-to", 3, 0, -1, -1 },
	{ "x-delivered-to", 3, 0, -1, -1 },
	{ "x-mail-from", 3, 0, -1, -1 },
	{ "x-truedomain", 3, 0, -1, -1 },
	{ "x-truedomain-dkim", 3, 0, -1, -1 },
	{ "x-truedomain-spf", 3, 0, -1, -1 },
	{ "x-truedomain-domain", 3, 0, -1, -1 },

	/* for conversations */
	{ "x-me-message-id", 4, 0, -1, -1 },

	/* things to never cache */
	{ "bcc", BIT32_MAX, ID_BCC, CACHE_BCC, ENV_BCC },
	{ "cc", BIT32_MAX, ID_CC, CACHE_CC, ENV_CC },
	{ "date", BIT32_MAX, ID_DATE, -1, ENV_DATE },
	{ "delivery-date", BIT32_MAX, 0, -1, -1 },
	{ "envelope-to", BIT32_MAX, 0, -1, -1 },
	{ "from", BIT32_MAX, ID_FROM, CACHE_FROM, ENV_FROM },
	{ "in-reply-to", BIT32_MAX, ID_IN_REPLY_TO, -1, ENV_INREPLYTO },
	{ "mime-version", BIT32_MAX, ID_MIME_VERSION, -1, -1 },
	{ "content-type", BIT32_MAX, ID_CONTENT_TYPE, -1, -1 },
	{ "content-transfer-encoding", BIT32_MAX,
	    ID_CONTENT_TRANSFER_ENCODING, -1, -1 },
	{ "reply-to", BIT32_MAX, 0, -1, -1 },
	{ "received", BIT32_MAX, 0, -1, -1 },
	{ "return-path", BIT32_MAX, 0, -1, -1 },
	{ "sender", BIT32_MAX, 0, -1, -1 },
	/* Subject: appears as CACHE_SUBJECT in the cache but that
	 * field is decoded and we want the raw value which is in
	 * the cached envelope. */
	{ "subject", BIT32_MAX, ID_SUBJECT, -1, ENV_SUBJECT },
	{ "to", BIT32_MAX, ID_TO, CACHE_TO, ENV_TO },

	/* signatures tend to be large, and are useless without the body */
	{ "dkim-signature", BIT32_MAX, 0, -1, -1 },
	{ "domainkey-signature", BIT32_MAX, 0, -1, -1 },
	{ "domainkey-x509", BIT32_MAX, 0, -1, -1 },

	/* older versions of PINE (before 4.56) need message-id in the cache too
	 * though technically it is a waste of space because it is in
	 * ENVELOPE.  We should probably uncomment the following at some
	 * future point [ken3 notes this may also be useful to have here for
	 * threading so we can avoid parsing the envelope] */
	{ "message-id", BIT32_MAX, ID_MESSAGE_ID, -1, ENV_MSGID },

	/* Not cached in any way, but we will be looking them up */
	{ "list-id", BIT32_MAX, ID_LIST_ID, -1, -1 },
	{ "mailing-list", BIT32_MAX, ID_MAILING_LIST, -1, -1 },

	{ NULL, 0, 0, 0, 0 }
    };

    for (desc = builtins ; desc->name ; desc++)
	field_desc_insert(desc);
}

static field_desc_t *field_desc_get_byname(const char *name, int len,
					   int create_flag)
{
    field_desc_t *desc;
    char namebuf[MAX_FIELDNAME_LENGTH];

    if (len <= 0) len = strlen(name);
    if (len >= MAX_FIELDNAME_LENGTH)
	return NULL;
    memcpy(namebuf, name, len);
    namebuf[len] = '\0';
    lcase(namebuf);

    if (!descs_by_name.size)
	field_desc_init_builtins();

    desc = hash_lookup(namebuf, &descs_by_name);
    if (!desc && create_flag)
	desc = field_desc_add(xstrdup(namebuf));
    return desc;
}

static field_desc_t *field_desc_get_byid(unsigned int id)
{
    if (!descs_by_name.size)
	field_desc_init_builtins();

    return ptrarray_nth(&descs_by_id, id & ID_MASK);
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static inline int is_finished(const segment_t *s)
{
    return (s != &unfinished_seg);
}

static inline int has_unique_children(const segment_t *s)
{
    return (s->id != ID_HEADER);
}

static inline int is_part(const segment_t *s)
{
    return ((s->id & TYPE_MASK) == T_PART);
}

static part_t *get_part(segment_t *s)
{
    while (s && !is_part(s))
	s = s->parent;
    /* safe downcast */
    return (part_t *)s;
}

#define to_segment(part)	    (&(part)->super)

static void segment_init(segment_t *s, unsigned int id)
{
    /* there's only one of these */
    assert(id != ID_UNFINISHED);
    s->id = id;
    s->children = &unfinished_seg;
}

static segment_t *segment_new(unsigned int id)
{
    segment_t *s = xzmalloc(sizeof(segment_t));
    segment_init(s, id);
    return s;
}

static void segment_free(segment_t *s)
{
    segment_t *child;

    if (!is_finished(s))
	return;

    while ((child = s->children)) {
	s->children = child->next;
	segment_free(child);
    }

    if (is_part(s)) {
	part_t *part = get_part(s);
	free(part->type);
	free(part->subtype);
	free(part->boundary);
    }

    free(s);
}

/* Adjust the shape of a new parent segment to cope with
 * the newly added or reshaped child */
static void segment_adjust_shape(segment_t *parent, segment_t *child)
{
    if (!parent->offset && !parent->length) {
	parent->offset = child->offset;
	parent->length = child->length;
    }
    else {
	unsigned long child_end = child->offset + child->length;
	unsigned long parent_end = parent->offset + parent->length;
	if (child_end > parent_end)
	    parent->length = child_end - parent->offset;
    }
}

static void segment_set_shape(segment_t *s,
			      unsigned int offset,
			      unsigned int length)
{
    assert(!s->offset);
    assert(!s->length);
    s->offset = offset;
    s->length = length;
    if (s->parent)
	segment_adjust_shape(s->parent, s);
}

/* Give 'parent' a new single child 'child' which covers the same range as
 * 'parent' (which will presumably be reduced later using something like
 * segment_split_right() */
static void segment_bud(segment_t *parent, segment_t *child)
{
    assert(is_finished(parent));
    assert(!is_finished(parent->children));
    assert(!child->parent);

    segment_set_shape(child, parent->offset, parent->length);

    parent->children = child;
    child->next = NULL;
    child->parent = parent;
}

/* Make a segment actually be a leaf, i.e. finished */
static void segment_finish(segment_t *s)
{
    assert(!is_finished(s->children));
    s->children = NULL;
}

/* Find and return the tail pointer of the segment's children */
static segment_t **segment_get_tail(segment_t *s)
{
    segment_t **tailp;

    assert(is_finished(s));

    if (is_finished(s->children)) {
	for (tailp = &s->children ;
	     *tailp ;
	     tailp = &(*tailp)->next)
	    ;
    }
    else {
	segment_finish(s);
	tailp = &s->children;
    }

    return tailp;
}

/* Give 'parent' a new child 'child' at the end of the child */
static void segment_append(segment_t *parent, segment_t *child)
{
    segment_t **tailp = segment_get_tail(parent);

    child->next = NULL;
    *tailp = child;
    child->parent = parent;
    segment_adjust_shape(parent, child);
}

static void segment_detach(segment_t *child)
{
    segment_t **prevp;

    assert(child);
    assert(child->parent);

    for (prevp = &child->parent->children ;
	 *prevp && *prevp != child;
	 prevp = &(*prevp)->next)
	;
    *prevp = child->next;
    child->next = NULL;
}

/* Give 's' a new right sibling and divide it's range between them
 * at offset 'off' from their parent. */
static void segment_split_right(segment_t *s,
				unsigned int off,
				segment_t *sib)
{
    assert(is_finished(s));
    assert(s->parent);
    assert(!sib->parent);

    /* bounds check 'off' and ensure we don't
     * try to create zero length parts */
    assert(off > 0);
    assert(off < s->length);
    /* TODO: perhaps bounds check off against 's's children if any */

    segment_set_shape(sib, s->offset + off, s->length - off);
    s->length = off;
    sib->next = s->next;
    s->next = sib;
    sib->parent = s->parent;
}

static segment_t *segment_find_child(segment_t *s,
				     unsigned int id)
{
    segment_t *child;

    if (!s) return NULL;

    for (child = s->children ; child ; child = child->next) {
	if (child->id == id)
	    return child;
    }
    return NULL;
}

static unsigned int segment_get_num_children(segment_t *s)
{
    segment_t *child;
    unsigned int n = 0;

    if (!s) return 0;

    for (child = s->children ; child ; child = child->next)
	n++;
    return n;
}

#if DEBUG
static const char *indent(int depth)
{
    int i;
    static struct buf buf = BUF_INITIALIZER;
    static int lastdepth = -1;

    if (depth != lastdepth) {
	buf_reset(&buf);
	for (i = 0 ; i < depth ; i++)
	    buf_appendcstr(&buf, "  ");
	lastdepth = depth;
    }
    return buf_cstring(&buf);
}

static void segment_dump(segment_t *s, int depth)
{
    segment_t *child;

    fprintf(stderr, "%sSEG id=", indent(depth));
    switch (s->id) {
    case ID_INVALID:
	fputs("INVALID", stderr);
	break;
    case ID_UNFINISHED:
	fputs("UNFINISHED\n", stderr);
	return;
    case ID_HEADER:
	fputs("HEADER", stderr);
	break;
    case ID_BODY:
	fputs("BODY", stderr);
	break;
    default:
	switch ((s->id & TYPE_MASK)) {
	case T_FIELD: {
	    field_desc_t *desc = field_desc_get_byid(s->id);
	    if (desc)
		fprintf(stderr, "FIELD:%s", desc->name);
	    else
		fprintf(stderr, "FIELD:%x", s->id & ID_MASK);
	    break;
	    }
	case T_PART:
	    fprintf(stderr, "PART:%u", (s->id & ID_MASK));
	    break;
	default:
	    fprintf(stderr, "%08x", s->id);
	    break;
	}
	break;
    }
    fprintf(stderr, " offset=%u length=%u",
	    s->offset, s->length);

    if (is_part(s)) {
	part_t *part = get_part(s);
	fprintf(stderr, " type=%s/%s"
			" charset=%s"
			" encoding=%s"
			" boundary=%s",
		part->type, part->subtype,
		charset_name(part->charset),
		encoding_name(part->encoding),
		part->boundary);
    }

    fputc('\n', stderr);

    for (child = s->children ; child ; child = child->next)
	segment_dump(child, depth+1);
}
#endif

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static segment_t *part_new(message_t *m, unsigned int id)
{
    part_t *part = xzmalloc(sizeof(part_t));
    segment_init(to_segment(part), T_PART|id);
    part->message = m;
    return to_segment(part);
}

static void part_set_type(part_t *part, const char *type,
			  const char *subtype)
{
    free(part->type);
    free(part->subtype);
    part->type = (type ? ucase(xstrdup(type)) : NULL);
    part->subtype = (type ? ucase(xstrdup(subtype)) : NULL);
}

#if DEBUG
static const char *part_get_path(part_t *part)
{
    ptrarray_t ancestors = PTRARRAY_INITIALIZER;
    static struct buf buf = BUF_INITIALIZER;
    int i;

    for ( ; part ; part = get_part(part->super.parent))
	ptrarray_push(&ancestors, part);

    buf_reset(&buf);
    for (i = ancestors.count-1 ; i >= 0  ; i--)
	buf_printf(&buf, "%s%u",
		    (buf.len ? "." : ""),
		    ((segment_t *)ancestors.data[i])->id & ID_MASK);

    ptrarray_fini(&ancestors);
    return buf_cstring(&buf);
}
#endif

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

EXPORTED message_t *message_new(void)
{
    message_t *m;

    m = xzmalloc(sizeof(*m));

    m->refcount = 1;
    m->segs = &unfinished_seg;
    m->cheader_segs = &unfinished_seg;

    return m;
}

static void message_free(message_t *m)
{
    assert(m->refcount == 0);

    message_yield(m, M_ALL);

    free(m->filename);
    m->filename = NULL;

    free(m);
}

EXPORTED message_t *message_new_from_data(const char *base, size_t len)
{
    message_t *m = message_new();
    buf_init_ro(&m->map, base, len);
    m->have = m->given = M_MAP;
    return m;
}

EXPORTED message_t *message_new_from_mailbox(struct mailbox *mailbox, unsigned int recno)
{
    message_t *m = message_new();
    m->mailbox = mailbox;
    m->record.recno = recno;
    m->have = m->given = M_MAILBOX;
    return m;
}

EXPORTED message_t *message_new_from_record(struct mailbox *mailbox,
					    const struct index_record *record)
{
    message_t *m = message_new();
    assert(record->uid > 0);
    m->mailbox = mailbox;
    m->record = *record;
    m->have = m->given = M_MAILBOX|M_RECORD|M_UID;
    return m;
}

EXPORTED message_t *message_new_from_index(struct mailbox *mailbox,
					   const struct index_record *record,
					   uint32_t msgno,
					   uint32_t indexflags)
{
    message_t *m = message_new();
    assert(record->uid > 0);
    m->mailbox = mailbox;
    m->record = *record;
    m->msgno = msgno;
    m->indexflags = indexflags;
    m->have = m->given = M_MAILBOX|M_RECORD|M_UID|M_INDEX;
    return m;
}

EXPORTED message_t *message_new_from_filename(const char *filename)
{
    message_t *m = message_new();
    m->filename = xstrdup(filename);
    m->have = m->given = M_FILENAME;
    return m;
}

EXPORTED message_t *message_ref(message_t *m)
{
    m->refcount++;
    assert(m->refcount >= 1);
    return m;
}

EXPORTED void message_unref(message_t **mp)
{
    message_t *m;

    if (!mp || !(m = *mp)) return;
    assert(m->refcount >= 1);
    if (--m->refcount == 0)
	message_free(m);
    *mp = NULL;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

/*
 * Open or create resources which we need but do not yet have.
 */
static int message_need(message_t *m, unsigned int need)
{
#define is_missing(flags)    ((need & ~(m->have)) & (flags))
#define found(flags)	     (m->have |= (flags))
    int r = 0;

    if (!is_missing(M_ALL))
	return 0;	/* easy, we already have it */

    if (is_missing(M_MAILBOX|M_FILENAME)) {
	/* We can't get these for ourselves,
	 * they need to be passed in by the caller */
	return IMAP_NOTFOUND;
    }

    if (is_missing(M_RECORD|M_UID)) {
	r = message_need(m, M_MAILBOX);
	if (r) return r;
	r = mailbox_read_index_record(m->mailbox, m->record.recno, &m->record);
	if (r) return r;
	found(M_RECORD|M_UID);
    }

    if (is_missing(M_MAP)) {
	const char *filename;
	if (message_need(m, M_FILENAME) == 0)
	    filename = m->filename;
	else if (message_need(m, M_MAILBOX|M_UID) == 0)
	    filename = mailbox_message_fname(m->mailbox, m->record.uid);
	else
	    return IMAP_NOTFOUND;
	r = message2_map_file(m, filename);
	if (r) return r;
	found(M_MAP);
    }

    if (is_missing(M_CACHE)) {
	r = message_need(m, M_MAILBOX|M_RECORD);
	if (r) return r;
	r = mailbox_cacherecord(m->mailbox, &m->record);
	if (r) return r;
	found(M_CACHE);
    }

    if (is_missing(M_SEGS)) {
	if (message_need(m, M_CACHE) == 0) {
	    r = message2_parse_csections(m);
	    if (r) return r;
	    found(M_SEGS);	    /* no M_BODY yet */
	}
	else if (message_need(m, M_MAP) == 0) {
	    if (!is_finished(m->segs)) {
		m->segs = part_new(m, 1);
		segment_set_shape(m->segs, 0, m->map.len);
	    }
	    r = message2_parse_header(get_part(m->segs), &m->map);
	    if (r) return r;
	    found(M_SEGS|M_BODY);
	}
	else
	    return IMAP_NOTFOUND;
#if DEBUG
	segment_dump(m->segs, 0);
#endif
    }

    if (is_missing(M_BODY)) {
	r = message_need(m, M_SEGS);
	if (r) return r;
	if (is_missing(M_BODY) && message_need(m, M_CACHE) == 0) {
	    r = message2_parse_cbodystructure(m);
	    if (r) return r;
	    found(M_BODY);
	}
    }

    if (is_missing(M_CHEADER)) {
	r = message_need(m, M_CACHE);
	if (r) return r;
	r = message2_parse_cheader(m);
	if (r) return r;
	found(M_CHEADER);
    }

    if (is_missing(M_CENVELOPE)) {
	r = message_need(m, M_CACHE);
	if (r) return r;
	r = message2_parse_cenvelope(m);
	if (r) return r;
	found(M_CENVELOPE);
    }

    /* Check that we got everything we asked for and could get */
    assert(!is_missing(M_ALL));

    return 0;
#undef found
#undef is_missing
}

/*
 * Yield open resources.
 */
static void message_yield(message_t *m, unsigned int yield)
{
    /* Can only yield those resources we have. */
    yield &= m->have;

    /* Do not yield resources we were given at initialisation
     * time, they cannot be rebuilt again later. */
    yield &= ~m->given;

    /* nothing to free for these - they're not constructed
     * or have no dynamically allocated memory */
    yield &= ~(M_MAILBOX|M_RECORD|M_FILENAME|M_UID|M_CACHE);

    if ((yield & M_MAP)) {
	buf_free(&m->map);
	m->have &= ~M_MAP;
    }

    if ((yield & M_SEGS)) {
	segment_free(m->segs);
	m->segs = NULL;
	m->have &= ~(M_SEGS|M_BODY);
    }

    if ((yield & M_CHEADER)) {
	buf_free(&m->cheader_map);
	segment_free(m->cheader_segs);
	m->cheader_segs = NULL;
	m->have &= ~M_CHEADER;
    }

    if ((yield & M_CENVELOPE)) {
	free(m->envelope);
	m->envelope = NULL;
	m->have &= ~M_CENVELOPE;
    }

    /* Check we yielded everything we could */
    assert((yield & m->have) == 0);
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static int message2_map_segment(message_t *m, segment_t *s, struct buf *buf)
{
    int r;

    if (!s) return IMAP_NOTFOUND;

    r = message_need(m, M_MAP);
    if (r) return r;

    buf_init_ro(buf, m->map.s + s->offset, s->length);
    return 0;
}

static int message2_expand_segment(message_t *m, segment_t *s)
{
    int r;

    if (is_finished(s->children))
	return 0;

    if (s->id == ID_BODY) {
	part_t *part = get_part(s);
	if (!strcmpsafe(part->type, "MULTIPART")) {
	    r = message2_parse_multipart(part, s);
	    if (r) return r;
	}
	else
	    segment_finish(s);
    }
    else if (s->id == ID_HEADER || is_part(s)) {
	/* ID_HEADER happens if we've read a message's segments from
	 * cyrus.cache and not parsed the header in detail. */
	struct buf map = BUF_INITIALIZER;
	r = message2_map_segment(m, s, &map);
	if (r) return r;
	r = message2_parse_header(get_part(s), &map);
	if (r) return r;
	buf_free(&map);
    }

    assert(is_finished(s->children));
#if DEBUG
    segment_dump(m->segs, 0);
#endif
    return 0;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

/*
 * Parse various information out of the cyrus.cache.
 */

/* Parse the cached header (strictly, header subset) */
static int message2_parse_cheader(message_t *m)
{
    buf_init_ro(&m->cheader_map,
		cacheitem_base(&m->record, CACHE_HEADERS),
		cacheitem_size(&m->record, CACHE_HEADERS));
    m->cheader_segs = part_new(m, 1);
    segment_set_shape(m->cheader_segs, 0, m->cheader_map.len);
    return message2_parse_header(get_part(m->cheader_segs),
				 &m->cheader_map);
}

/* Parse the cached envelope */
static int message2_parse_cenvelope(message_t *m)
{
    int tokslen;
    int strslen;
    char **toks;
    char *strs;

    if (cacheitem_size(&m->record, CACHE_ENVELOPE) < 2)
	return IMAP_INTERNAL;

    tokslen = NUMENVTOKENS * sizeof(char *);
    strslen = cacheitem_size(&m->record, CACHE_ENVELOPE) - 2;
    toks = xzmalloc(tokslen + strslen + 1);
    strs = ((char *)toks) + tokslen;

    /* +1 -> skip the leading paren */
    /* -2 -> don't include the size of the outer parens */
    memcpy(strs, cacheitem_base(&m->record, CACHE_ENVELOPE) + 1, strslen);

    parse_cached_envelope(strs, toks, NUMENVTOKENS);

    m->envelope = toks;
    return 0;
}

/* trim the range [start,start+len) */
#define TRIM_RANGE(off, len, size) \
    do { \
	if (len == (uint32_t)-1) \
	    len = 0; \
	else if (off > size) { \
	    len = 0; \
	} \
	else if (off + len > size) { \
	    len = size - off; \
	} \
    } while(0)

#define IS_SHAPED(s, off, len) \
    (((s) == NULL && (len) == 0) || \
     ((s) != NULL && (s)->offset == (off) && (s)->length == (len)))

/* Parse the cached section structure, which gives us a
 * skeleton tree of segments without most of the MIME
 * information. */
static int message2_parse_csections(message_t *m)
{
    segment_t *part;
    segment_t *subpart;
    segment_t *body;
    segment_t *header;
    int is_same;
    int nsubparts;
    int ins;
    uint32_t hdr_start, hdr_len;
    uint32_t con_start, con_len;
    int partno, encoding, charset;
    const char *cachestr = cacheitem_base(&m->record, CACHE_SECTION);
    const char *cacheend = cachestr + cacheitem_size(&m->record, CACHE_SECTION);
    ptrarray_t stack = PTRARRAY_INITIALIZER;
    int r = 0;

    assert(!is_finished(m->segs));
    part = part_new(m, 1);
    ptrarray_push(&stack, part);
    m->segs = part;

    while (stack.count) {
	part = ptrarray_pop(&stack);	/* may be NULL */

	if (cachestr + 4 > cacheend) {
	    /* ran out of data early */
	    r = IMAP_MAILBOX_BADFORMAT;
	    goto out;
	}
	nsubparts = CACHE_ITEM_BIT32(cachestr);
	cachestr += 4;
	if (!nsubparts)
	    continue;	    /* leaf part */
	if (!part)
	    continue;	    /* found 0 length body in parent */

	ins = stack.count;
	for (partno = 0 ; partno < nsubparts ; partno++) {

	    if (cachestr + 5*4 > cacheend) {
		/* ran out of data early */
		r = IMAP_MAILBOX_BADFORMAT;
		goto out;
	    }
	    hdr_start = CACHE_ITEM_BIT32(cachestr+0*4);
	    hdr_len = CACHE_ITEM_BIT32(cachestr+1*4);
	    con_start = CACHE_ITEM_BIT32(cachestr+2*4);
	    con_len = CACHE_ITEM_BIT32(cachestr+3*4);
	    charset = CACHE_ITEM_BIT32(cachestr+4*4) >> 16;
	    encoding = CACHE_ITEM_BIT32(cachestr+4*4) & 0xff;

	    cachestr += 5*4;

	    TRIM_RANGE(hdr_start, hdr_len, m->record.size);
	    TRIM_RANGE(con_start, con_len, m->record.size);

	    subpart = NULL;
	    if (hdr_len || con_len) {

		subpart = part;

		body = segment_find_child(part, ID_BODY);
		header = segment_find_child(part, ID_HEADER);
		is_same = (IS_SHAPED(header, hdr_start, hdr_len) &&
			   IS_SHAPED(body, con_start, con_len));
		if (partno && !is_same) {
		    subpart = part_new(m, partno);
		    segment_append(segment_find_child(part, ID_BODY), subpart);
		}
		get_part(subpart)->charset = charset;
		get_part(subpart)->encoding = encoding;

		if (hdr_len > 0 && !is_same) {
		    segment_t *header = segment_new(ID_HEADER);
		    segment_set_shape(header, hdr_start, hdr_len);
		    segment_append(subpart, header);
		}

		if (con_len > 0 && !is_same) {
		    segment_t *body = segment_new(ID_BODY);
		    segment_set_shape(body, con_start, con_len);
		    segment_append(subpart, body);
		}
	    }

	    if (partno) {
		/* Note: we need to insert at the old tail,
		 * so that the order of children is reversed,
		 * so that it's correct again when we pop off.
		 * Also note: no recursing for part 0, it's a
		 * header only */
		ptrarray_insert(&stack, ins, subpart);
	    }
	}
    }

out:
    ptrarray_fini(&stack);
    return r;
}

/*
 * Skip either a single NIL or a balanced possibly-nested list of
 * nstrings.  Useful for ignoring various constructs from the
 * BODYSTRUCTURE cache.
 */
static int skip_nil_or_nstring_list(struct protstream *prot,
				    int depth __attribute__((unused)))
{
    int r = IMAP_MAILBOX_BADFORMAT;
    int c;
    struct buf word = BUF_INITIALIZER;

    c = prot_getc(prot);
    if (c == EOF)
	goto out;   /* ran out of data */
    if (c == '(') {
	/* possibly-nested list of atoms */
	int treedepth = 1;
	do {
	    c = prot_getc(prot);
	    if (c == ' ')
		c = prot_getc(prot);
	    if (c != ')' && c != '(') {
		prot_ungetc(c, prot);
		c = getnstring(prot, NULL, &word);
#if DEBUG
		if (word.len)
		    fprintf(stderr, "%sskipping string \"%s\" at %d\n",
			    indent(depth), word.s, treedepth);
#endif
	    }
	    if (c == '(')
		treedepth++;
	    else if (c == ')')
		treedepth--;
	    else if (c == ' ')
		prot_ungetc(c, prot);
	    else
		goto out;
	} while (treedepth);
	c = prot_getc(prot);
	if (c != ' ') goto out;
	r = 0;
    }
    else {
	prot_ungetc(c, prot);
	c = getnstring(prot, NULL, &word);
	if (c == ' ' && !word.len) {
	    /* 'NIL' */
#if DEBUG
	    fprintf(stderr, "%sskipping NIL\n", indent(depth));
#endif
	    r = 0;
	    goto out;
	}
    }
    /* else, error */

out:
    buf_free(&word);
    return r;
}

static int parse_bodystructure_part(part_t *part,
				    struct protstream *prot,
				    int depth)
{
    int c;
    int r = 0;
    struct buf buf1 = BUF_INITIALIZER;
    struct buf buf2 = BUF_INITIALIZER;
    segment_t *body = segment_find_child(to_segment(part), ID_BODY);
    int is_multipart = 0;

#if DEBUG
    fprintf(stderr, "%sparsing bodystructure for %s {\n",
	    indent(depth), part_get_path(part));
#endif

    c = prot_getc(prot);
    if (c != '(') {
badformat:
	r = IMAP_MAILBOX_BADFORMAT;
	goto out;
    }

    c = prot_getc(prot);
    prot_ungetc(c, prot);
    if (c == '(') {
	segment_t *s;
	int body_is_fake = 0;

	if (!body) {
	    /* IRIS-1912. Message with Content-Type=multipart/something
	     * but no body at all.  This isn't legal according to
	     * RFC2046 but it does happen.  We create a fake zero-length
	     * body just long enough to parse the BODYSTRUCTURE. */
	    body = segment_new(ID_BODY);
	    segment_append(to_segment(part), body);
	    segment_append(body, part_new(part->message, 1));
	    body_is_fake = 1;
	}
	else if (!is_finished(body->children)) {
	    /* IRIS-1912. Message with Content-Type=multipart/something
	     * and a non-empty body with no boundaries in it.  This
	     * isn't legal according to RFC2046 but it does happen.  We
	     * create a single subpart to finish off the segment subtree
	     * beneath ID_BODY and keep it. */
	    segment_t *subpart, *subbody;

	    subpart = part_new(part->message, 1);
	    segment_set_shape(subpart, body->offset, body->length);
	    segment_append(body, subpart);

	    subbody = segment_new(ID_BODY);
	    segment_set_shape(subbody, body->offset, body->length);
	    segment_append(subpart, subbody);
	    segment_finish(subbody);
	}

	is_multipart = 1;
	/* parse children of a MULTIPART */
	for (s = body->children ; s ; s = s->next) {
	    r = parse_bodystructure_part(get_part(s), prot, depth+1);
	    if (r) goto out;
	}

	c = prot_getc(prot);
	if (c != ' ') goto badformat;

	if (body_is_fake) {
	    segment_detach(body);
	    segment_free(body);
	}
    }
    else {

	/* parse mime-type */
	c = getnstring(prot, NULL, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	fprintf(stderr, "%smime-type=\"%s\"\n", indent(depth), buf1.s);
#endif
    }

    /* parse mime-subtype */
    c = getnstring(prot, NULL, &buf2);
    if (c != ' ') goto badformat;
#if DEBUG
    fprintf(stderr, "%smime-subtype=\"%s\"\n", indent(depth), buf2.s);
#endif

    part_set_type(part, (is_multipart ? "MULTIPART" : buf1.s), buf2.s);

    /* skip mime-params: we have all the ones we care about from SECTION */
    r = skip_nil_or_nstring_list(prot, depth);
    if (r) goto out;

    if (!is_multipart) {

	/* skip msgid: we have it from ENVELOPE */
	c = getnstring(prot, NULL, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	fprintf(stderr, "%smsgid=\"%s\"\n", indent(depth), buf1.s);
#endif

	/* skip description: we don't care */
	c = getnstring(prot, NULL, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	fprintf(stderr, "%sdescription=\"%s\"\n", indent(depth), buf1.s);
#endif

	/* skip encoding: we have it from SECTION */
	c = getnstring(prot, NULL, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	fprintf(stderr, "%sencoding=\"%s\"\n", indent(depth), buf1.s);
#endif

	/* skip content-size: we have it from SECTION */
	c = getword(prot, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	    fprintf(stderr, "%scontent-size=\"%s\"\n", indent(depth), buf1.s);
#endif

	if (!strcmpsafe(part->type, "TEXT")) {

	    /* parse content-lines */
	    c = getword(prot, &buf1);
	    if (c != ' ') goto badformat;
#if DEBUG
	    fprintf(stderr, "%scontent-lines=\"%s\"\n", indent(depth), buf1.s);
#endif

	}
	else if (!strcmpsafe(part->type, "MESSAGE") &&
		 !strcmpsafe(part->subtype, "RFC822")) {

	    /* skip envelope */
	    r = skip_nil_or_nstring_list(prot, depth);
	    if (r) goto out;

	    /* process body */
	    r = parse_bodystructure_part(get_part(body->children),
					 prot, depth+1);
	    if (r) goto out;

	    /* skip trailing space (parse_bs_part doesn't eat it) */
	    c = prot_getc(prot);
	    if (c != ' ') goto badformat;

	    /* parse content-lines */
	    c = getword(prot, &buf1);
	    if (c != ' ') goto badformat;
#if DEBUG
	    fprintf(stderr, "%scontent-lines=\"%s\"\n", indent(depth), buf1.s);
#endif
	}

	/* parse md5sum */
	c = getnstring(prot, NULL, &buf1);
	if (c != ' ') goto badformat;
#if DEBUG
	fprintf(stderr, "%smd5sum=\"%s\"\n", indent(depth), buf1.s);
#endif
    }

    /* skips disposition-and-params */
    r = skip_nil_or_nstring_list(prot, depth);
    if (r) goto out;

    /* parse languages */  /* TODO */
    r = skip_nil_or_nstring_list(prot, depth);
    if (r) goto out;

    /* skip location */
    c = getnstring(prot, NULL, &buf1);
    if (c != ')') goto badformat;
#if DEBUG
    fprintf(stderr, "%slocation=\"%s\"\n", indent(depth), buf1.s);
#endif

    r = 0;
out:
#if DEBUG
    fprintf(stderr, "%s}\n", indent(depth));
#endif
    buf_free(&buf1);
    buf_free(&buf2);
    return r;
}

static int message2_parse_cbodystructure(message_t *m)
{
    struct protstream *prot = NULL;
    int r;

    /* We assume we have a complete and correct tree of segments
     * from the SECTION cache, and we're just filling in some
     * details like MIME types */
    assert(m->have & M_SEGS);
    assert(is_finished(m->segs));

    /* We're reading the cache - double check we have it */
    assert(m->have & M_CACHE);

#if DEBUG
    fprintf(stderr, "parsing bodystructure=\"");
    fwrite(cacheitem_base(&m->record, CACHE_BODYSTRUCTURE), 1,
	    cacheitem_size(&m->record, CACHE_BODYSTRUCTURE), stderr);
    fprintf(stderr, "\"\n");
#endif

    prot = prot_readmap(cacheitem_base(&m->record, CACHE_BODYSTRUCTURE),
			cacheitem_size(&m->record, CACHE_BODYSTRUCTURE));
    if (!prot)
	return IMAP_MAILBOX_BADFORMAT;
    prot_setisclient(prot, 1);	/* don't crash parsing literals */

    r = parse_bodystructure_part(get_part(m->segs), prot, 0);
    prot_free(prot);
#if DEBUG
    segment_dump(m->segs, 0);
#endif
    if (r) {
	syslog(LOG_ERR, "IOERROR: Failed to parse bodystructure: uid=<%u> mailbox=<%s> bs=<%.*s>",
	       m->record.uid, m->mailbox->name,
	       (int)cacheitem_size(&m->record, CACHE_BODYSTRUCTURE),
	       cacheitem_base(&m->record, CACHE_BODYSTRUCTURE));
    }
    return r;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

/*
 * Parsing a raw RFC822 message from mapped data, or just the header
 * part from a cached header.
 */

#define P_UNKNOWN   	0
#define P_BOUNDARY	1
#define P_CHARSET	2

static int parse_param_name(const char *s)
{
    if (!s) return P_UNKNOWN;

    switch (s[0]) {
    case 'B':
    case 'b':
	if (!strcasecmp(s, "boundary"))
	    return P_BOUNDARY;
	break;
    case 'C':
    case 'c':
	if (!strcasecmp(s, "charset"))
	    return P_CHARSET;
	break;
    }
    return P_UNKNOWN;
}

/*
 * Parse the special MIME fields.  Note that we can't just parse these
 * as they appear in the header, because we have to check them in a
 * specific order and they might not appear in that order.
 *
 * We do not return failure: RFC2045 recommends that the defaults be
 * assumed the absence of the Content-Type field, or syntactic errors in
 * the field.
 */
static void handle_mime_fields(part_t *part,
			       const struct buf *mime_fields)
{
    const struct buf *raw;
    char *subtype = NULL;
    rfc822tok_t tok = RFC822TOK_INITIALIZER;
    int t;
    char *val;

    /* parse MIME-Version: */
    raw = &mime_fields[ID_MIME_VERSION - ID_MIME_FIRST];
    /* TODO: per RFC2045 section 4, MIME-Version is required sometimes
     * and not required at some other times. */
    if (raw->s) {
	rfc822tok_init_buf(&tok, raw, 0);
	/* RFC2045 says "It is not possible to fully specify how a mail
	 * reader that conforms with MIME as defined in this document should
	 * treat a message that might arrive in the future with some value
	 * of MIME-Version other than "1.0"."  Thanks for nothing guys. */
	t = rfc822tok_next(&tok, &val);
	if (t != RFC822_ATOM || strcmpsafe(val, "1.0"))
	    goto defaults;
	t = rfc822tok_next(&tok, &val);
	if (t != EOF)
	    goto defaults;
	rfc822tok_fini(&tok);
    }
    else if (part->super.parent == NULL) {
	/* MIME-Version is required in the outermost header of a multipart */
	goto defaults;
    }

    /* parse Content-Type: */
    raw = &mime_fields[ID_CONTENT_TYPE - ID_MIME_FIRST];
    if (!raw->s)
	goto defaults;
    rfc822tok_init_buf(&tok, raw, RFC822_SPECIAL_EQUAL);

    /* parse TYPE/SUBTYPE */
    t = rfc822tok_next(&tok, &val);
    if (t != RFC822_ATOM && t != RFC822_QSTRING)
	goto defaults;
    subtype = strchr(val, '/');
    /* RFC2045 says "a subtype specification is MANDATORY -- it may
     * not be omitted from a Content-Type header field" */
    if (!subtype || !*subtype)
	goto defaults;
    *subtype++ = '\0';
    /* RFC2045 says "The type, subtype, and parameter names are not
     * case sensitive", so we normalise the case here.  We use upper
     * case only for legacy reasons; the old message API used it. */
    part_set_type(part, val, subtype);

    /* RFC2045 says "the "charset" parameter is applicable to any
     * subtype of "text"" */
    if (!strcmp(part->type, "TEXT"))
	part->charset = 0;	    /* US-ASCII is always charset 0 */
    else
	part->charset = CHARSET_UNKNOWN_CHARSET;

    /* parse any parameters */
    while ((t = rfc822tok_next(&tok, &val)) == ';') {
	int param = P_UNKNOWN;
	t = rfc822tok_next(&tok, &val);
	if (t != RFC822_ATOM && t != RFC822_QSTRING)
	    goto defaults;
	param = parse_param_name(val);
	t = rfc822tok_next(&tok, &val);
	if (t != '=')
	    goto defaults;
	t = rfc822tok_next(&tok, &val);
	if (t != RFC822_ATOM && t != RFC822_QSTRING)
	    goto defaults;
	if (!val || !*val)
	    continue;
	if (param == P_BOUNDARY) {
	    /* RFC2045 says "multipart boundaries are case-sensitive" */
	    free(part->boundary);
	    part->boundary = xstrdup(val);
	}
	else if (param == P_CHARSET) {
	    part->charset = charset_lookupname(val);
	}
    }
    if (t != EOF)
	goto defaults;

    /* parse Content-Transfer-Encoding: */
    /* RFC2045 says ""Content-Transfer-Encoding: 7BIT" is assumed if the
     * Content-Transfer-Encoding header field is not present." */
    part->encoding = ENCODING_NONE;
    raw = &mime_fields[ID_CONTENT_TRANSFER_ENCODING - ID_MIME_FIRST];
    if (raw->s) {
	int e;
	rfc822tok_init_buf(&tok, raw, 0);
	t = rfc822tok_next(&tok, &val);
	if (t != RFC822_ATOM && t != RFC822_QSTRING)
	    goto default_encoding;
	e = encoding_lookupname(val);
	if (e == ENCODING_UNKNOWN)
	    goto default_encoding;
	part->encoding = e;
	t = rfc822tok_next(&tok, &val);
	if (t != EOF)
	    goto default_encoding;
    }

    /* post-parse checks */

    if (!strcmp(part->type, "MULTIPART")) {
	/* RFC2045 says "the "boundary" parameter is required for any
	 * subtype of the "multipart" media type" */
	if (!part->boundary)
	    goto defaults;
	/* RFC2045 says "If an entity is of type "multipart" the
	 * Content-Transfer-Encoding is not permitted to have any value
	 * other than "7bit", "8bit" or "binary" */
	if (part->encoding != ENCODING_NONE)
	    goto defaults;
    }

    rfc822tok_fini(&tok);
    return;

defaults:
    /* RFC2045 says "Default RFC 822 messages without a MIME
     * Content-Type header are taken this protocol to be plain text in
     * the US-ASCII character set, which can be explicitly specified as:
     * Content-type: text/plain; charset=us-ascii" */
    part_set_type(part, "TEXT", "PLAIN");
    part->charset = 0;	    /* US-ASCII is always charset 0 */
    part->encoding = ENCODING_NONE;
    free(part->boundary);
    part->boundary = NULL;
    rfc822tok_fini(&tok);
    return;

default_encoding:
    /* RFC2045 says "Any entity with an unrecognized
     * Content-Transfer-Encoding must be treated as if it has a
     * Content-Type of "application/octet-stream"" */
    part_set_type(part, "APPLICATION", "OCTET-STREAM");
    part->charset = CHARSET_UNKNOWN_CHARSET;
    part->encoding = ENCODING_NONE;
}

static int add_field(segment_t *header,
		     field_desc_t *desc,
		     const char *start,
		     const char *head,
		     const char *colon,
		     const char *line,
		     struct buf *mime_fields)
{
    segment_t *field;
    int r = 0;

    field = segment_new(desc->id);
    segment_set_shape(field, header->offset + (head - start), line - head);
    segment_finish(field);
    segment_append(header, field);

    if (desc->id >= ID_MIME_FIRST && desc->id <= ID_MIME_LAST) {
	colon++;
	buf_init_ro(&mime_fields[desc->id - ID_MIME_FIRST],
		    colon, line - colon);
    }

    return r;
}

/*
 * A note about the ID_HEADER segment.  RFC5322 (Internet Message
 * Format) and RFC3501 (IMAPv4) disagree slightly about what a "header"
 * is.  In RFC5322 the empty line (i.e. the CRLF pair) immediately
 * following the last header field is neither in the header nor in the
 * body, so strictly speaking an RFC5322 header does not include a
 * trailing empty line.  In RFC3501 however, when the client asks for a
 * "HEADER" section, this must include a trailing empty line (except in
 * the corner case where the underlying message has no body and no empty
 * line).  For a number of reasons (most of them historical) we lean the
 * RFC3501 way and include the trailing empty line in ID_HEADER.  This
 * means that ID_HEADER and the following ID_BODY always abut precisely.
 */

static int message2_parse_header(part_t *part, const struct buf *map)
{
    segment_t *header;
    const char *start;	    /* start of header+body section */
    const char *end;	    /* end of header+body section */
    const char *head;	    /* start of first line of this header  */
    const char *line;	    /* start of this line */
    const char *colon;	    /* the ':' separating the name, if any */
    const char *crlf;	    /* CR+LF at end of this line */
    struct buf mime_fields[ID_MIME_LAST-ID_MIME_FIRST+1];
    field_desc_t *desc = NULL;
    int i;
    int r = IMAP_MESSAGE_BADHEADER;

    header = segment_find_child(to_segment(part), ID_HEADER);
    if (!header) {
	header = segment_new(ID_HEADER);
	segment_bud(to_segment(part), header);
    }
    segment_finish(header);

    memset(mime_fields, 0, sizeof(mime_fields));

    start = map->s;
    end = start + map->len;
    line = start;
    head = NULL;

    while (line < end) {

	if (end - line < 2) {
	    /* not enough room remains for a field */
	    goto out;
	}
	else if (line[0] == '\r' && line[1] == '\n') {
	    /* empty line: separates header and body */
	    break;
	}
	else if (isspace(*line)) {
	    /* continuation line */
	}
	else {
	    /* new header line */
	    if (desc) {
		/* previous field is complete */
		r = add_field(header, desc, start, head, colon, line, mime_fields);
		if (r) goto out;
		desc = NULL;
		head = NULL;
	    }
	    colon = memchr(line, ':', end-line);
	    if (!colon)
		goto next;  /* no colon */
	    /* TODO: walk 'colon' back over any whitespace */
	    if (colon == line)
		goto next;  /* zero length name */
	    if (colon-line > MAX_FIELDNAME_LENGTH)
		goto next;  /* name too long */
	    head = line;
	    desc = field_desc_get_byname(line, colon-line, /*create*/1);
	}

next:
	crlf = memchr(line, '\r', line-end);
	if (!crlf)
	    goto out;  /* no CR */
	if (crlf+2 >= end)
	    goto out;  /* no LF */
	line = crlf+2;
    }

    if (desc) {
	/* last field is complete */
	r = add_field(header, desc, start, head, colon, line, mime_fields);
	if (r) goto out;
    }

    if (line+2 < end) {
	/* a body follows; this is not always the case, especially
	 * when we're parsing cached header fields. */
	segment_t *body = segment_new(ID_BODY);
	segment_split_right(header, line+2 - start, body);
    }

    /* TODO: maintain a line count in each part!!! */

    handle_mime_fields(part, mime_fields);
    r = 0;

out:
    for (i = ID_MIME_FIRST ; i < ID_MIME_LAST ; i++)
	buf_free(&mime_fields[i - ID_MIME_FIRST]);
    return r;
}

static int message2_parse_multipart(part_t *part,
				    segment_t *body)
{
    const char *start;	    /* start of body section */
    const char *end;	    /* end of body section */
    const char *line;	    /* start of this line */
    const char *crlf;	    /* CR+LF at end of this line */
    const char *entstart;   /* start of the entity being parsed */
    int blen;		    /* length of boundary string */
    unsigned int next_partno = 1;
    int r;
    struct buf map = BUF_INITIALIZER;
    message_t *m = part->message;

    assert(part->boundary);
    blen = strlen(part->boundary);

    r = message2_map_segment(m, body, &map);
    if (r) return r;

    start = map.s;
    end = start + map.len;
    line = start;
    entstart = NULL;
    crlf = NULL;

    while (line < end) {

	if (end - line < blen+4) {
	    /* not enough room remains for a closing boundary */
	    break;
	}
	else if (line[0] == '-' && line[1] == '-') {
	    /* Potentially a boundary line.  Note that the nice thing
	     * about our top-down parsing model is that we already know
	     * the shape of the entity so we don't have to deal with
	     * possibility of seeing any boundary except our own.  */
	    int close = 0;
	    const char *p = line+2;
	    if (!memcmp(p, part->boundary, blen)) {
		p += blen;
		if (p[0] == '-' && p[1] == '-') {
		    p += 2;
		    close = 1;
		}
		/* skip any trailing Linear White Space */
		for ( ; p < end && (*p == ' ' || *p == '\t') ; p++)
		    ;
		/* boundary line must end with a CRLF or the end
		 * of the entity */
		if (p == end ||
		    ((end - p) >= 2 && p[0] == '\r' && p[1] == '\n')) {
		    /* ok we have a correctly formed boundary line */
		    if (entstart) {
			/* crlf points to the CRLF before the start of
			 * the boundary line, which is one after the
			 * last byte of the previous entity */
			segment_t *part = part_new(m, next_partno++);
			segment_set_shape(part,
					  body->offset + (entstart - start),
					  crlf - entstart);
			segment_append(body, part);
		    }
		    entstart = (p < end ? p+2 : NULL);
		    /* entstart points to the first byte of the next entity */
		    if (close)
			break;
		}
	    }
	}

	crlf = memchr(line, '\r', line-end);
	if (!crlf)
	    break;  /* no CR */
	if (crlf+2 >= end)
	    break;  /* no LF */
	if (crlf[1] != '\n')
	    break;  /* no LF */
	line = crlf+2;
    }

    /*
     * RFC2046 says:
     *
     * There appears to be room for additional information prior to the
     * first boundary delimiter line and following the final boundary
     * delimiter line.  These areas should generally be left blank, and
     * implementations must ignore anything that appears before the
     * first boundary delimiter line or after the last one.
     */

    return 0;
}

static int message2_map_file(message_t *m, const char *fname)
{
    int fd;
    struct stat sbuf;
    const char *base = NULL;
    size_t len = 0;

    fd = open(fname, O_RDONLY, 0666);
    if (fd == -1) return errno;

    if (fstat(fd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on %s: %m", fname);
	fatal("can't fstat message file", EC_OSFILE);
    }
    if (!S_ISREG(sbuf.st_mode)) {
	close(fd);
	return EINVAL;
    }
    buf_free(&m->map);
    map_refresh(fd, 1, &base, &len, sbuf.st_size, fname,
		(m->mailbox ? m->mailbox->name : NULL));
    if (!base || !len) {
	close(fd);
	return IMAP_IOERROR;
    }
    buf_init_mmap(&m->map, base, len);
    close(fd);

    return 0;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static void extract_one(struct buf *buf,
			const field_desc_t *desc,
			int format,
			int has_name,
			struct buf *raw)
{
    char *p = NULL;

    if (has_name && !(format & MESSAGE_FIELDNAME)) {
	/* remove the fieldname and colon */
	int pos = buf_findchar(raw, 0, ':');
	assert(pos > 0);
	buf_remove(raw, 0, pos+1);
    }
    else if (!has_name && (format & MESSAGE_FIELDNAME)) {
	/* insert a fieldname and colon */
	buf_insertcstr(raw, 0, ":");
	buf_insertcstr(raw, 0, desc->name);
    }

    if (!(format & MESSAGE_APPEND))
	buf_reset(buf);

    switch (format & _MESSAGE_FORMAT_MASK) {
    case MESSAGE_RAW:
	/* Logically, we're appending to the resulting buffer.
	 * However if the buf is empty we can save a memory copy
	 * by setting it up as a CoW buffer.  This means that
	 * the caller will need to call buf_cstring() if they
	 * need a C string. */
	if (!raw->alloc)
	    buf_cowappendmap(buf, raw->s, raw->len);
	else
	    buf_append(buf, raw);
	break;
    case MESSAGE_DECODED:
	p = charset_parse_mimeheader(buf_cstring(raw));
	buf_appendcstr(buf, p);
	break;
    case MESSAGE_SNIPPET:
	p = charset_decode_mimeheader(buf_cstring(raw), CHARSET_SNIPPET);
	buf_appendcstr(buf, p);
	break;
    case MESSAGE_SEARCH:
	/* TODO: need a variant of decode_mimeheader() which
	 * takes two struct buf* and a search flag */
	p = charset_decode_mimeheader(buf_cstring(raw), charset_flags);
	buf_appendcstr(buf, p);
	break;
    }

    free(p);
}

static int message_extract_field(message_t *m,
				 segment_t *part,
				 field_desc_t *desc,
				 int format,
				 struct buf *buf)
{
    int r = 0;
    struct buf raw = BUF_INITIALIZER;
    segment_t *s = NULL;
    const struct buf *map = NULL;

    if (!desc)
	return IMAP_NOTFOUND;

    assert(part == m->segs || is_finished(part));

    /* Note we don't check part->parent, that isn't right in the case
     * when we've been passed an unfinished root part */
    if (part == m->segs) {
	/* top-level header fields might be in the cyrus.cache */

	/* retrieve from cache entry if possible */
	if (desc->cache_idx >= 0) {
	    r = message_need(m, M_CACHE);
	    if (!r) {
		if (cacheitem_size(&m->record, desc->cache_idx))
		    buf_init_ro(&raw, cacheitem_base(&m->record, desc->cache_idx),
				      cacheitem_size(&m->record, desc->cache_idx));
		extract_one(buf, desc, format, /*has_name*/0, &raw);
		goto out;
	    }
	}

	/* retrieve from cached envelope if possible */
	if (desc->env_idx >= 0) {
	    assert(desc->env_idx < NUMENVTOKENS);
	    r = message_need(m, M_CENVELOPE);
	    if (!r) {
		buf_init_ro_cstr(&raw, m->envelope[desc->env_idx]);
		extract_one(buf, desc, format, /*has_name*/0, &raw);
		goto out;
	    }
	}

	/* retrieve from cached headers if possible */
	if (desc->min_cache_version != BIT32_MAX) {
	    r = message_need(m, M_CHEADER);
	    if (!r && desc->min_cache_version <= m->record.cache_version) {
		s = m->cheader_segs;
		map = &m->cheader_map;
	    }
	}
    }

    /* retrieve from full mapped file headers */
    if (!s) {
	r = message_need(m, M_SEGS);
	if (!r) {
	    s = is_finished(part) ? part : m->segs;
	    map = &m->map;
	}
    }

    r = IMAP_NOTFOUND;
    if (s) {
	s = segment_find_child(s, ID_HEADER);
	r = message2_expand_segment(m, s);
	if (r) goto out;
	r = IMAP_NOTFOUND;
	for (s = (s ? s->children : NULL) ; s ; s = s->next) {
	    if (s->id != (unsigned)desc->id)
		continue;
	    buf_init_ro(&raw, map->s + s->offset, s->length);
	    extract_one(buf, desc, format, /*has_name*/1, &raw);
	    buf_free(&raw);
	    r = 0;	/* found */
	    if (!(format & MESSAGE_MULTIPLE))
		break;
	}
    }

out:
    buf_free(&raw);
    return r;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static int part_extract_header(part_t *part,
			       int format,
			       struct buf *buf)
{
    segment_t *s;
    int r;
    struct buf raw = BUF_INITIALIZER;
    const char *p;

    r = message_need(part->message, M_SEGS);
    if (r) return r;

    s = segment_find_child(to_segment(part), ID_HEADER);
    if (!s) return IMAP_NOTFOUND;

    r = message2_map_segment(part->message, s, &raw);
    if (r) return r;

    if (!(format & MESSAGE_APPEND))
	buf_reset(buf);

    switch (format & _MESSAGE_FORMAT_MASK) {
    case MESSAGE_RAW:
	/* Logically, we're appending to the resulting buffer.
	 * However if the buf is empty we can save a memory copy
	 * by setting it up as a CoW buffer.  This means that
	 * the caller will need to call buf_cstring() if they
	 * need a C string. */
	if (!raw.alloc)
	    buf_cowappendmap(buf, raw.s, raw.len);
	else
	    buf_append(buf, &raw);
	break;
    case MESSAGE_DECODED:
	p = charset_parse_mimeheader(buf_cstring(&raw));
	buf_appendcstr(buf, p);
	break;
    case MESSAGE_SEARCH:
	/* TODO: need a variant of decode_mimeheader() which
	 * takes two struct buf* and a search flag */
	p = charset_decode_mimeheader(buf_cstring(&raw), charset_flags);
	buf_appendcstr(buf, p);
	break;
    }

    buf_free(&raw);
    return r;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

static int part_extract_body(part_t *part,
			     int format,
			     struct buf *buf)
{
    segment_t *s;
    int r;
    struct buf raw = BUF_INITIALIZER;
    const char *p;
    char *decbuf = NULL;
    size_t declen = 0;

    r = message_need(part->message, M_SEGS);
    if (r) return r;

    s = segment_find_child(to_segment(part), ID_BODY);
    if (!s) return IMAP_NOTFOUND;

    r = message2_map_segment(part->message, s, &raw);
    if (r) return r;

    if (!(format & MESSAGE_APPEND))
	buf_reset(buf);

    switch (format & _MESSAGE_FORMAT_MASK) {
    case MESSAGE_RAW:
	/* Logically, we're appending to the resulting buffer.
	 * However if the buf is empty we can save a memory copy
	 * by setting it up as a CoW buffer.  This means that
	 * the caller will need to call buf_cstring() if they
	 * need a C string. */
	buf_cowappendmap(buf, raw.s, raw.len);
	break;
    case MESSAGE_DECODED:
    case MESSAGE_SEARCH:
	/* TODO: should push the append-to-a-buf semantics
	 * down into charset_decode_mimebody instead of having
	 * to deal with the interface mismatch here */
	p = charset_decode_mimebody(raw.s, raw.len,
				    part->encoding,
				    &decbuf, &declen);
	if (p == raw.s) {
	    /* trivial encoding */
	    buf_cowappendmap(buf, raw.s, raw.len);
	}
	else {
	    /* nontrivial encoding: newly allocated result in decbuf */
	    buf_cowappendfree(buf, decbuf, declen);
	}
	break;
    }

    buf_free(&raw);
    return r;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

EXPORTED int part_get_field(part_t *part, const char *name,
			    int format, struct buf *buf)
{
    return message_extract_field(part->message, to_segment(part),
				 field_desc_get_byname(name, 0, /*create*/0),
				 format, buf);
}

EXPORTED int part_get_header(part_t *part, int format, struct buf *buf)
{
    return part_extract_header(part, format, buf);
}

EXPORTED int part_get_body(part_t *part, int format, struct buf *buf)
{
    return part_extract_body(part, format, buf);
}

EXPORTED int part_get_type(part_t *part, const char **strp)
{
    int r = message_need(part->message, M_BODY);
    if (r) return r;
    /* we need to have parsed the header to report type */
    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;
    *strp = part->type;
    return 0;
}

EXPORTED int part_get_subtype(part_t *part, const char **strp)
{
    int r = message_need(part->message, M_BODY);
    if (r) return r;
    /* we need to have parsed the header to report subtype */
    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;
    *strp = part->subtype;
    return 0;
}

EXPORTED int part_get_charset(part_t *part, int *csp)
{
    int r;
    /* we need to have parsed the header to report charset */
    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;
    *csp = part->charset;
    return 0;
}

EXPORTED int part_get_encoding(part_t *part, int *encp)
{
    int r;
    /* we need to have parsed the header to report encoding */
    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;
    *encp = part->encoding;
    return 0;
}

EXPORTED int part_get_num_parts(part_t *part, unsigned int *np)
{
    segment_t *s;
    int r;

    r = message_need(part->message, M_SEGS);
    if (r) return r;

    s = segment_find_child(to_segment(part), ID_BODY);
    if (!s) return IMAP_NOTFOUND;

    r = message2_expand_segment(part->message, s);
    if (r) return r;
    *np = segment_get_num_children(s);
    return 0;
}

EXPORTED int part_get_part(part_t *part, unsigned int id, part_t **childp)
{
    segment_t *s;
    int r;

    r = message_need(part->message, M_SEGS);
    if (r) return r;

    s = segment_find_child(to_segment(part), ID_BODY);
    if (!s) return IMAP_NOTFOUND;

    r = message2_expand_segment(part->message, s);
    if (r) return r;
    *childp = get_part(segment_find_child(s, T_PART|id));
    return (*childp ? 0 : IMAP_NOTFOUND);
}

static int part_foreach_text_section(part_t *part,
				     int (*proc)(int partno, int charset,
						 int encoding, const char *subtype,
						 struct buf *data, void *rock),
				     void *rock)
{
    segment_t *header;
    segment_t *body;
    segment_t *s;
    struct buf data = BUF_INITIALIZER;
    int r;

    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;

    header = segment_find_child(to_segment(part), ID_HEADER);
    if (header) {
	buf_init_ro(&data, part->message->map.s + header->offset, header->length);
	r = proc(0, 0, ENCODING_NONE, NULL, &data, rock);
	buf_free(&data);
	if (r) return r;
    }

    body = segment_find_child(to_segment(part), ID_BODY);
    if (body) {
	r = message2_expand_segment(part->message, body);
	if (r) return r;

	if (!strcmpsafe(part->type, "TEXT")) {
	    buf_init_ro(&data, part->message->map.s + body->offset, body->length);
	    r = proc(part->super.id & ID_MASK,
		     part->charset, part->encoding, part->subtype,
		     &data, rock);
	    buf_free(&data);
	    if (r) return r;
	}
	for (s = body->children ; s ; s = s->next) {
	    r = part_foreach_text_section(get_part(s), proc, rock);
	    if (r) return r;
	}
    }

    return 0;
}

static int part_get_leaf_types(part_t *part, strarray_t *types)
{
    segment_t *body;
    segment_t *s;
    int r;

    r = message2_expand_segment(part->message, to_segment(part));
    if (r) return r;

    body = segment_find_child(to_segment(part), ID_BODY);
    if (body) {
	r = message2_expand_segment(part->message, body);
	if (r) return r;

	if (strcmpsafe(part->type, "MULTIPART") &&
	    strcmpsafe(part->type, "MESSAGE")) {
	    strarray_append(types, part->type);
	    strarray_append(types, part->subtype);
	}
	for (s = body->children ; s ; s = s->next) {
	    r = part_get_leaf_types(get_part(s), types);
	    if (r) return r;
	}
    }

    return 0;
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

/*
 * Retrieve a single header field named 'name' from the message
 * 'message' and append it's value to 'buf'.  In general, the result in
 * 'buf' may be CoW so the caller should use buf_cstring() before
 * assuming that there is a NUL terminator.  The 'format' argument is
 * flags from enum message_format which control how the result is
 * formatted.  Returns zero on success, or an IMAP error number.
 */
EXPORTED int message_get_field(message_t *m, const char *name,
			       int format, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byname(name, 0, /*create*/1),
				 format, buf);
}

EXPORTED int message_get_header(message_t *m, int format, struct buf *buf)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_extract_header(get_part(m->segs), format, buf);
}

EXPORTED int message_get_body(message_t *m, int format, struct buf *buf)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_extract_body(get_part(m->segs), format, buf);
}

EXPORTED int message_get_type(message_t *m, const char **strp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_type(get_part(m->segs), strp);
}

EXPORTED int message_get_subtype(message_t *m, const char **strp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_subtype(get_part(m->segs), strp);
}

EXPORTED int message_get_charset(message_t *m, int *csp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_charset(get_part(m->segs), csp);
}

EXPORTED int message_get_encoding(message_t *m, int *encp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_encoding(get_part(m->segs), encp);
}

/* TODO: add message_get_parts(message_t *, ptrarray_t *); */

EXPORTED int message_get_num_parts(message_t *m, unsigned int *np)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_num_parts(get_part(m->segs), np);
}

EXPORTED int message_get_part(message_t *m, unsigned int id, part_t **partp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    return part_get_part(get_part(m->segs), id, partp);
}

EXPORTED int message_get_root_part(message_t *m, part_t **partp)
{
    int r = message_need(m, M_SEGS);
    if (r) return r;
    *partp = get_part(m->segs);
    return 0;
}

EXPORTED int message_get_messageid(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_MESSAGE_ID),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_listid(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_LIST_ID),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_mailinglist(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_MAILING_LIST),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_from(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_FROM),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_to(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_TO),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_bcc(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_BCC),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_cc(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_CC),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_inreplyto(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_IN_REPLY_TO),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_references(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_REFERENCES),
				 MESSAGE_RAW, buf);
}

EXPORTED int message_get_subject(message_t *m, struct buf *buf)
{
    return message_extract_field(m, m->segs,
				 field_desc_get_byid(ID_SUBJECT),
				 MESSAGE_DECODED, buf);
}

EXPORTED int message_get_date(message_t *m, time_t *tp)
{
    struct buf buf = BUF_INITIALIZER;
    int r = 0;

    r = message_extract_field(m, m->segs,
			      field_desc_get_byid(ID_DATE),
			      MESSAGE_RAW, &buf);
    if (r) return r;
    r = time_from_rfc822(buf_cstring(&buf), tp);
    if (r < 0) r = -EINVAL;
    buf_free(&buf);
    return r;
}

EXPORTED int message_get_mailbox(message_t *m, struct mailbox **mailboxp)
{
    int r = message_need(m, M_MAILBOX);
    if (r) return r;
    *mailboxp = m->mailbox;
    return 0;
}

EXPORTED int message_get_uid(message_t *m, uint32_t *uidp)
{
    int r = message_need(m, M_UID);
    if (r) return r;
    *uidp = m->record.uid;
    return 0;
}

EXPORTED int message_get_cid(message_t *m, conversation_id_t *cidp)
{
    int r = message_need(m, M_RECORD);
    if (r) return r;
    *cidp = m->record.cid;
    return 0;
}

EXPORTED int message_get_internaldate(message_t *m, time_t *tp)
{
    int r = message_need(m, M_RECORD);
    if (r) return r;
    *tp = m->record.internaldate;
/* TODO: as fallback, extract from header fields */
    return 0;
}

EXPORTED int message_get_sentdate(message_t *m, time_t *tp)
{
    int r = message_need(m, M_RECORD);
    if (r) return r;
    *tp = m->record.sentdate;
/* TODO: as fallback, extract from header fields */
    return 0;
}

EXPORTED int message_get_modseq(message_t *m, modseq_t *modseqp)
{
    int r = message_need(m, M_RECORD);
    if (r) return r;
    *modseqp = m->record.modseq;
    return 0;
}

EXPORTED int message_get_systemflags(message_t *m, uint32_t *flagsp)
{
    int r = message_need(m, M_RECORD);
    if (r) return r;
    *flagsp = m->record.system_flags;
    return 0;
}

EXPORTED int message_get_indexflags(message_t *m, uint32_t *flagsp)
{
    int r = message_need(m, M_INDEX);
    if (r) return r;
    *flagsp = m->indexflags;
    return 0;
}

EXPORTED int message_get_userflags(message_t *m, uint32_t *flagsp)
{
    int i;
    int r = message_need(m, M_RECORD);
    if (r) return r;
    for (i = 0; i < MAX_USER_FLAGS/32; i++)
	flagsp[i] = m->record.user_flags[i];
    return 0;
}

EXPORTED int message_get_size(message_t *m, uint32_t *sizep)
{
    if (!message_need(m, M_RECORD)) {
	*sizep = m->record.size;
	return 0;
    }
    if (!message_need(m, M_SEGS)) {
	*sizep = m->segs->length;
	return 0;
    }
    return IMAP_NOTFOUND;
}

EXPORTED int message_get_msgno(message_t *m, uint32_t *msgnop)
{
    int r = message_need(m, M_INDEX);
    if (r) return r;
    *msgnop = m->msgno;
    return 0;
}

/*
 * Iterate 'proc' over all the MIME header sections and body sections of
 * type TEXT, in the message 'm', preorder.  The 'proc' is called with
 * 'partno' equal to zero for header sections, non-zero for body
 * sections.  If 'proc' returns non-zero, the iteration finishes early
 * and the return value of 'proc' is returned.  Otherwise returns 0.
 */
EXPORTED int message_foreach_text_section(message_t *m,
			 int (*proc)(int partno, int charset,
				     int encoding, const char *subtype,
				     struct buf *data, void *rock),
			 void *rock)
{
    int r = message_need(m, M_SEGS|M_BODY|M_MAP);
    if (r) return r;
    return part_foreach_text_section(get_part(m->segs), proc, rock);
}

/*
 * Get the MIME content types of all leaf sections, i.e. sections whose
 * type is not multipart or message.  Strings are added to the array in
 * pairs, type first then subtype.
 */
EXPORTED int message_get_leaf_types(message_t *m, strarray_t *types)
{
    int r = message_need(m, M_SEGS|M_BODY|M_MAP);
    if (r) return r;
    return part_get_leaf_types(get_part(m->segs), types);
}

/*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/
