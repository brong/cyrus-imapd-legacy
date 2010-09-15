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
 *
 * $Id: message.c,v 1.118 2010/06/28 12:04:38 brong Exp $
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

#include "exitcodes.h"
#include "imap_err.h"
#include "prot.h"
#include "map.h"
#include "mailbox.h"
#include "message.h"
#include "message_guid.h"
#include "parseaddr.h"
#include "charset.h"
#include "stristr.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "global.h"
#include "retry.h"

/* Message being parsed */
struct msg {
    const char *base;
    unsigned long len;
    unsigned long offset;
    int encode;
};

/* cyrus.cache file item buffer */
struct ibuf {
    char *start, *end, *last;
};
    
/*
 * Parsed form of a body-part
 */
struct body {
    /* Content-* header information */
    char *type;
    char *subtype;
    struct param *params;
    char *id;
    char *description;
    char *encoding;
    char *md5;
    char *disposition;
    struct param *disposition_params;
    struct param *language;
    char *location;

    /* Location/size information */
    long header_offset;
    long header_size;
    long header_lines;
    long content_offset;
    long content_size;
    long content_lines;
    long boundary_size;		/* Size of terminating boundary */
    long boundary_lines;

    int numparts;		/* For multipart types */
    struct body *subpart;	/* For message/rfc822 and multipart types */

    /*
     * Other header information.
     * Only meaningful for body-parts at top level or
     * enclosed in message/rfc-822
     */
    char *date;
    char *subject;
    struct address *from;
    struct address *sender;
    struct address *reply_to;
    struct address *to;
    struct address *cc;
    struct address *bcc;
    char *in_reply_to;
    char *message_id;

    /*
     * Cached headers.  Only filled in at top-level
     */
    struct ibuf cacheheaders;

    /*
     * decoded body.  Filled in as needed.
     */
    char *decoded_body;

    /* Message GUID. Only filled in at top level */
    struct message_guid guid;
};

/* List of Content-type parameters */
struct param {
    struct param *next;
    char *attribute;
    char *value;
};

/* List of pending multipart boundaries */
struct boundary {
    char **id;
    int count;
    int alloc;
};

/* (draft standard) MIME tspecials */
#define TSPECIALS "()<>@,;:\\\"/[]?="

/* Default MIME Content-type */
#define DEFAULT_CONTENT_TYPE "TEXT/PLAIN; CHARSET=us-ascii"

static int message_parse_mapped P((const char *msg_base, unsigned long msg_len,
				   struct body *body));
static int message_parse_body P((struct msg *msg,
				 int format, struct body *body,
				 char *defaultContentType,
				 struct boundary *boundaries));

static int message_parse_headers P((struct msg *msg,
				    int format, struct body *body,
				    char *defaultContentType,
				    struct boundary *boundaries));
static void message_parse_address P((char *hdr, struct address **addrp));
static void message_parse_encoding P((char *hdr, char **hdrp));
static void message_parse_charset P((struct body *body, int *encoding, int *charset));
static void message_parse_string P((char *hdr, char **hdrp));
static void message_parse_header P((char *hdr, struct ibuf *ibuf));
static void message_parse_type P((char *hdr, struct body *body));
/* static */ void message_parse_disposition P((char *hdr, struct body *body));
static void message_parse_params P((char *hdr, struct param **paramp));
static void message_fold_params P((struct param **paramp));
static void message_parse_language P((char *hdr, struct param **paramp));
static void message_parse_rfc822space P((char **s));

static void message_parse_multipart P((struct msg *msg,
				       int format, struct body *body,
				       struct boundary *boundaries));
static void message_parse_content P((struct msg *msg,
				     int format, struct body *body,
				     struct boundary *boundaries));

static char *message_getline P((char *s, unsigned n, struct msg *msg));
static int message_pendingboundary P((const char *s, char **boundaries,
				      int *boundaryct));

static int message_write_cache P((int outfd, struct body *body));

static void message_write_envelope P((struct ibuf *ibuf, struct body *body));
static void message_write_body P((struct ibuf *ibuf, struct body *body,
				  int newformat));
static void message_write_address P((struct ibuf *ibuf,
				     struct address *addrlist));
static void message_write_nstring P((struct ibuf *ibuf, char *s));
static void message_write_text P((struct ibuf *ibuf, char *s));
static void message_write_text_lcase P((struct ibuf *ibuf, char *s));
static void message_write_number P((struct ibuf *ibuf, unsigned n));
static void message_write_section P((struct ibuf *ibuf, struct body *body));
static void message_write_charset P((struct ibuf *ibuf, struct body *body));
static void message_write_bit32 P((struct ibuf *ibuf, bit32 val));
static void message_write_searchaddr P((struct ibuf *ibuf,
					struct address *addrlist));

static void message_ibuf_init P((struct ibuf *ibuf));
static int message_ibuf_ensure P((struct ibuf *ibuf, unsigned len));
static void message_ibuf_iov P((struct iovec *iov, struct ibuf *ibuf));
static void message_ibuf_free P((struct ibuf *ibuf));

/*
 * Copy a message of 'size' bytes from 'from' to 'to',
 * ensuring minimal RFC-822 compliance.
 *
 * Caller must have initialized config_* routines (with cyrus_init) to read
 * imapd.conf before calling.
 */
int
message_copy_strict(from, to, size, allow_null)
struct protstream *from;
FILE *to;
unsigned size;
int allow_null;
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

/*
 * Parse the message 'infile'.
 *
 * The caller MUST free the allocated body struct.
 *
 * If msg_base/msg_len are non-NULL, the file will remain memory-mapped
 * and returned to the caller.  The caller MUST unmap the file.
 */
int message_parse_file(FILE *infile,
		       const char **msg_base, unsigned long *msg_len,
		       struct body **body)
{
    int fd = fileno(infile);
    struct stat sbuf;
    const char *tmp_base;
    unsigned long tmp_len;
    int unmap = 0, r;

    if (!msg_base) {
	unmap = 1;
	msg_base = &tmp_base;
	msg_len = &tmp_len;
    }
    *msg_base = 0;
    *msg_len = 0;

    if (fstat(fd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on new message in spool: %m");
	fatal("can't fstat message file", EC_OSFILE);
    }
    map_refresh(fd, 1, msg_base, msg_len, sbuf.st_size,
		"new message", 0);

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
int message_parse_binary_file(FILE *infile, struct body **body)
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
    message_parse_body(&msg, MAILBOX_FORMAT_NORMAL, *body,
		       DEFAULT_CONTENT_TYPE, (struct boundary *)0);

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
int message_parse_mapped(const char *msg_base, unsigned long msg_len,
			 struct body *body)
{
    struct msg msg;

    msg.base = msg_base;
    msg.len = msg_len;
    msg.offset = 0;
    msg.encode = 0;

    message_parse_body(&msg, MAILBOX_FORMAT_NORMAL, body,
		       DEFAULT_CONTENT_TYPE, (struct boundary *)0);

    message_guid_generate(&body->guid, msg_base, msg_len);

    return 0;
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
void message_fetch_part(struct message_content *msg,
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
 * by 'message_index'.
 */
int
message_create_record(cache_name, cache_fd, message_index, body)
const char *cache_name;
int cache_fd;
struct index_record *message_index;
struct body *body;
{
    int n;
    enum enum_value config_guidmode = config_getenum(IMAPOPT_GUID_MODE);

    message_index->sentdate = message_parse_date(body->date, 0);
    message_index->size = body->header_size + body->content_size;
    message_index->header_size = body->header_size;
    message_index->content_offset = body->content_offset;
    message_index->content_lines = body->content_lines;

    message_index->cache_offset = lseek(cache_fd, 0, SEEK_CUR);

    message_index->cache_version = MAILBOX_CACHE_MINOR_VERSION;

    n = message_write_cache(cache_fd, body);

    if (n == -1) {
	syslog(LOG_ERR, "IOERROR: appending cache for %s: %m", cache_name);
	return IMAP_IOERROR;
    }

    /* Copy in GUID unless GUID already assigned to the message
     * (allows parent to decide which source of GUIDs to use)
     */
    if (config_guidmode && message_guid_isnull(&message_index->guid)) {
	message_guid_copy(&message_index->guid, &body->guid);
    }

    return 0;
}

/*
 * Parse a body-part
 */
static int
message_parse_body(msg, format, body, defaultContentType, boundaries)
struct msg *msg;
int format;
struct body *body;
char *defaultContentType;
struct boundary *boundaries;
{
    struct boundary newboundaries;
    int sawboundary;

    memset(body, 0, sizeof(struct body));
    newboundaries.id = 0;

    /* No passed-in boundary structure, create a new, empty one */
    if (!boundaries) {
	boundaries = &newboundaries;
	boundaries->alloc = boundaries->count = 0;
	/* We're at top-level--set up to store cached headers */
	message_ibuf_init(&body->cacheheaders);
    }

    sawboundary = message_parse_headers(msg, format, body, defaultContentType,
					boundaries);

    /* Recurse according to type */
    if (strcmp(body->type, "MULTIPART") == 0) {
	if (!sawboundary) {
	    message_parse_multipart(msg, format, body, boundaries);
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
	    message_parse_body(msg, format, body->subpart,
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
	    message_parse_content(msg, format, body, boundaries);
	}
    }

    /* Free up boundary storage if necessary */
    if (newboundaries.id) free(newboundaries.id);

    return 0;
}

/*
 * Parse the headers of a body-part
 */
#define HEADGROWSIZE 1000
static int
message_parse_headers(msg, format, body, defaultContentType,
		      boundaries)
struct msg *msg;
int format __attribute__((unused));
struct body *body;
char *defaultContentType;
struct boundary *boundaries;
{
    static int alloced = 0;
    static char *headers;
    int left, len;
    char *next;
    int sawboundary = 0;
    int maxlines = config_getint(IMAPOPT_MAXHEADERLINES);
    int have_max = 0;

    body->header_offset = msg->offset;

    if (!alloced) {
	headers = xmalloc(alloced = HEADGROWSIZE);
    }

    next = headers;
    *next++ = '\n';		/* Leading newline to prime the pump */
    left = alloced - 3;		/* Allow for leading newline, added CR */
				/*  and trailing NUL */

    /* Slurp up all of the headers into 'headers' */
    while (message_getline(next, left, msg) &&
	   (next[-1] != '\n' ||
	    (*next != '\r' || next[1] != '\n'))) {

	if (next[-1] == '\n' && *next == '-' &&
	    message_pendingboundary(next, boundaries->id, &boundaries->count)) {
	    body->boundary_size = strlen(next);
	    body->boundary_lines++;
	    if (next - 1 > headers) {
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

	len = strlen(next);
	left -= len;
	next += len;

	/* Allocate more header space if necessary */
	if (left < 100) {
	    len = next - headers;
	    alloced += HEADGROWSIZE;
	    left += HEADGROWSIZE;
	    headers = xrealloc(headers, alloced);
	    next = headers + len;
	}
    }

    body->content_offset = msg->offset;
    body->header_size = strlen(headers+1);

    /* Scan over the slurped-up headers for interesting header information */
    body->header_lines = -1;	/* Correct for leading newline */
    for (next = headers; *next; next++) {
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

	    /* Check for headers in generic cache */
	    if (body->cacheheaders.start &&
		(next[1] != ' ') && (next[1] != '\t') &&
		mailbox_cached_header_inline(next+1) != BIT32_MAX) {
		    message_parse_header(next+1, &body->cacheheaders);
	    }

	    switch (next[1]) {
	    case 'b':
	    case 'B':
		if (!strncasecmp(next+2, "cc:", 3)) {
		    message_parse_address(next+5, &body->bcc);
		}
		break;
		
	    case 'c':
	    case 'C':
		if (!strncasecmp(next+2, "c:", 2)) {
		    message_parse_address(next+4, &body->cc);
		}
		if (!strncasecmp(next+2, "ontent-", 7)) {
		    switch (next[9]) {
		    case 'd':
		    case 'D':
			if (!strncasecmp(next+10, "escription:", 11)) {
			    message_parse_string(next+21, &body->description);
			}
			else if (!strncasecmp(next+10, "isposition:", 11)) {
			    message_parse_disposition(next+21, body);
			}
			break;

		    case 'i':
		    case 'I':
			if (!strncasecmp(next+10, "d:", 2)) {
			    message_parse_string(next+12, &body->id);
			}
			break;

		    case 'l':
		    case 'L':
			if (!strncasecmp(next+10, "anguage:", 8)) {
			    message_parse_language(next+18, &body->language);
			}
			else if (!strncasecmp(next+10, "ocation:", 8)) {
			    message_parse_string(next+18, &body->location);
			}
			break;

		    case 'm':
		    case 'M':
			if (!strncasecmp(next+10, "d5:", 3)) {
			    message_parse_string(next+13, &body->md5);
			}
			break;

		    case 't':
		    case 'T':
			if (!strncasecmp(next+10, "ransfer-encoding:", 17)) {
			    message_parse_encoding(next+27, &body->encoding);

			    /* If we're encoding binary, replace "binary"
			       with "base64" in CTE header body */
			    if (msg->encode &&
				!strcmp(body->encoding, "BINARY")) {
				char *p = (char*)
				    stristr(msg->base + body->header_offset +
					    (next - headers) + 27,
					    "binary");
				memcpy(p, "base64", 6);
			    }
			}
			else if (!strncasecmp(next+10, "ype:", 4)) {
			    message_parse_type(next+14, body);
			}
			break;
		    }
		}
		break;

	    case 'd':
	    case 'D':
		if (!strncasecmp(next+2, "ate:", 4)) {
		    message_parse_string(next+6, &body->date);
		}
		break;

	    case 'f':
	    case 'F':
		if (!strncasecmp(next+2, "rom:", 4)) {
		    message_parse_address(next+6, &body->from);
		}
		break;

	    case 'i':
	    case 'I':
		if (!strncasecmp(next+2, "n-reply-to:", 11)) {
		    message_parse_string(next+13, &body->in_reply_to);
		}
		break;

	    case 'm':
	    case 'M':
		if (!strncasecmp(next+2, "essage-id:", 10)) {
		    message_parse_string(next+12, &body->message_id);
		}
		break;

	    case 'r':
	    case 'R':
		if (!strncasecmp(next+2, "eply-to:", 8)) {
		    message_parse_address(next+10, &body->reply_to);
		}

		break;

	    case 's':
	    case 'S':
		if (!strncasecmp(next+2, "ubject:", 7)) {
		    message_parse_string(next+9, &body->subject);
		}
		if (!strncasecmp(next+2, "ender:", 6)) {
		    message_parse_address(next+8, &body->sender);
		}
		break;

	    case 't':
	    case 'T':
		if (!strncasecmp(next+2, "o:", 2)) {
		    message_parse_address(next+4, &body->to);
		}
		break;
	    } /* switch(next[1]) */
	} /* if (*next == '\n') */
    }

    /* If didn't find Content-Type: header, use the passed-in default type */
    if (!body->type) {
	message_parse_type(defaultContentType, body);
    }
    return sawboundary;
}

/*
 * Parse a list of RFC-822 addresses from a header, appending them
 * to the address list pointed to by 'addrp'.
 */
static void
message_parse_address(hdr, addrp)
char *hdr;
struct address **addrp;
{
    char *hdrend, hdrendchar = '\0';

    /* Find end of header */
    hdrend = hdr;
    do {
	hdrend = strchr(hdrend+1, '\n');
    } while (hdrend && (hdrend[1] == ' ' || hdrend[1] == '\t'));

    /* Put a NUL character at the end of header */
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
static void
message_parse_encoding(hdr, hdrp)
char *hdr;
char **hdrp;
{
    int len;
    char *p;

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
    *hdrp = xmalloc(len + 1);
    strlcpy(*hdrp, hdr, len + 1);
    for (p = *hdrp; *p; p++) {
	if (Uislower(*p)) *p = toupper((int) *p);
    }
}

/* 
 * parse a charset and encoding out of a body structure
 */
static void
message_parse_charset(struct body *body, int *e_ptr, int *c_ptr)
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
static void
message_parse_string(hdr, hdrp)
char *hdr;
char **hdrp;
{
    int len;
    char *hdrend;

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
    len = hdrend - hdr;
    *hdrp = xmalloc(len + 1);
    strlcpy(*hdrp, hdr, len + 1);

    /* Un-fold header (overlapping buffers, use memmove) */
    hdrend = *hdrp;
    while ((hdrend = strchr(hdrend, '\n'))!=NULL) {
	if (hdrend > *hdrp && hdrend[-1] == '\r') {
	    hdrend--;
	    memmove(hdrend, hdrend+2, strlen(hdrend+2)+1);
	}
	else {
	    memmove(hdrend, hdrend+1, strlen(hdrend+1)+1);
	}
    }
}

/*
 * Cache a header
 */
static void
message_parse_header(hdr, ibuf)
char *hdr;
struct ibuf *ibuf;
{
    int len;
    char *hdrend;

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
    message_ibuf_ensure(ibuf, len+2);
    strncpy(ibuf->end, hdr, len);
    ibuf->end += len;
    *(ibuf->end)++ = '\r';
    *(ibuf->end)++ = '\n';
}

/*
 * Parse a Content-Type from a header.
 */
static void
message_parse_type(hdr, body)	    
char *hdr;
struct body *body;
{
    char *type;
    int typelen;
    char *subtype;
    int subtypelen;
    char *p;

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
    body->type = xmalloc(typelen + 1);
    strlcpy(body->type, type, typelen + 1);
    for (p = body->type; *p; p++) {
	if (Uislower(*p)) *p = toupper((int) *p);
    }
    body->subtype = xmalloc(subtypelen + 1);
    strlcpy(body->subtype, subtype, subtypelen + 1);
    for (p = body->subtype; *p; p++) {
	if (Uislower(*p)) *p = toupper((int) *p);
    }

    /* Parse parameter list */
    if (hdr) {
	message_parse_params(hdr+1, &body->params);
	message_fold_params(&body->params);
    }
}

/*
 * Parse a Content-Disposition from a header.
 */
/* static */ void
message_parse_disposition(hdr, body)	    
char *hdr;
struct body *body;
{
    char *disposition;
    int dispositionlen;
    char *p;

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
    body->disposition = xmalloc(dispositionlen + 1);
    strlcpy(body->disposition, disposition, dispositionlen + 1);

    for (p = body->disposition; *p; p++) {
	if (Uislower(*p)) *p = toupper((int) *p);
    }

    /* Parse parameter list */
    if (hdr) {
	message_parse_params(hdr+1, &body->disposition_params);
	message_fold_params(&body->disposition_params);
    }
}

/*
 * Parse a parameter list from a header
 */
static void
message_parse_params(hdr, paramp)
char *hdr;
struct param **paramp;
{
    struct param *param;
    char *attribute;
    int attributelen;
    char *value;
    int valuelen;
    char *p;

    for (;;) {
	/* Skip over leading whitespace */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Find end of attribute */
	attribute = hdr;
	for (; *hdr && !Uisspace(*hdr) && *hdr != '=' && *hdr != '('; hdr++) {
	    if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) return;
	}
	attributelen = hdr - attribute;

	/* Skip whitespace after attribute */
	message_parse_rfc822space(&hdr);
	if (!hdr) return;

	/* Ignore param if no '=' character */
	if (*hdr++ != '=') return;

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
		    if (hdr[1] == '\n' && (hdr[2] == ' ' || hdr[2] == '\t')) hdr += 2;
 		    else return;
		}
		hdr++;
	    }
	    if (!*hdr++) return;
	}
	else {
	    for (; *hdr && !Uisspace(*hdr) && *hdr != ';' && *hdr != '('; hdr++) {
		if (*hdr < ' ' || strchr(TSPECIALS, *hdr)) return;
	    }
	}
	valuelen = hdr - value;

	/* Skip whitespace after value */
	message_parse_rfc822space(&hdr);

	/* Ignore parameter if not at end of header or parameter delimiter */
	if (hdr && *hdr++ != ';') return;
		  
	/* Save attribute/value pair */
	*paramp = param = (struct param *)xmalloc(sizeof(struct param));
	memset(param, 0, sizeof(struct param));
	param->attribute = xmalloc(attributelen + 1);
	strlcpy(param->attribute, attribute, attributelen + 1);

	for (p = param->attribute; *p; p++) {
	    if (Uislower(*p)) *p = toupper((int) *p);
	}
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

/* Alphabet for hex encoding */
static char basis_hex[] = "0123456789ABCDEF";

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
static void
message_fold_params(struct param **params)
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
				*to++ = basis_hex[(*from>>4) & 0xf];
				*to++ = basis_hex[*from & 0xf];
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
				*to++ = basis_hex[(*from>>4) & 0xf];
				*to++ = basis_hex[*from & 0xf];
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
static void
message_parse_language(hdr, paramp)
char *hdr;
struct param **paramp;
{
    struct param *param;
    char *value;
    int valuelen;
    char *p;

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
	*paramp = param = (struct param *)xmalloc(sizeof(struct param));
	memset(param, 0, sizeof(struct param));
	param->value = xmalloc(valuelen + 1);
	strlcpy(param->value, value, valuelen + 1);

	for (p = param->value; *p; p++) {
	    if (Uislower(*p)) *p = toupper((int) *p);
	}

	/* Get ready to parse the next parameter */
	paramp = &param->next;
    }
}

/*
 * Parse a RFC-822 date from a header.
 * Only parses to day granularity--ignores the time of day.
 */
time_t
message_parse_date(hdr, flags)
char *hdr;
unsigned flags;
{
    struct tm tm;
    time_t t;
    char month[4];
    static char *monthname[] = {
	"jan", "feb", "mar", "apr", "may", "jun",
	"jul", "aug", "sep", "oct", "nov", "dec"
    };
    int zone_off = 0;

    if (!hdr) goto baddate;

    memset(&tm, 0, sizeof(tm));

    message_parse_rfc822space(&hdr);
    if (!hdr) goto baddate;

    if (Uisalpha(*hdr)) {
	/* Day name -- skip over it */
	hdr++;
	if (!Uisalpha(*hdr)) goto baddate;
	hdr++;
	if (!Uisalpha(*hdr)) goto baddate;
	hdr++;
	message_parse_rfc822space(&hdr);
	if (!hdr || *hdr++ != ',') goto baddate;
	message_parse_rfc822space(&hdr);
	if (!hdr) goto baddate;
    }

    if (!Uisdigit(*hdr)) goto baddate;
    tm.tm_mday = *hdr++ - '0';
    if (Uisdigit(*hdr)) {
	tm.tm_mday = tm.tm_mday*10 + *hdr++ - '0';
    }
    
    /* Parse month name */
    message_parse_rfc822space(&hdr);
    if (!hdr) goto baddate;
    month[0] = *hdr++;
    if (!Uisalpha(month[0])) goto baddate;
    month[1] = *hdr++;
    if (!Uisalpha(month[1])) goto baddate;
    month[2] = *hdr++;
    if (!Uisalpha(month[2])) goto baddate;
    month[3] = '\0';
    lcase(month);
    for (tm.tm_mon = 0; tm.tm_mon < 12; tm.tm_mon++) {
	if (!strcmp(month, monthname[tm.tm_mon])) break;
    }
    if (tm.tm_mon == 12) goto baddate;
    
    /* Parse year */
    message_parse_rfc822space(&hdr);
    if (!hdr || !Uisdigit(*hdr)) goto baddate;
    tm.tm_year = *hdr++ - '0';
    if (!Uisdigit(*hdr)) goto baddate;
    tm.tm_year = tm.tm_year * 10 + *hdr++ - '0';
    if (Uisdigit(*hdr)) {
	if (tm.tm_year < 19) goto baddate;
	tm.tm_year -= 19;
	tm.tm_year = tm.tm_year * 10 + *hdr++ - '0';
	if (!Uisdigit(*hdr)) goto baddate;
	tm.tm_year = tm.tm_year * 10 + *hdr++ - '0';
    } else {
	if (tm.tm_year < 70) {
	    /* two-digit year, probably after 2000.
	     * This patent was overturned, right?
	     */
	    tm.tm_year += 100;
	}
    }
    if (Uisdigit(*hdr)) {
       /* five-digit date */
       goto baddate;
     }

    message_parse_rfc822space(&hdr);
    if (hdr && (flags & PARSE_TIME)) {
	/* Parse hour */
	if (!hdr || !Uisdigit(*hdr)) goto badtime;
	tm.tm_hour = *hdr++ - '0';
	if (!Uisdigit(*hdr)) goto badtime;
	tm.tm_hour = tm.tm_hour * 10 + *hdr++ - '0';
	if (!hdr || *hdr++ != ':') goto badtime;

	/* Parse min */
	if (!hdr || !Uisdigit(*hdr)) goto badtime;
	tm.tm_min = *hdr++ - '0';
	if (!Uisdigit(*hdr)) goto badtime;
	tm.tm_min = tm.tm_min * 10 + *hdr++ - '0';

	if (*hdr == ':') {
	    /* Parse sec */
	    if (!++hdr || !Uisdigit(*hdr)) goto badtime;
	    tm.tm_sec = *hdr++ - '0';
	    if (!Uisdigit(*hdr)) goto badtime;
	    tm.tm_sec = tm.tm_sec * 10 + *hdr++ - '0';
	}

	message_parse_rfc822space(&hdr);
	if (hdr && (flags & PARSE_ZONE)) {
	    /* Parse timezone offset */
	    if (*hdr == '+' || *hdr == '-') {
		/* Parse numeric offset */
		int east = (*hdr++ == '-');

		if (!hdr || !Uisdigit(*hdr)) goto badzone;
		zone_off = *hdr++ - '0';
		if (!hdr || !Uisdigit(*hdr)) goto badzone;
		zone_off = zone_off * 10 + *hdr++ - '0';
		if (!hdr || !Uisdigit(*hdr)) goto badzone;
		zone_off = zone_off * 6 + *hdr++ - '0';
		if (!hdr || !Uisdigit(*hdr)) goto badzone;
		zone_off = zone_off * 10 + *hdr++ - '0';

		if (east) zone_off = -zone_off;
	    }
	    else if (Uisalpha(*hdr)) {
		char zone[4];

		zone[0] = *hdr++;
		if (!Uisalpha(*hdr)) {
		    /* Parse military (single-char) zone */
		    zone[1] = '\0';
		    lcase(zone);
		    if (zone[0] < 'j')
			zone_off = (zone[0] - 'a' + 1) * 60;
		    else if (zone[0] == 'j')
			goto badzone;
		    else if (zone[0] <= 'm')
			zone_off = (zone[0] - 'a') * 60;
		    else if (zone[0] < 'z')
			zone_off = ('m' - zone[0]) * 60;
		    else
			zone_off = 0;
		}
		else {
		    zone[1] = *hdr++;
		    if (!Uisalpha(*hdr)) {
			/* Parse UT (universal time) */
			zone[2] = '\0';
			lcase(zone);
			if (strcmp(zone, "ut")) goto badzone;
			zone_off = 0;
		    }
		    else {
			/* Parse 3-char time zone */
			char *p;

			zone[2] = *hdr;
			zone[3] = '\0';
			lcase(zone);
			/* GMT (Greenwich mean time) */
			if (!strcmp(zone, "gmt")) zone_off = 0;

			/* US time zone */
			else {
			    p = strchr("aecmpyhb", zone[0]);
			    if (!p || zone[2] != 't') goto badzone;
			    zone_off = (strlen(p) - 12) * 60;
			    if (zone[1] == 'd') zone_off += 60;
			    else if (zone[1] != 's') goto badzone;
			}
		    }
		}
	    }
	    else
 badzone:
		zone_off = 0;
	}
    }
    else
 badtime:
	tm.tm_hour = 12;

    tm.tm_isdst = -1;

    t = mktime(&tm);
    /* Don't return -1; it's never right.  Return the current time instead.
     * That's much closer than 1969.
     */
    if (t >= 0) return (t - zone_off * 60);
    
 baddate:
    return (flags & PARSE_NOCREATE) ? 0 : time(0);
}

/*
 * Skip over RFC-822 whitespace and comments
 */
static void
message_parse_rfc822space(s)
char **s;
{
    char *p = *s;
    int commentlevel = 0;

    if (!p) return;
    while (*p && (Uisspace(*p) || *p == '(')) {
	if (*p == '\n') {
	    p++;
	    if (*p != ' ' && *p != '\t') {
		*s = 0;
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
	*s = 0;
    }
    else {
	*s = p;
    }
}

/*
 * Parse the content of a MIME multipart body-part
 */
static void
message_parse_multipart(msg, format, body, boundaries)
struct msg *msg;
int format;
struct body *body;
struct boundary *boundaries;
{
    struct body preamble, epilogue;
    struct param *boundary;
    char *defaultContentType = DEFAULT_CONTENT_TYPE;
    int i, depth;

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
	message_parse_content(msg, format, body, boundaries);
	return;
    }

    /* Expand boundaries array if necessary */
    if (boundaries->count == boundaries->alloc) {
	boundaries->alloc += 20;
	boundaries->id = (char **)xrealloc((char *)boundaries->id,
					   boundaries->alloc * sizeof(char *));
    }
    
    /* Add the new boundary id */
    boundaries->id[boundaries->count++] = boundary->value;
    depth = boundaries->count;

    /* Parse preamble */
    message_parse_content(msg, format, &preamble, boundaries);

    /* Parse the component body-parts */
    while (boundaries->count == depth) {
	body->subpart = (struct body *)xrealloc((char *)body->subpart,
				 (body->numparts+1)*sizeof(struct body));
	message_parse_body(msg, format, &body->subpart[body->numparts++],
			   defaultContentType, boundaries);
	if (msg->offset == msg->len &&
	    body->subpart[body->numparts-1].boundary_size == 0) {
	    /* hit the end of the message, therefore end all pending
	       multiparts */
	    boundaries->count = 0;
	}
    }

    if (boundaries->count == depth-1) {
	/* Parse epilogue */
	message_parse_content(msg, format, &epilogue, boundaries);
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
}

/*
 * Parse the content of a generic body-part
 */
static void
message_parse_content(msg, format, body, boundaries)
struct msg *msg;
int format __attribute__((unused));
struct body *body;
struct boundary *boundaries;
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
	    message_pendingboundary(line, boundaries->id, &boundaries->count)) {
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
	int b64_size, b64_lines, delta;

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


/*
 * Read a line from 'msg' (or at most 'n' characters) into 's'
 */
static char *
message_getline(s, n, msg)
char *s;
unsigned n;
struct msg *msg;
{
    char *rval = s;

    if (n == 0) return 0;
    n--;			/* Allow for terminating nul */

    while (msg->offset < msg->len && n--) {
	if ((*s++ = msg->base[msg->offset++]) == '\n') break;
    }
    *s = '\0';

    if (s == rval) return 0;
    return rval;
}


/*
 * Return nonzero if s is an enclosing boundary delimiter.
 * If we hit a terminating boundary, the integer pointed to by
 * 'boundaryct' is modified appropriately.
 */
static int message_pendingboundary(s, boundaries, boundaryct)
const char *s;
char **boundaries;
int *boundaryct;
{
    int i, len;
    int rfc2046_strict = config_getswitch(IMAPOPT_RFC2046_STRICT);

    if (s[0] != '-' || s[1] != '-') return(0);
    s+=2;

    for (i=0; i < *boundaryct; ++i) {
	len = strlen(boundaries[i]);
        if (!strncmp(s, boundaries[i], len)) {
            if (s[len] == '-' && s[len+1] == '-') *boundaryct = i;
	    else if (!rfc2046_strict && s[len] && !Uisspace(s[len])) {
		/* Allow substring matches in the boundary.
		 *
		 * If rfc2046_strict is enabled, boundaries containing
		 * other boundaries as substrings will be treated as identical
		 * (per RFC 2046 section 5.1.1).  Note that this will
		 * break some messages created by Eudora 5.1 (and earlier).
		 */
		continue;
	    }
            return(1);
        }
    }
    return(0);
}

/*
 * Write the cache information for the message parsed to 'body'
 * to 'outfile'.
 */
static int
message_write_cache(outfd, body)
int outfd;
struct body *body;
{
    struct ibuf section, envelope, bodystructure, oldbody;
    struct ibuf from, to, cc, bcc, subject;
    struct body toplevel;
    int n;
    struct iovec iov[15];
    char* t;

    toplevel.type = "MESSAGE";
    toplevel.subtype = "RFC822";
    toplevel.subpart = body;

    message_ibuf_init(&envelope);
    message_write_envelope(&envelope, body);

    message_ibuf_init(&bodystructure);
    message_write_body(&bodystructure, body, 1);

    message_ibuf_init(&oldbody);
    message_write_body(&oldbody, body, 0);

    message_ibuf_init(&section);
    message_write_section(&section, &toplevel);

    message_ibuf_init(&from);
    message_write_searchaddr(&from, body->from);

    message_ibuf_init(&to);
    message_write_searchaddr(&to, body->to);

    message_ibuf_init(&cc);
    message_write_searchaddr(&cc, body->cc);

    message_ibuf_init(&bcc);
    message_write_searchaddr(&bcc, body->bcc);

    message_ibuf_init(&subject);
    t = charset_decode_mimeheader(body->subject, NULL, 0);
    message_write_nstring(&subject, t);
    free(t);

    message_ibuf_iov(&iov[0], &envelope);
    message_ibuf_iov(&iov[1], &bodystructure);
    message_ibuf_iov(&iov[2], &oldbody);
    message_ibuf_iov(&iov[3], &section);
    message_ibuf_iov(&iov[4], &body->cacheheaders);
    message_ibuf_iov(&iov[5], &from);
    message_ibuf_iov(&iov[6], &to);
    message_ibuf_iov(&iov[7], &cc);
    message_ibuf_iov(&iov[8], &bcc);
    message_ibuf_iov(&iov[9], &subject);

    n = retry_writev(outfd, iov, 10);

    message_ibuf_free(&envelope);
    message_ibuf_free(&bodystructure);
    message_ibuf_free(&oldbody);
    message_ibuf_free(&section);
    message_ibuf_free(&from);
    message_ibuf_free(&to);
    message_ibuf_free(&cc);
    message_ibuf_free(&bcc);
    message_ibuf_free(&subject);

    return n;
}

/* Append character 'c' to 'ibuf' */
#define PUTIBUF(ibuf,c) (((void)((ibuf)->end<(ibuf)->last || message_ibuf_ensure((ibuf),1))),(*((ibuf)->end)++ = (c)))

/*
 * Write the IMAP envelope for 'body' to 'ibuf'
 */
static void
message_write_envelope(ibuf, body)
struct ibuf *ibuf;
struct body *body;
{
    PUTIBUF(ibuf, '(');
    message_write_nstring(ibuf, body->date);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->subject);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->from);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->sender ? body->sender : body->from);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->reply_to ? body->reply_to : body->from);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->to);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->cc);
    PUTIBUF(ibuf, ' ');
    message_write_address(ibuf, body->bcc);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->in_reply_to);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->message_id);
    PUTIBUF(ibuf, ')');
}

/*
 * Write the BODY (if 'newformat' is zero) or BODYSTRUCTURE
 * (if 'newformat' is nonzero) for 'body' to 'ibuf'.
 */
static void
message_write_body(ibuf, body, newformat)
struct ibuf *ibuf;
struct body *body;
int newformat;
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
	    message_write_body(ibuf, &zerotextbody, newformat);
	    return;
	}

	/* Multipart types get a body_multipart */
	PUTIBUF(ibuf, '(');
	for (i = 0; i < body->numparts; i++) {
	    message_write_body(ibuf, &body->subpart[i], newformat);
	}
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, body->subtype);

	if (newformat) {
	    PUTIBUF(ibuf, ' ');
	    if ((param = body->params)!=NULL) {
		PUTIBUF(ibuf, '(');
		while (param) {
		    message_write_nstring(ibuf, param->attribute);
		    PUTIBUF(ibuf, ' ');
		    message_write_nstring(ibuf, param->value);
		    if ((param = param->next)!=NULL) {
			PUTIBUF(ibuf, ' ');
		    }
		}
		PUTIBUF(ibuf, ')');
	    }
	    else message_write_nstring(ibuf, (char *)0);
	    PUTIBUF(ibuf, ' ');
	    if (body->disposition) {
		PUTIBUF(ibuf, '(');
		message_write_nstring(ibuf, body->disposition);
		PUTIBUF(ibuf, ' ');
		if ((param = body->disposition_params)!=NULL) {
		    PUTIBUF(ibuf, '(');
		    while (param) {
			message_write_nstring(ibuf, param->attribute);
			PUTIBUF(ibuf, ' ');
			message_write_nstring(ibuf, param->value);
			if ((param = param->next)!=NULL) {
			    PUTIBUF(ibuf, ' ');
			}
		    }
		    PUTIBUF(ibuf, ')');
		}
		else message_write_nstring(ibuf, (char *)0);
		PUTIBUF(ibuf, ')');
	    }
	    else {
		message_write_nstring(ibuf, (char *)0);
	    }
	    PUTIBUF(ibuf, ' ');
	    if ((param = body->language)!=NULL) {
		PUTIBUF(ibuf, '(');
		while (param) {
		    message_write_nstring(ibuf, param->value);
		    if ((param = param->next)!=NULL) {
			PUTIBUF(ibuf, ' ');
		    }
		}
		PUTIBUF(ibuf, ')');
	    }
	    else message_write_nstring(ibuf, (char *)0);
	    PUTIBUF(ibuf, ' ');
	    message_write_nstring(ibuf, body->location);
	}

	PUTIBUF(ibuf, ')');
	return;
    }

    PUTIBUF(ibuf, '(');
    message_write_nstring(ibuf, body->type);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->subtype);
    PUTIBUF(ibuf, ' ');

    if ((param = body->params)!=NULL) {
	PUTIBUF(ibuf, '(');
	while (param) {
	    message_write_nstring(ibuf, param->attribute);
	    PUTIBUF(ibuf, ' ');
	    message_write_nstring(ibuf, param->value);
	    if ((param = param->next)!=NULL) {
		PUTIBUF(ibuf, ' ');
	    }
	}
	PUTIBUF(ibuf, ')');
    }
    else message_write_nstring(ibuf, (char *)0);
    PUTIBUF(ibuf, ' ');

    message_write_nstring(ibuf, body->id);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->description);
    PUTIBUF(ibuf, ' ');
    message_write_nstring(ibuf, body->encoding ? body->encoding : "7BIT");
    PUTIBUF(ibuf, ' ');
    message_write_number(ibuf, body->content_size);

    if (strcmp(body->type, "TEXT") == 0) {
	/* Text types get a line count */
	PUTIBUF(ibuf, ' ');
	message_write_number(ibuf, body->content_lines);
    }
    else if (strcmp(body->type, "MESSAGE") == 0
	     && strcmp(body->subtype, "RFC822") == 0) {
	/* Message/rfc822 gets a body_msg */
	PUTIBUF(ibuf, ' ');
	message_write_envelope(ibuf, body->subpart);
	PUTIBUF(ibuf, ' ');
	message_write_body(ibuf, body->subpart, newformat);
	PUTIBUF(ibuf, ' ');
	message_write_number(ibuf, body->content_lines);
    }

    if (newformat) {
	/* Add additional fields for BODYSTRUCTURE */
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, body->md5);
	PUTIBUF(ibuf, ' ');
	if (body->disposition) {
	    PUTIBUF(ibuf, '(');
	    message_write_nstring(ibuf, body->disposition);
	    PUTIBUF(ibuf, ' ');
	    if ((param = body->disposition_params)!=NULL) {
		PUTIBUF(ibuf, '(');
		while (param) {
		    message_write_nstring(ibuf, param->attribute);
		    PUTIBUF(ibuf, ' ');
		    message_write_nstring(ibuf, param->value);
		    if ((param = param->next)!=NULL) {
			PUTIBUF(ibuf, ' ');
		    }
		}
		PUTIBUF(ibuf, ')');
	    }
	    else message_write_nstring(ibuf, (char *)0);
	    PUTIBUF(ibuf, ')');
	}
	else {
	    message_write_nstring(ibuf, (char *)0);
	}
	PUTIBUF(ibuf, ' ');
	if ((param = body->language)!=NULL) {
	    PUTIBUF(ibuf, '(');
	    while (param) {
		message_write_nstring(ibuf, param->value);
		if ((param = param->next)!=NULL) {
		    PUTIBUF(ibuf, ' ');
		}
	    }
	    PUTIBUF(ibuf, ')');
	}
	else message_write_nstring(ibuf, (char *)0);
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, body->location);
    }

    PUTIBUF(ibuf, ')');
}

/*
 * Write the address list 'addrlist' to 'ibuf'
 */
static void
message_write_address(ibuf, addrlist)
struct ibuf *ibuf;
struct address *addrlist;
{
    /* If no addresses, write out NIL */
    if (!addrlist) {
	message_write_nstring(ibuf, (char *)0);
	return;
    }

    PUTIBUF(ibuf, '(');

    while (addrlist) {
	PUTIBUF(ibuf, '(');
	message_write_nstring(ibuf, addrlist->name);
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, addrlist->route);
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, addrlist->mailbox);
	PUTIBUF(ibuf, ' ');
	message_write_nstring(ibuf, addrlist->domain);
	PUTIBUF(ibuf, ')');
	addrlist = addrlist->next;
    }

    PUTIBUF(ibuf, ')');
}

/*
 * Write the nil-or-string 's' to 'ibuf'
 */
static void
message_write_nstring(ibuf, s)
struct ibuf *ibuf;
char *s;
{
    char *p;
    int len = 0;

    /* Write null pointer as NIL */
    if (!s) {
	message_ibuf_ensure(ibuf, 3);
	*(ibuf->end)++ = 'N';
	*(ibuf->end)++ = 'I';
	*(ibuf->end)++ = 'L';
	return;
    }

    /* Look for any non-QCHAR characters */
    for (p = s; *p; p++) {
	len++;
	if (*p & 0x80 || *p == '\r' || *p == '\n'
	    || *p == '\"' || *p == '%' || *p == '\\') break;
    }

    if (*p || len >= 1024) {
	/* Write out as literal */
	char buf[100];
	snprintf(buf, sizeof(buf), "{" SIZE_T_FMT "}\r\n", strlen(s));
	message_ibuf_ensure(ibuf, strlen(s)+strlen(buf));
	for (p = buf; *p; p++) *(ibuf->end)++ = *p;
	for (p = s; *p; p++) *(ibuf->end)++ = *p;
    }
    else {
	/* Write out as quoted string */
	message_ibuf_ensure(ibuf, strlen(s)+2);
	*(ibuf->end)++ = '\"';
	for (p = s; *p; p++) *(ibuf->end)++ = *p;
	*(ibuf->end)++ = '\"';
    }
}

/*
 * Write the text 's' to 'ibuf'
 */
static void
message_write_text(ibuf, s)
struct ibuf *ibuf;
char *s;
{
    char *p;

    message_ibuf_ensure(ibuf, strlen(s));
    for (p = s; *p; p++) *(ibuf->end)++ = *p;
}

/*
 * Write the text 's' to 'ibuf', converting to lower case as we go.
 */
static void
message_write_text_lcase(ibuf, s)
struct ibuf *ibuf;
char *s;
{
    char *p;

    message_ibuf_ensure(ibuf, strlen(s));
    for (p = s; *p; p++) *(ibuf->end)++ = TOLOWER(*p);
}

/*
 * Write out the IMAP number 'n' to 'ibuf'
 */
static void
message_write_number(ibuf, n)
struct ibuf *ibuf;
unsigned n;
{
    char buf[100], *p;

    snprintf(buf, sizeof(buf), "%u", n);

    message_ibuf_ensure(ibuf, strlen(buf));
    for (p = buf; *p; p++) *(ibuf->end)++ = *p;
}

/*
 * Write out the FETCH BODY[section] location/size information to 'ibuf'.
 */
static void
message_write_section(ibuf, body)
struct ibuf *ibuf;
struct body *body;
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
	    message_write_bit32(ibuf, body->subpart->numparts+1);
	    message_write_bit32(ibuf, body->subpart->header_offset);
	    message_write_bit32(ibuf, body->subpart->header_size);
	    message_write_bit32(ibuf, body->subpart->content_offset);
	    message_write_bit32(ibuf, body->subpart->content_size);
	    message_write_bit32(ibuf, (-1<<16)|ENCODING_NONE);
	    for (part = 0; part < body->subpart->numparts; part++) {
		message_write_bit32(ibuf, body->subpart->subpart[part].header_offset);
		message_write_bit32(ibuf, body->subpart->subpart[part].header_size);
		message_write_bit32(ibuf, body->subpart->subpart[part].content_offset);
		if (body->subpart->subpart[part].numparts == 0 &&
		    strcmp(body->subpart->subpart[part].type, "MULTIPART") == 0) {
		    /* Treat 0-part multipart as 0-length text */
		    message_write_bit32(ibuf, 0);
		}
		else {
		    message_write_bit32(ibuf, body->subpart->subpart[part].content_size);
		}
		message_write_charset(ibuf, &body->subpart->subpart[part]);
	    }
	    for (part = 0; part < body->subpart->numparts; part++) {
		message_write_section(ibuf, &body->subpart->subpart[part]);
	    }
	}
	else {
	    /*
	     * Part 0 of a message/rfc822 is the message header/text.
	     * Part 1 of a message/rfc822 containing a non-multipart
	     * is the message body.
	     */
	    message_write_bit32(ibuf, 2);
	    message_write_bit32(ibuf, body->subpart->header_offset);
	    message_write_bit32(ibuf, body->subpart->header_size);
	    message_write_bit32(ibuf, body->subpart->content_offset);
	    message_write_bit32(ibuf, body->subpart->content_size);
	    message_write_bit32(ibuf, (-1<<16)|ENCODING_NONE);
	    message_write_bit32(ibuf, body->subpart->header_offset);
	    message_write_bit32(ibuf, body->subpart->header_size);
	    message_write_bit32(ibuf, body->subpart->content_offset);
	    if (strcmp(body->subpart->type, "MULTIPART") == 0) {
		/* Treat 0-part multipart as 0-length text */
		message_write_bit32(ibuf, 0);
		message_write_bit32(ibuf, (-1<<16)|ENCODING_NONE);
	    }
	    else {
		message_write_bit32(ibuf, body->subpart->content_size);
		message_write_charset(ibuf, body->subpart);
	    }
	    message_write_section(ibuf, body->subpart);
	}
    }
    else if (body->numparts) {
	/*
	 * Cannot fetch part 0 of a multipart.
	 * Nested parts of a multipart are the sub-parts.
	 */
	message_write_bit32(ibuf, body->numparts+1);	
	message_write_bit32(ibuf, 0);
	message_write_bit32(ibuf, -1);
	message_write_bit32(ibuf, 0);
	message_write_bit32(ibuf, -1);
	message_write_bit32(ibuf, (-1<<16)|ENCODING_NONE);
	for (part = 0; part < body->numparts; part++) {
	    message_write_bit32(ibuf, body->subpart[part].header_offset);
	    message_write_bit32(ibuf, body->subpart[part].header_size);
	    message_write_bit32(ibuf, body->subpart[part].content_offset);
	    if (body->subpart[part].numparts == 0 &&
		strcmp(body->subpart[part].type, "MULTIPART") == 0) {
		/* Treat 0-part multipart as 0-length text */
		message_write_bit32(ibuf, 0);
		message_write_bit32(ibuf, (-1<<16)|ENCODING_NONE);
	    }
	    else {
		message_write_bit32(ibuf, body->subpart[part].content_size);
		message_write_charset(ibuf, &body->subpart[part]);
	    }
	}
	for (part = 0; part < body->numparts; part++) {
	    message_write_section(ibuf, &body->subpart[part]);
	}
    }
    else {
	/*
	 * Leaf section--no part 0 or nested parts
	 */
	message_write_bit32(ibuf, 0);
    }
}

/*
 * Write the 32-bit charset/encoding value for section 'body' to 'ibuf'
 */
static void
message_write_charset(ibuf, body)
struct ibuf *ibuf;
struct body *body;
{
    int encoding, charset;

    message_parse_charset(body, &encoding, &charset);

    message_write_bit32(ibuf, (charset<<16)|encoding);
}

/*
 * Write the 32-bit integer quantitiy 'val' to 'ibuf'
 */
static void
message_write_bit32(ibuf, val)
struct ibuf *ibuf;
bit32 val;
{
    bit32 buf;
    unsigned i;
    char *p = (char *)&buf;
    
    message_ibuf_ensure(ibuf, sizeof(bit32));
    buf = htonl(val);

    for (i=0; i < sizeof(bit32); i++) {
	*(ibuf->end)++ = *p++;
    }
}

/*
 * Unparse the address list 'addrlist' to 'ibuf'
 */
static void
message_write_searchaddr(ibuf, addrlist)
struct ibuf *ibuf;
struct address *addrlist;
{
    int prevaddr = 0;
    char* tmp;

    while (addrlist) {

	/* Handle RFC-822 group addresses */
	if (!addrlist->domain) {
	    if (addrlist->mailbox) {
		if (prevaddr) PUTIBUF(ibuf, ',');
		
		tmp = charset_decode_mimeheader(addrlist->mailbox, NULL, 0);
		message_write_text(ibuf, tmp);
		free(tmp);
		tmp = NULL;
		PUTIBUF(ibuf, ':');
	
		/* Suppress a trailing comma */
		prevaddr = 0;
	    }
	    else {
		PUTIBUF(ibuf, ';');
		prevaddr = 1;
	    }
	}
	else {
	    if (prevaddr) PUTIBUF(ibuf, ',');

	    if (addrlist->name) {
		tmp = charset_decode_mimeheader(addrlist->name, NULL, 0);
		message_write_text(ibuf, tmp);
		free(tmp); tmp = NULL;
		PUTIBUF(ibuf, ' ');
	    }

	    PUTIBUF(ibuf, '<');
	    if (addrlist->route) {
		message_write_text_lcase(ibuf, addrlist->route);
		PUTIBUF(ibuf, ':');
	    }

	    message_write_text_lcase(ibuf, addrlist->mailbox);
	    PUTIBUF(ibuf, '@');

	    message_write_text_lcase(ibuf, addrlist->domain);
	    PUTIBUF(ibuf, '>');
	    prevaddr = 1;
	}

	addrlist = addrlist->next;
    }
}

/*
 * Initialize 'ibuf'
 */
#define IBUFGROWSIZE 1000
static void 
message_ibuf_init(ibuf)
struct ibuf *ibuf;
{
    char *s = xmalloc(IBUFGROWSIZE);

    ibuf->start = ibuf->end = s + sizeof(bit32);
    ibuf->last = ibuf->start + IBUFGROWSIZE - sizeof(bit32);
}

/*
 * Ensure 'ibuf' has enough free space to append 'len' bytes.
 */
static int
message_ibuf_ensure(struct ibuf *ibuf,
		    unsigned len)
{
    char *s;
    int size;

    if ((unsigned) (ibuf->last - ibuf->end) >= len) return 0;
    if (len < IBUFGROWSIZE) len = IBUFGROWSIZE;

    s = ibuf->start - sizeof(bit32);
    size = len + (ibuf->last - ibuf->start);
    s = xrealloc(s, size + sizeof(bit32));
    s += sizeof(bit32);
    ibuf->end = (ibuf->end - ibuf->start) + s;
    ibuf->start = s;
    ibuf->last = s + size;

    return 1;
}

/*
 * Set up 'iov' to write the data for 'ibuf'.
 */
static void
message_ibuf_iov(iov, ibuf)
struct iovec *iov;
struct ibuf *ibuf;
{
    char *s;
    int len;

    /* Drop padding on end */
    message_ibuf_ensure(ibuf, 3);
    ibuf->end[0] = '\0';
    ibuf->end[1] = '\0';
    ibuf->end[2] = '\0';

    len = (ibuf->end - ibuf->start);
    s = ibuf->start - sizeof(bit32);
    *((bit32 *)s) = htonl(len);

    iov->iov_base = s;
    iov->iov_len = (len+sizeof(bit32)+3) & ~3;
}

/*
 * Free the space used by 'ibuf'
 */
static void
message_ibuf_free(ibuf)
struct ibuf *ibuf;
{
    free(ibuf->start - sizeof(bit32));
}

/*
 * Free the parsed body-part 'body'
 */
void
message_free_body(body)
struct body *body;
{
    struct param *param, *nextparam;
    int part;

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

    if (body->cacheheaders.start) {
	message_ibuf_free(&body->cacheheaders);
    }

    if (body->decoded_body) free(body->decoded_body);
}
