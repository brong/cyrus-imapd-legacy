/*
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
 * $Id: charset.h,v 1.24 2010/01/06 17:01:44 murch Exp $
 */

#ifndef INCLUDED_CHARSET_H
#define INCLUDED_CHARSET_H

#define ENCODING_NONE 0
#define ENCODING_QP 1
#define ENCODING_BASE64 2
#define ENCODING_UNKNOWN 255

#define CHARSET_UNKNOWN_CHARSET (-1)

typedef int comp_pat;
typedef int charset_index;

/* ensure up to MAXTRANSLATION times expansion into buf */
extern char *charset_convert(const char *s, charset_index charset, char *buf,
    size_t bufsz);
extern char *charset_decode_mimeheader(const char *s, char *buf, 
    size_t bufsz);
extern char *charset_parse_mimeheader(const char *s);

extern charset_index charset_lookupname(const char *name);
extern comp_pat *charset_compilepat(const char *s);
extern void charset_freepat(comp_pat *pat);
extern int charset_searchstring(const char *substr, comp_pat *pat,
    const char *s, size_t len);
extern int charset_searchfile(const char *substr, comp_pat *pat,
                              const char *msg_base, size_t len, 
                              charset_index charset, int encoding);
extern char *charset_decode_mimebody(const char *msg_base, size_t len,
				     int encoding, char **retval, size_t alloced,
				     size_t *outlen);
extern char *charset_encode_mimebody(const char *msg_base, size_t len,
				     char *retval, size_t *outlen, 
				     int *outlines);
extern char *charset_to_utf8(const char *msg_base, size_t len, charset_index charset, int encoding);
extern int charset_search_mimeheader(const char *substr, comp_pat *pat, const char *s, int searchform);

/* Definitions for charset_extractfile */

/* These constants are passed into the index_search_text_receiver_t callback to
   tell it which part of the message is being sent down */
#define SEARCHINDEX_PART_FROM    1
#define SEARCHINDEX_PART_TO      2
#define SEARCHINDEX_PART_CC      3
#define SEARCHINDEX_PART_BCC     4
#define SEARCHINDEX_PART_SUBJECT 5
#define SEARCHINDEX_PART_HEADERS 6 /* headers OTHER than the above headers */
#define SEARCHINDEX_PART_BODY    7

/* These constants tell the index_search_text_receiver_t callback what is happening. */
#define SEARCHINDEX_CMD_BEGINPART  0x01 /* starting a new part */
#define SEARCHINDEX_CMD_APPENDPART 0x02 /* recording some text that belongs to the part */
#define SEARCHINDEX_CMD_ENDPART    0x04 /* done with the part */
#define SEARCHINDEX_CMD_STUFFPART  0x07 /* All of the above in one invocation */

/* This function gets called at least once for each part of every message.
   The invocations form a sequence:
       CMD_BEGINPART <part1>
       CMD_APPENDPART <part1, text, text_len>     (1 or more times)
       CMD_ENDPART <part1>
       ...
       CMD_BEGINPART <partN>
       CMD_APPENDPART <partN, text, text_len>     (1 or more times)
       CMD_ENDPART <partN>
   BEGIN, APPEND and/or END operations on the same part may be combined into one call by
   ORing the 'cmds' flags.

   The parts need not arrive in any particular order, but each part
   can only participate in one BEGIN ... APPEND ... END sequence, and
   the sequences for different parts cannot be interleaved.
*/
typedef void index_search_text_receiver_t(int UID, int part, int cmds,
  char const* text, int text_len, void* rock);

/* Extract the body text for the message denoted by 'uid', convert its
   text to the canonical form for searching, and pass the converted
   text down in a series of invocations to the callback function with
   part=SEARCHINDEX_PART_BODY and cmds=CMD_APPENDPART.  This is called
   by index_getsearchtextmsg to extract the MIME body parts. */ 
extern int charset_extractfile(index_search_text_receiver_t receiver,
                               void* rock, int uid, const char *msg_base, 
                               size_t len, charset_index charset,
                               int encoding);

#endif /* INCLUDED_CHARSET_H */
