/* sieve_interface.h -- interface for deliver
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

#ifndef SIEVE_H
#define SIEVE_H

#include <stdio.h>

#define SIEVE_VERSION "CMU Sieve 2.4"

/* error codes */
#define SIEVE_OK (0)

#include "strarray.h"
#include "sieve/sieve_err.h"
#include "varlist.h"

/* external sieve types */
typedef struct sieve_interp sieve_interp_t;
typedef struct sieve_script sieve_script_t;
typedef struct sieve_execute sieve_execute_t;
typedef struct bytecode_info bytecode_info_t;

typedef int sieve_callback(void *action_context, void *interp_context, 
			   void *script_context,
			   void *message_context, const char **errmsg);
typedef int sieve_get_size(void *message_context, int *size);
typedef int sieve_get_header(void *message_context, 
			     const char *header,
			     const char ***contents);
typedef int sieve_get_fname(void *message_context, const char **fname);
typedef int sieve_get_envelope(void *message_context, 
			       const char *field,
			       const char ***contents);
typedef int sieve_get_include(void *script_context, const char *script,
			      int isglobal, char *fpath, size_t size);

/* MUST keep this struct sync'd with bodypart in imap/message.h */
typedef struct sieve_bodypart {
    char section[128];
    const char *decoded_body;
} sieve_bodypart_t;

typedef int sieve_get_body(void *message_context, const char **content_types,
			   sieve_bodypart_t ***parts);

typedef struct sieve_vacation {
    int min_response;		/* 0 -> defaults to 3 days */
    int max_response;		/* 0 -> defaults to 90 days */

    /* given a hash, say whether we've already responded to it in the last
       days days.  return SIEVE_OK if we SHOULD autorespond (have not already)
       or SIEVE_DONE if we SHOULD NOT. */
    sieve_callback *autorespond;

    /* mail the response */
    sieve_callback *send_response;
} sieve_vacation_t;


/* sieve_imapflags: NULL -> defaults to \flagged */

typedef struct sieve_redirect_context {
    const char *addr;
} sieve_redirect_context_t;

typedef struct sieve_reject_context {
    const char *msg;
} sieve_reject_context_t;

typedef struct sieve_fileinto_context {
    const char *mailbox;
    strarray_t *imapflags;
} sieve_fileinto_context_t;

typedef struct sieve_keep_context {
    strarray_t *imapflags;
} sieve_keep_context_t;

typedef struct sieve_notify_context {
    const char *method;
    const char **options;
    const char *priority;
    const char *message;
    const char *fname;
} sieve_notify_context_t;

#define SIEVE_HASHLEN 16

typedef struct sieve_autorespond_context {
    unsigned char hash[SIEVE_HASHLEN];
    int seconds;
} sieve_autorespond_context_t;

typedef struct sieve_send_response_context {
    char *addr;
    char *fromaddr;
    const char *msg;
    char *subj;
    int mime;
} sieve_send_response_context_t;

/* build a sieve interpretor */
sieve_interp_t *sieve_interp_alloc(void *interp_context);
int sieve_interp_free(sieve_interp_t **interp);

/* add the callbacks for actions. undefined behavior results if these
   are called after sieve_script_parse is called! */
void sieve_register_redirect(sieve_interp_t *interp, sieve_callback *f);
void sieve_register_discard(sieve_interp_t *interp, sieve_callback *f);
void sieve_register_reject(sieve_interp_t *interp, sieve_callback *f);
void sieve_register_fileinto(sieve_interp_t *interp, sieve_callback *f);
void sieve_register_keep(sieve_interp_t *interp, sieve_callback *f);
int sieve_register_vacation(sieve_interp_t *interp, sieve_vacation_t *v);
void sieve_register_imapflags(sieve_interp_t *interp, const strarray_t *mark);
void sieve_register_notify(sieve_interp_t *interp, sieve_callback *f);
void sieve_register_include(sieve_interp_t *interp, sieve_get_include *f);

/* add the callbacks for messages. again, undefined if used after
   sieve_script_parse */
void sieve_register_size(sieve_interp_t *interp, sieve_get_size *f);
void sieve_register_header(sieve_interp_t *interp, sieve_get_header *f);
void sieve_register_fname(sieve_interp_t *interp, sieve_get_fname *f);
void sieve_register_envelope(sieve_interp_t *interp, sieve_get_envelope *f);
void sieve_register_body(sieve_interp_t *interp, sieve_get_body *f);

typedef int sieve_parse_error(int lineno, const char *msg, 
			      void *interp_context,
			      void *script_context);
void sieve_register_parse_error(sieve_interp_t *interp, sieve_parse_error *f);

typedef int sieve_execute_error(const char *msg, void *interp_context,
				void *script_context, void *message_context);
void sieve_register_execute_error(sieve_interp_t *interp, 
				 sieve_execute_error *f);
 
/* given an interpretor and a script, produce an executable script */
int sieve_script_parse(sieve_interp_t *interp, FILE *script,
		       void *script_context, sieve_script_t **ret);

/* given a path to a bytecode file, load it into the sieve_execute_t */
int sieve_script_load(const char *fpath, sieve_execute_t **ret);

/* Unload a sieve_bytecode_t */
int sieve_script_unload(sieve_execute_t **s);

/* Free a sieve_script_t */
void sieve_script_free(sieve_script_t **s);

/* execute bytecode on a message */
int sieve_execute_bytecode(sieve_execute_t *script, sieve_interp_t *interp,
			   void *script_context, void *message_context);

/* Get space separated list of extensions supported by the implementation */
const char *sieve_listextensions(sieve_interp_t *i);

/* Create a bytecode structure given a parsed commandlist */
int sieve_generate_bytecode(bytecode_info_t **retval, sieve_script_t *s);

/* Emit bytecode to a file descriptor */
int sieve_emit_bytecode(int fd, bytecode_info_t *bc);

/* Free a bytecode_info_t */
void sieve_free_bytecode(bytecode_info_t **p);

#endif
