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
 * $Id: isieve.h,v 1.5.8.1 2009/12/28 21:51:42 murch Exp $
 */

#ifndef ISIEVE_H_
#define ISIEVE_H_

#include <sasl/sasl.h>

typedef struct iseive_s isieve_t;

int init_net(char *serverFQDN, int port, isieve_t **obj);


int init_sasl(isieve_t *obj,
	      int ssf,
	      sasl_callback_t *callbacks);

char * read_capability(isieve_t *obj);

typedef enum {
    STAT_CONT = 0,
    STAT_NO = 1,
    STAT_OK = 2
} imt_stat;

int auth_sasl(char *mechlist, isieve_t *obj);


int isieve_put_file(isieve_t *obj, char *filename);

int isieve_put(isieve_t *obj, char *name, char *data, int len);

int isieve_delete(isieve_t *obj, char *name);

typedef void *isieve_listcb_t(char *name, int isactive, void *rock);

int isieve_list(isieve_t *obj, isieve_listcb_t *cb,void *rock);

int isieve_activate(isieve_t *obj, char *name);

int isieve_get(isieve_t *obj,char *name, char **output);  


#endif /* ISIEVE_H_ */
