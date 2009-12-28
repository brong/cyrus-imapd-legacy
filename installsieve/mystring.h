/* mystring.h
 * Tim Martin
 * 9/21/99
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
 * $Id: mystring.h,v 1.6.8.1 2009/12/28 21:51:42 murch Exp $
 */

#include "codes.h"


#ifndef INCLUDED_MYSTRING_H
#define INCLUDED_MYSTRING_H

typedef struct {
  int        len;
  /* Data immediately following... */
}  mystring_t;


int string_allocate(int length,
		    const char *buf,	/* NULL => no copy */
		    mystring_t ** str);

int string_copy(mystring_t *oldstr,
		mystring_t **newstr);

void string_free(mystring_t **str);

int string_compare(mystring_t *str1, mystring_t *str2);

int string_comparestr(mystring_t *str1, char *str2);

int string_compare_with(mystring_t *str1, mystring_t *str2, mystring_t *comp);

/*eq_result_t
  string_equal_cstr(const mystring_t * str, const char *cstr);*/

#define string_DATAPTR(s) (((char *) s)+sizeof(mystring_t))

int safe_to_use_quoted(char *str, int len);


#endif /* INCLUDED_MYSTRING_H */
