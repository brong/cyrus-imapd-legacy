/*
 * $XConsortium: ifparser.h,v 1.1 92/08/22 13:05:39 rws Exp $
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
 * $Id: ifparser.h,v 1.3.8.1 2009/12/28 21:51:48 murch Exp $
 *
 *
 * Copyright 1992 Network Computing Devices, Inc.
 * 
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose and without fee is hereby granted, provided
 * that the above copyright notice appear in all copies and that both that
 * copyright notice and this permission notice appear in supporting
 * documentation, and that the name of Network Computing Devices may not be
 * used in advertising or publicity pertaining to distribution of the software
 * without specific, written prior permission.  Network Computing Devices makes
 * no representations about the suitability of this software for any purpose.
 * It is provided ``as is'' without express or implied warranty.
 * 
 * NETWORK COMPUTING DEVICES DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
 * SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS,
 * IN NO EVENT SHALL NETWORK COMPUTING DEVICES BE LIABLE FOR ANY SPECIAL,
 * INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
 * OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 * 
 * Author:  Jim Fulton
 *          Network Computing Devices, Inc.
 * 
 * Simple if statement processor
 *
 * This module can be used to evaluate string representations of C language
 * if constructs.  It accepts the following grammar:
 * 
 *     EXPRESSION	:=	VALUE
 * 			 |	VALUE  BINOP	EXPRESSION
 * 
 *     VALUE		:=	'('  EXPRESSION  ')'
 * 			 |	'!'  VALUE
 * 			 |	'-'  VALUE
 * 			 |	'defined'  '('  variable  ')'
 * 			 |	variable
 * 			 |	number
 * 
 *     BINOP		:=	'*'	|  '/'	|  '%'
 * 			 |	'+'	|  '-'
 * 			 |	'<<'	|  '>>'
 * 			 |	'<'	|  '>'	|  '<='  |  '>='
 * 			 |	'=='	|  '!='
 * 			 |	'&'	|  '|'
 * 			 |	'&&'	|  '||'
 * 
 * The normal C order of precidence is supported.
 * 
 * 
 * External Entry Points:
 * 
 *     ParseIfExpression		parse a string for #if
 */

#include <stdio.h>

#define const /**/
typedef int Bool;
#define False 0
#define True 1

typedef struct _if_parser {
    struct {				/* functions */
	char *(*handle_error) (/* struct _if_parser *, const char *,
				 const char * */);
	int (*eval_variable) (/* struct _if_parser *, const char *, int */);
	int (*eval_defined) (/* struct _if_parser *, const char *, int */);
    } funcs;
    char *data;
} IfParser;

char *ParseIfExpression (/* IfParser *, const char *, int * */);

