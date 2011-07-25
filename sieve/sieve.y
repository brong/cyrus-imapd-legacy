%{
/* sieve.y -- sieve parser
 * Larry Greenfield
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
 * $Id: sieve.y,v 1.45.2.1 2010/02/12 03:41:11 brong Exp $
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>
#include "xmalloc.h"
#include "comparator.h"
#include "interp.h"
#include "script.h"
#include "tree.h"

#include "../lib/imapurl.h"
#include "../lib/util.h"
#include "../lib/imparse.h"
#include "../lib/libconfig.h"

#define ERR_BUF_SIZE 1024

char errbuf[ERR_BUF_SIZE];

    /* definitions */
    extern int addrparse(void);

struct vtags {
    int days;
    strarray_t *addresses;
    char *subject;
    char *from;
    char *handle;
    int mime;
};

struct htags {
    char *comparator;
    int comptag;
    int relation;
};

struct aetags {
    int addrtag;
    char *comparator;
    int comptag;
    int relation;
};

struct btags {
    int transform;
    int offset;
    strarray_t *content_types;
    char *comparator;
    int comptag;
    int relation;
};

struct ntags {
    char *method;
    char *id;
    strarray_t *options;
    int priority;
    char *message;
};

struct dtags {
    int comptag;
    int relation;
    void *pattern;
    int priority;
};

static commandlist_t *ret;
static sieve_script_t *parse_script;
static char *check_reqs(strarray_t *sl);
static test_t *build_address(int t, struct aetags *ae,
			     strarray_t *sl, strarray_t *pl);
static test_t *build_header(int t, struct htags *h,
			    strarray_t *sl, strarray_t *pl);
static test_t *build_body(int t, struct btags *b, strarray_t *pl);
static commandlist_t *build_vacation(int t, struct vtags *h, char *s);
static commandlist_t *build_notify(int t, struct ntags *n);
static commandlist_t *build_denotify(int t, struct dtags *n);
static commandlist_t *build_fileinto(int t, int c, char *f);
static commandlist_t *build_redirect(int t, int c, char *a);
static struct aetags *new_aetags(void);
static struct aetags *canon_aetags(struct aetags *ae);
static void free_aetags(struct aetags *ae);
static struct htags *new_htags(void);
static struct htags *canon_htags(struct htags *h);
static void free_htags(struct htags *h);
static struct btags *new_btags(void);
static struct btags *canon_btags(struct btags *b);
static void free_btags(struct btags *b);
static struct vtags *new_vtags(void);
static struct vtags *canon_vtags(struct vtags *v);
static void free_vtags(struct vtags *v);
static struct ntags *new_ntags(void);
static struct ntags *canon_ntags(struct ntags *n);
static void free_ntags(struct ntags *n);
static struct dtags *new_dtags(void);
static struct dtags *canon_dtags(struct dtags *d);
static void free_dtags(struct dtags *d);

static int verify_stringlist(strarray_t *sl, int (*verify)(char *));
static int verify_mailbox(char *s);
static int verify_address(char *s);
static int verify_header(char *s);
static int verify_addrheader(char *s);
static int verify_envelope(char *s);
static int verify_flag(char *s);
static int verify_relat(char *s);
#ifdef ENABLE_REGEX
static int verify_regex(char *s, int cflags);
static int verify_regexs(const strarray_t *sl, char *comp);
#endif
static int verify_utf8(char *s);

int yyerror(char *msg);
extern int yylex(void);
extern void yyrestart(FILE *f);

#define YYERROR_VERBOSE /* i want better error messages! */

/* byacc default is 500, bison default is 10000 - go with the
   larger to support big sieve scripts (see Bug #3461) */
#define YYSTACKSIZE 10000
%}

%union {
    int nval;
    char *sval;
    strarray_t *sl;
    test_t *test;
    testlist_t *testl;
    commandlist_t *cl;
    struct vtags *vtag;
    struct aetags *aetag;
    struct htags *htag;
    struct btags *btag;
    struct ntags *ntag;
    struct dtags *dtag;
}

%token <nval> NUMBER
%token <sval> STRING
%token IF ELSIF ELSE
%token REJCT FILEINTO REDIRECT KEEP STOP DISCARD VACATION REQUIRE
%token SETFLAG ADDFLAG REMOVEFLAG MARK UNMARK
%token NOTIFY DENOTIFY
%token ANYOF ALLOF EXISTS SFALSE STRUE HEADER NOT SIZE ADDRESS ENVELOPE BODY
%token COMPARATOR IS CONTAINS MATCHES REGEX COUNT VALUE OVER UNDER
%token GT GE LT LE EQ NE
%token ALL LOCALPART DOMAIN USER DETAIL
%token RAW TEXT CONTENT
%token DAYS ADDRESSES SUBJECT FROM HANDLE MIME
%token METHOD ID OPTIONS LOW NORMAL HIGH ANY MESSAGE
%token INCLUDE PERSONAL GLOBAL RETURN
%token COPY

%type <cl> commands command action elsif block
%type <sl> stringlist strings
%type <test> test
%type <nval> comptag relcomp sizetag addrparttag addrorenv location copy
%type <testl> testlist tests
%type <htag> htags
%type <aetag> aetags
%type <btag> btags
%type <vtag> vtags
%type <ntag> ntags
%type <dtag> dtags
%type <nval> priority

%%

start: reqs			{ ret = NULL; }
	| reqs commands		{ ret = $2; }
	;

reqs: /* empty */
	| require reqs
	;

require: REQUIRE stringlist ';'	{ char *err = check_reqs($2);
                                  if (err) {
				    yyerror(err);
				    free(err);
				    YYERROR; 
                                  } }
	;

commands: command		{ $$ = $1; }
	| command commands	{ $1->next = $2; $$ = $1; }
	;

command: action ';'		{ $$ = $1; }
	| IF test block elsif   { $$ = new_if($2, $3, $4); }
	| error ';'		{ $$ = new_command(STOP); }
	;

elsif: /* empty */               { $$ = NULL; }
	| ELSIF test block elsif { $$ = new_if($2, $3, $4); }
	| ELSE block             { $$ = $2; }
	;

action: REJCT STRING             { if (!parse_script->support.reject) {
				     yyerror("reject MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   if (!verify_utf8($2)) {
				     YYERROR; /* vu should call yyerror() */
				   }
				   $$ = new_command(REJCT);
				   $$->u.str = $2; }
	| FILEINTO copy STRING	 { if (!parse_script->support.fileinto) {
				     yyerror("fileinto MUST be enabled with \"require\"");
	                             YYERROR;
                                   }
				   if (!verify_mailbox($3)) {
				     YYERROR; /* vm should call yyerror() */
				   }
	                           $$ = build_fileinto(FILEINTO, $2, $3); }
	| REDIRECT copy STRING   { if (!verify_address($3)) {
				     YYERROR; /* va should call yyerror() */
				   }
	                           $$ = build_redirect(REDIRECT, $2, $3); }
	| KEEP			 { $$ = new_command(KEEP); }
	| STOP			 { $$ = new_command(STOP); }
	| DISCARD		 { $$ = new_command(DISCARD); }
	| VACATION vtags STRING  { if (!parse_script->support.vacation) {
				     yyerror("vacation MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   if (($2->mime == -1) && !verify_utf8($3)) {
				     YYERROR; /* vu should call yyerror() */
				   }
  				   $$ = build_vacation(VACATION,
					    canon_vtags($2), $3); }
        | SETFLAG stringlist     { if (!parse_script->support.imapflags) {
                                    yyerror("imapflags MUST be enabled with \"require\"");
                                    YYERROR;
                                   }
                                  if (!verify_stringlist($2, verify_flag)) {
                                    YYERROR; /* vf should call yyerror() */
                                  }
                                  $$ = new_command(SETFLAG);
                                  $$->u.sl = $2; }
         | ADDFLAG stringlist     { if (!parse_script->support.imapflags) {
                                    yyerror("imapflags MUST be enabled with \"require\"");
                                    YYERROR;
                                    }
                                  if (!verify_stringlist($2, verify_flag)) {
                                    YYERROR; /* vf should call yyerror() */
                                  }
                                  $$ = new_command(ADDFLAG);
                                  $$->u.sl = $2; }
         | REMOVEFLAG stringlist  { if (!parse_script->support.imapflags) {
                                    yyerror("imapflags MUST be enabled with \"require\"");
                                    YYERROR;
                                    }
                                  if (!verify_stringlist($2, verify_flag)) {
                                    YYERROR; /* vf should call yyerror() */
                                  }
                                  $$ = new_command(REMOVEFLAG);
                                  $$->u.sl = $2; }
         | MARK                   { if (!parse_script->support.imapflags) {
                                    yyerror("imapflags MUST be enabled with \"require\"");
                                    YYERROR;
                                    }
                                  $$ = new_command(MARK); }
         | UNMARK                 { if (!parse_script->support.imapflags) {
                                    yyerror("imapflags MUST be enabled with \"require\"");
                                    YYERROR;
                                    }
                                  $$ = new_command(UNMARK); }

         | NOTIFY ntags           { if (!parse_script->support.notify) {
				       yyerror("notify MUST be enabled with \"require\"");
				       $$ = new_command(NOTIFY); 
				       YYERROR;
	 			    } else {
				      $$ = build_notify(NOTIFY,
				             canon_ntags($2));
				    } }
         | DENOTIFY dtags         { if (!parse_script->support.notify) {
                                       yyerror("notify MUST be enabled with \"require\"");
				       $$ = new_command(DENOTIFY);
				       YYERROR;
				    } else {
					$$ = build_denotify(DENOTIFY, canon_dtags($2));
					if ($$ == NULL) { 
			yyerror("unable to find a compatible comparator");
			YYERROR; } } }

	 | INCLUDE location STRING { if (!parse_script->support.include) {
				     yyerror("include MUST be enabled with \"require\"");
	                             YYERROR;
                                   }
	                           $$ = new_command(INCLUDE);
				   $$->u.inc.location = $2;
				   $$->u.inc.script = $3; }
         | RETURN		 { if (!parse_script->support.include) {
                                    yyerror("include MUST be enabled with \"require\"");
                                    YYERROR;
                                  }
                                   $$ = new_command(RETURN); }
	;

location: /* empty */		 { $$ = PERSONAL; }
	| PERSONAL		 { $$ = PERSONAL; }
	| GLOBAL		 { $$ = GLOBAL; }
	;

ntags: /* empty */		 { $$ = new_ntags(); }
	| ntags ID STRING	 { if ($$->id != NULL) { 
					yyerror("duplicate :method"); YYERROR; }
				   else { $$->id = $3; } }
	| ntags METHOD STRING	 { if ($$->method != NULL) { 
					yyerror("duplicate :method"); YYERROR; }
				   else { $$->method = $3; } }
	| ntags OPTIONS stringlist { if ($$->options != NULL) { 
					yyerror("duplicate :options"); YYERROR; }
				     else { $$->options = $3; } }
        | ntags priority	 { if ($$->priority != -1) { 
                                 yyerror("duplicate :priority"); YYERROR; }
                                   else { $$->priority = $2; } }
	| ntags MESSAGE STRING	 { if ($$->message != NULL) { 
					yyerror("duplicate :message"); YYERROR; }
				   else { $$->message = $3; } }
	;

dtags: /* empty */		 { $$ = new_dtags(); }
	| dtags priority	 { if ($$->priority != -1) { 
				yyerror("duplicate priority level"); YYERROR; }
				   else { $$->priority = $2; } }
	| dtags comptag STRING 	 { if ($$->comptag != -1)
	                             { 
					 yyerror("duplicate comparator type tag"); YYERROR;
				     }
	                           $$->comptag = $2;
#ifdef ENABLE_REGEX
				   if ($$->comptag == REGEX)
				   {
				       int cflags = REG_EXTENDED |
					   REG_NOSUB | REG_ICASE;
				       if (!verify_regex($3, cflags)) { YYERROR; }
				   }
#endif
				   $$->pattern = $3;
	                          }
	| dtags relcomp STRING  { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2;
				   $$->relation = verify_relat($3);
				   if ($$->relation==-1) 
				     {YYERROR; /*vr called yyerror()*/ }
				   } }
	;

priority: LOW                   { $$ = LOW; }
        | NORMAL                { $$ = NORMAL; }
        | HIGH                  { $$ = HIGH; }
        ;

vtags: /* empty */		 { $$ = new_vtags(); }
	| vtags DAYS NUMBER	 { if ($$->days != -1) { 
					yyerror("duplicate :days"); YYERROR; }
				   else { $$->days = $3; } }
	| vtags ADDRESSES stringlist { if ($$->addresses != NULL) { 
					yyerror("duplicate :addresses"); 
					YYERROR;
				       } else if (!verify_stringlist($3,
							verify_address)) {
					  YYERROR;
				       } else {
					 $$->addresses = $3; } }
	| vtags SUBJECT STRING	 { if ($$->subject != NULL) { 
					yyerror("duplicate :subject"); 
					YYERROR;
				   } else if (!verify_utf8($3)) {
				        YYERROR; /* vu should call yyerror() */
				   } else { $$->subject = $3; } }
	| vtags FROM STRING	 { if ($$->from != NULL) { 
					yyerror("duplicate :from"); 
					YYERROR;
				   } else if (!verify_address($3)) {
				        YYERROR; /* vu should call yyerror() */
				   } else { $$->from = $3; } }
	| vtags HANDLE STRING	 { if ($$->handle != NULL) { 
					yyerror("duplicate :handle"); 
					YYERROR;
				   } else if (!verify_utf8($3)) {
				        YYERROR; /* vu should call yyerror() */
				   } else { $$->handle = $3; } }
	| vtags MIME		 { if ($$->mime != -1) { 
					yyerror("duplicate :mime"); 
					YYERROR; }
				   else { $$->mime = MIME; } }
	;

stringlist: '[' strings ']'      { $$ = $2; }
	| STRING		 {
				    $$ = strarray_new();
				    strarray_appendm($$, $1);
				 }
	;

strings: STRING			 {
				    $$ = strarray_new();
				    strarray_appendm($$, $1);
				 }
	| strings ',' STRING	 {
				    $$ = $1;
				    strarray_appendm($$, $3);
				 }
	;

block: '{' commands '}'		 { $$ = $2; }
	| '{' '}'		 { $$ = NULL; }
	;

test:     ANYOF testlist	 { $$ = new_test(ANYOF); $$->u.tl = $2; }
        | ALLOF testlist	 { $$ = new_test(ALLOF); $$->u.tl = $2; }
        | EXISTS stringlist      { $$ = new_test(EXISTS); $$->u.sl = $2; }
        | SFALSE		 { $$ = new_test(SFALSE); }
	| STRUE			 { $$ = new_test(STRUE); }
	| HEADER htags stringlist stringlist
				 {
				     if (!verify_stringlist($3, verify_header)) {
					 YYERROR; /* vh should call yyerror() */
				     }
				     if (!verify_stringlist($4, verify_utf8)) {
					 YYERROR; /* vu should call yyerror() */
				     }
				     
				     $2 = canon_htags($2);
#ifdef ENABLE_REGEX
				     if ($2->comptag == REGEX)
				     {
					 if (!(verify_regexs($4, $2->comparator)))
					 { YYERROR; }
				     }
#endif
				     $$ = build_header(HEADER, $2, $3, $4);
				     if ($$ == NULL) { 
					 yyerror("unable to find a compatible comparator");
					 YYERROR; } 
				 }


        | addrorenv aetags stringlist stringlist
				 { 
				     if (($1 == ADDRESS) &&
					 !verify_stringlist($3, verify_addrheader))
					 { YYERROR; }
				     else if (($1 == ENVELOPE) &&
					      !verify_stringlist($3, verify_envelope))
					 { YYERROR; }
				     $2 = canon_aetags($2);
#ifdef ENABLE_REGEX
				     if ($2->comptag == REGEX)
				     {
					 if (!( verify_regexs($4, $2->comparator)))
					 { YYERROR; }
				     }
#endif
				     $$ = build_address($1, $2, $3, $4);
				     if ($$ == NULL) { 
					 yyerror("unable to find a compatible comparator");
					 YYERROR; } 
				 }

	| BODY btags stringlist
				 {
				     if (!parse_script->support.body) {
                                       yyerror("body MUST be enabled with \"require\"");
				       YYERROR;
				     }
					
				     if (!verify_stringlist($3, verify_utf8)) {
					 YYERROR; /* vu should call yyerror() */
				     }
				     
				     $2 = canon_btags($2);
#ifdef ENABLE_REGEX
				     if ($2->comptag == REGEX)
				     {
					 if (!(verify_regexs($3, $2->comparator)))
					 { YYERROR; }
				     }
#endif
				     $$ = build_body(BODY, $2, $3);
				     if ($$ == NULL) { 
					 yyerror("unable to find a compatible comparator");
					 YYERROR; } 
				 }


	| NOT test		 { $$ = new_test(NOT); $$->u.t = $2; }
	| SIZE sizetag NUMBER    { $$ = new_test(SIZE); $$->u.sz.t = $2;
		                   $$->u.sz.n = $3; }
	| error			 { $$ = NULL; }
	;

addrorenv: ADDRESS		 { $$ = ADDRESS; }
	| ENVELOPE		 {if (!parse_script->support.envelope)
	                              {yyerror("envelope MUST be enabled with \"require\""); YYERROR;}
	                          else{$$ = ENVELOPE; }
	                         }

	;

aetags: /* empty */              { $$ = new_aetags(); }
        | aetags addrparttag	 { $$ = $1;
				   if ($$->addrtag != -1) { 
			yyerror("duplicate or conflicting address part tag");
			YYERROR; }
				   else { $$->addrtag = $2; } }
	| aetags comptag         { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2; } }
	| aetags relcomp STRING{ $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2;
				   $$->relation = verify_relat($3);
				   if ($$->relation==-1) 
				     {YYERROR; /*vr called yyerror()*/ }
				   } }
        | aetags COMPARATOR STRING { $$ = $1;
	if ($$->comparator != NULL) { 
			yyerror("duplicate comparator tag"); YYERROR; }
				   else if (!strcmp($3, "i;ascii-numeric") &&
					    !parse_script->support.i_ascii_numeric) {
			yyerror("comparator-i;ascii-numeric MUST be enabled with \"require\"");
			YYERROR; }
				   else { $$->comparator = $3; } }
	;

htags: /* empty */		 { $$ = new_htags(); }
	| htags comptag		 { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2; } }
	| htags relcomp STRING { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2;
				   $$->relation = verify_relat($3);
				   if ($$->relation==-1) 
				     {YYERROR; /*vr called yyerror()*/ }
				   } }
	| htags COMPARATOR STRING { $$ = $1;
				   if ($$->comparator != NULL) { 
			 yyerror("duplicate comparator tag"); YYERROR; }
				   else if (!strcmp($3, "i;ascii-numeric") &&
					    !parse_script->support.i_ascii_numeric) { 
			 yyerror("comparator-i;ascii-numeric MUST be enabled with \"require\"");  YYERROR; }
				   else { 
				     $$->comparator = $3; } }
        ;

btags: /* empty */		 { $$ = new_btags(); }
        | btags RAW	 	 { $$ = $1;
				   if ($$->transform != -1) {
			yyerror("duplicate or conflicting transform tag");
			YYERROR; }
				   else { $$->transform = RAW; } }
        | btags TEXT	 	 { $$ = $1;
				   if ($$->transform != -1) {
			yyerror("duplicate or conflicting transform tag");
			YYERROR; }
				   else { $$->transform = TEXT; } }
        | btags CONTENT stringlist { $$ = $1;
				   if ($$->transform != -1) {
			yyerror("duplicate or conflicting transform tag");
			YYERROR; }
				   else {
				       $$->transform = CONTENT;
				       $$->content_types = $3;
				   } }
	| btags comptag		 { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2; } }
	| btags relcomp STRING { $$ = $1;
				   if ($$->comptag != -1) { 
			yyerror("duplicate comparator type tag"); YYERROR; }
				   else { $$->comptag = $2;
				   $$->relation = verify_relat($3);
				   if ($$->relation==-1) 
				     {YYERROR; /*vr called yyerror()*/ }
				   } }
	| btags COMPARATOR STRING { $$ = $1;
				   if ($$->comparator != NULL) { 
			 yyerror("duplicate comparator tag"); YYERROR; }
				   else if (!strcmp($3, "i;ascii-numeric") &&
					    !parse_script->support.i_ascii_numeric) { 
			 yyerror("comparator-i;ascii-numeric MUST be enabled with \"require\"");  YYERROR; }
				   else { 
				     $$->comparator = $3; } }
        ;


addrparttag: ALL                 { $$ = ALL; }
	| LOCALPART		 { $$ = LOCALPART; }
	| DOMAIN                 { $$ = DOMAIN; }
	| USER                   { if (!parse_script->support.subaddress) {
				     yyerror("subaddress MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   $$ = USER; }  
	| DETAIL                { if (!parse_script->support.subaddress) {
				     yyerror("subaddress MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   $$ = DETAIL; }
	;
comptag: IS			 { $$ = IS; }
	| CONTAINS		 { $$ = CONTAINS; }
	| MATCHES		 { $$ = MATCHES; }
	| REGEX			 { if (!parse_script->support.regex) {
				     yyerror("regex MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   $$ = REGEX; }
	;

relcomp: COUNT			 { if (!parse_script->support.relational) {
				     yyerror("relational MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   $$ = COUNT; }
	| VALUE			 { if (!parse_script->support.relational) {
				     yyerror("relational MUST be enabled with \"require\"");
				     YYERROR;
				   }
				   $$ = VALUE; }
	;


sizetag: OVER			 { $$ = OVER; }
	| UNDER			 { $$ = UNDER; }
	;

copy: /* empty */		 { $$ = 0; }
	| COPY			 { if (!parse_script->support.copy) {
				     yyerror("copy MUST be enabled with \"require\"");
	                             YYERROR;
                                   }
				   $$ = COPY; }
	;

testlist: '(' tests ')'		 { $$ = $2; }
	;

tests: test                      { $$ = new_testlist($1, NULL); }
	| test ',' tests         { $$ = new_testlist($1, $3); }
	;

%%
commandlist_t *sieve_parse(sieve_script_t *script, FILE *f)
{
    commandlist_t *t;

    parse_script = script;
    yyrestart(f);
    if (yyparse()) {
	t = NULL;
    } else {
	t = ret;
    }
    ret = NULL;
    return t;
}

int yyerror(char *msg)
{
    extern int yylineno;

    parse_script->err++;
    if (parse_script->interp.err) {
	parse_script->interp.err(yylineno, msg, 
				 parse_script->interp.interp_context,
				 parse_script->script_context);
    }

    return 0;
}

static char *check_reqs(strarray_t *sa)
{
    char *s;
    struct buf errs = BUF_INITIALIZER;
    char *res;

    while ((s = strarray_shift(sa))) {
	if (!script_require(parse_script, s)) {
	    if (!errs.len)
		buf_printf(&errs, "Unsupported feature(s) in \"require\": \"%s\"", s);
	    else
		buf_printf(&errs, ", \"%s\"", s);
	}
	free(s);
    }
    strarray_free(sa);

    res = buf_release(&errs);
    if (!res[0]) {
	free(res);
	return NULL;
    }

    return res;
}

static test_t *build_address(int t, struct aetags *ae,
			     strarray_t *sl, strarray_t *pl)
{
    test_t *ret = new_test(t);	/* can be either ADDRESS or ENVELOPE */

    assert((t == ADDRESS) || (t == ENVELOPE));

    if (ret) {
	ret->u.ae.comptag = ae->comptag;
	ret->u.ae.relation=ae->relation;
	ret->u.ae.comparator=xstrdup(ae->comparator);
	ret->u.ae.sl = sl;
	ret->u.ae.pl = pl;
	ret->u.ae.addrpart = ae->addrtag;
	free_aetags(ae);

    }
    return ret;
}

static test_t *build_header(int t, struct htags *h,
			    strarray_t *sl, strarray_t *pl)
{
    test_t *ret = new_test(t);	/* can be HEADER */

    assert(t == HEADER);

    if (ret) {
	ret->u.h.comptag = h->comptag;
	ret->u.h.relation=h->relation;
	ret->u.h.comparator=xstrdup(h->comparator);
	ret->u.h.sl = sl;
	ret->u.h.pl = pl;
	free_htags(h);
    }
    return ret;
}

static test_t *build_body(int t, struct btags *b, strarray_t *pl)
{
    test_t *ret = new_test(t);	/* can be BODY */

    assert(t == BODY);

    if (ret) {
	ret->u.b.comptag = b->comptag;
	ret->u.b.relation = b->relation;
	ret->u.b.comparator = xstrdup(b->comparator);
	ret->u.b.transform = b->transform;
	ret->u.b.offset = b->offset;
	ret->u.b.content_types = b->content_types; b->content_types = NULL;
	ret->u.b.pl = pl;
	free_btags(b);
    }
    return ret;
}

static commandlist_t *build_vacation(int t, struct vtags *v, char *reason)
{
    commandlist_t *ret = new_command(t);

    assert(t == VACATION);

    if (ret) {
	ret->u.v.subject = v->subject; v->subject = NULL;
	ret->u.v.from = v->from; v->from = NULL;
	ret->u.v.handle = v->handle; v->handle = NULL;
	ret->u.v.days = v->days;
	ret->u.v.mime = v->mime;
	ret->u.v.addresses = v->addresses; v->addresses = NULL;
	free_vtags(v);
	ret->u.v.message = reason;
    }
    return ret;
}

static commandlist_t *build_notify(int t, struct ntags *n)
{
    commandlist_t *ret = new_command(t);

    assert(t == NOTIFY);
       if (ret) {
	ret->u.n.method = n->method; n->method = NULL;
	ret->u.n.id = n->id; n->id = NULL;
	ret->u.n.options = n->options; n->options = NULL;
	ret->u.n.priority = n->priority;
	ret->u.n.message = n->message; n->message = NULL;
	free_ntags(n);
    }
    return ret;
}

static commandlist_t *build_denotify(int t, struct dtags *d)
{
    commandlist_t *ret = new_command(t);

    assert(t == DENOTIFY);

    if (ret) {
	ret->u.d.comptag = d->comptag;
	ret->u.d.relation=d->relation;
	ret->u.d.pattern = d->pattern; d->pattern = NULL;
	ret->u.d.priority = d->priority;
	free_dtags(d);
    }
    return ret;
}

static commandlist_t *build_fileinto(int t, int copy, char *folder)
{
    commandlist_t *ret = new_command(t);

    assert(t == FILEINTO);

    if (ret) {
	ret->u.f.copy = copy;
	if (config_getswitch(IMAPOPT_SIEVE_UTF8FILEINTO)) {
	    ret->u.f.folder = xmalloc(5 * strlen(folder) + 1);
	    UTF8_to_mUTF7(ret->u.f.folder, folder);
	    free(folder);
	}
	else {
	    ret->u.f.folder = folder;
	}
    }
    return ret;
}

static commandlist_t *build_redirect(int t, int copy, char *address)
{
    commandlist_t *ret = new_command(t);

    assert(t == REDIRECT);

    if (ret) {
	ret->u.r.copy = copy;
	ret->u.r.address = address;
    }
    return ret;
}

static struct aetags *new_aetags(void)
{
    struct aetags *r = (struct aetags *) xmalloc(sizeof(struct aetags));

    r->addrtag = r->comptag = r->relation=-1;
    r->comparator=NULL;

    return r;
}

static struct aetags *canon_aetags(struct aetags *ae)
{
    if (ae->addrtag == -1) { ae->addrtag = ALL; }
    if (ae->comparator == NULL) {
        ae->comparator = xstrdup("i;ascii-casemap");
    }
    if (ae->comptag == -1) { ae->comptag = IS; }
    return ae;
}

static void free_aetags(struct aetags *ae)
{
    free(ae->comparator);
     free(ae);
}

static struct htags *new_htags(void)
{
    struct htags *r = (struct htags *) xmalloc(sizeof(struct htags));

    r->comptag = r->relation= -1;
    
    r->comparator = NULL;

    return r;
}

static struct htags *canon_htags(struct htags *h)
{
    if (h->comparator == NULL) {
	h->comparator = xstrdup("i;ascii-casemap");
    }
    if (h->comptag == -1) { h->comptag = IS; }
    return h;
}

static void free_htags(struct htags *h)
{
    free(h->comparator);
    free(h);
}

static struct btags *new_btags(void)
{
    struct btags *r = (struct btags *) xmalloc(sizeof(struct btags));

    r->transform = r->offset = r->comptag = r->relation = -1;
    r->content_types = NULL;
    r->comparator = NULL;

    return r;
}

static struct btags *canon_btags(struct btags *b)
{
    if (b->transform == -1) { b->transform = TEXT; }
    if (b->content_types == NULL) {
	b->content_types = strarray_new();
	if (b->transform == RAW) {
	    strarray_append(b->content_types, "");
	} else {
	    strarray_append(b->content_types, "text");
	}
    }
    if (b->offset == -1) { b->offset = 0; }
    if (b->comparator == NULL) { b->comparator = xstrdup("i;ascii-casemap"); }
    if (b->comptag == -1) { b->comptag = IS; }
    return b;
}

static void free_btags(struct btags *b)
{
    if (b->content_types) { strarray_free(b->content_types); }
    free(b->comparator);
    free(b);
}

static struct vtags *new_vtags(void)
{
    struct vtags *r = (struct vtags *) xmalloc(sizeof(struct vtags));

    r->days = -1;
    r->addresses = NULL;
    r->subject = NULL;
    r->from = NULL;
    r->handle = NULL;
    r->mime = -1;

    return r;
}

static struct vtags *canon_vtags(struct vtags *v)
{
    assert(parse_script->interp.vacation != NULL);

    if (v->days == -1) { v->days = 7; }
    if (v->days < parse_script->interp.vacation->min_response) 
       { v->days = parse_script->interp.vacation->min_response; }
    if (v->days > parse_script->interp.vacation->max_response)
       { v->days = parse_script->interp.vacation->max_response; }
    if (v->mime == -1) { v->mime = 0; }

    return v;
}

static void free_vtags(struct vtags *v)
{
    if (v->addresses) { strarray_free(v->addresses); }
    if (v->subject) { free(v->subject); }
    if (v->from) { free(v->from); }
    if (v->handle) { free(v->handle); }
    free(v);
}

static struct ntags *new_ntags(void)
{
    struct ntags *r = (struct ntags *) xmalloc(sizeof(struct ntags));

    r->method = NULL;
    r->id = NULL;
    r->options = NULL;
    r->priority = -1;
    r->message = NULL;

    return r;
}

static struct ntags *canon_ntags(struct ntags *n)
{
    if (n->priority == -1) { n->priority = NORMAL; }
    if (n->message == NULL) { n->message = xstrdup("$from$: $subject$"); }
    if (n->method == NULL) { n->method = xstrdup("default"); }
    return n;
}
static struct dtags *canon_dtags(struct dtags *d)
{
    if (d->priority == -1) { d->priority = ANY; }
    if (d->comptag == -1) { d->comptag = ANY; }
       return d;
}

static void free_ntags(struct ntags *n)
{
    if (n->method) { free(n->method); }
    if (n->id) { free(n->id); }
    if (n->options) { strarray_free(n->options); }
    if (n->message) { free(n->message); }
    free(n);
}

static struct dtags *new_dtags(void)
{
    struct dtags *r = (struct dtags *) xmalloc(sizeof(struct dtags));

    r->comptag = r->priority= r->relation = -1;
    r->pattern  = NULL;

    return r;
}

static void free_dtags(struct dtags *d)
{
    if (d->pattern) free(d->pattern);
    free(d);
}

static int verify_stringlist(strarray_t *sa, int (*verify)(char *))
{
    int i;

    for (i = 0 ; i < sa->count ; i++)
	if (!verify(sa->data[i]))
	    return 0;
    return 1;
}

char *addrptr;		/* pointer to address string for address lexer */
char addrerr[500];	/* buffer for address parser error messages */

static int verify_address(char *s)
{
    addrptr = s;
    addrerr[0] = '\0';	/* paranoia */
    if (addrparse()) {
	snprintf(errbuf, ERR_BUF_SIZE, 
		 "address '%s': %s", s, addrerr);
	yyerror(errbuf);
	return 0;
    }
    return 1;
}

static int verify_mailbox(char *s)
{
    if (!verify_utf8(s)) return 0;

    /* xxx if not a mailbox, call yyerror */
    return 1;
}

static int verify_header(char *hdr)
{
    char *h = hdr;

    while (*h) {
	/* field-name      =       1*ftext
	   ftext           =       %d33-57 / %d59-126         
	   ; Any character except
	   ;  controls, SP, and
	   ;  ":". */
	if (!((*h >= 33 && *h <= 57) || (*h >= 59 && *h <= 126))) {
	    snprintf(errbuf, ERR_BUF_SIZE,
		     "header '%s': not a valid header", hdr);
	    yyerror(errbuf);
	    return 0;
	}
	h++;
    }
    return 1;
}
 
static int verify_addrheader(char *hdr)
{
    const char **h, *hdrs[] = {
	"from", "sender", "reply-to",	/* RFC2822 originator fields */
	"to", "cc", "bcc",		/* RFC2822 destination fields */
	"resent-from", "resent-sender",	/* RFC2822 resent fields */
	"resent-to", "resent-cc", "resent-bcc",
	"return-path",			/* RFC2822 trace fields */
	"disposition-notification-to",	/* RFC2298 MDN request fields */
	"delivered-to",			/* non-standard (loop detection) */
	"approved",			/* RFC1036 moderator/control fields */
	NULL
    };

    if (!config_getswitch(IMAPOPT_RFC3028_STRICT))
	return verify_header(hdr);

    for (lcase(hdr), h = hdrs; *h; h++) {
	if (!strcmp(*h, hdr)) return 1;
    }

    snprintf(errbuf, ERR_BUF_SIZE,
	     "header '%s': not a valid header for an address test", hdr);
    yyerror(errbuf);
    return 0;
}
 
static int verify_envelope(char *env)
{
    lcase(env);
    if (!config_getswitch(IMAPOPT_RFC3028_STRICT) ||
	!strcmp(env, "from") || !strcmp(env, "to") || !strcmp(env, "auth")) {
	return 1;
    }

    snprintf(errbuf, ERR_BUF_SIZE,
	     "env-part '%s': not a valid part for an envelope test", env);
    yyerror(errbuf);
    return 0;
}
 
static int verify_relat(char *r)
{/* this really should have been a token to begin with.*/
	lcase(r);
	if (!strcmp(r, "gt")) {return GT;}
	else if (!strcmp(r, "ge")) {return GE;}
	else if (!strcmp(r, "lt")) {return LT;}
	else if (!strcmp(r, "le")) {return LE;}
	else if (!strcmp(r, "ne")) {return NE;}
	else if (!strcmp(r, "eq")) {return EQ;}
	else{
	  snprintf(errbuf, ERR_BUF_SIZE,
		   "flag '%s': not a valid relational operation", r);
	  yyerror(errbuf);
	  return -1;
	}
	
}




static int verify_flag(char *f)
{
    if (f[0] == '\\') {
	lcase(f);
	if (strcmp(f, "\\seen") && strcmp(f, "\\answered") &&
	    strcmp(f, "\\flagged") && strcmp(f, "\\draft") &&
	    strcmp(f, "\\deleted")) {
	    snprintf(errbuf, ERR_BUF_SIZE,
		     "flag '%s': not a system flag", f);
	    yyerror(errbuf);
	    return 0;
	}
	return 1;
    }
    if (!imparse_isatom(f)) {
	snprintf(errbuf, ERR_BUF_SIZE,
		 "flag '%s': not a valid keyword", f);
	yyerror(errbuf);
	return 0;
    }
    return 1;
}
 
#ifdef ENABLE_REGEX
static int verify_regex(char *s, int cflags)
{
    int ret;
    regex_t *reg = (regex_t *) xmalloc(sizeof(regex_t));

#ifdef HAVE_PCREPOSIX_H
    /* support UTF8 comparisons */
    cflags |= REG_UTF8;
#endif

    if ((ret = regcomp(reg, s, cflags)) != 0) {
	(void) regerror(ret, reg, errbuf, ERR_BUF_SIZE);
	yyerror(errbuf);
	free(reg);
	return 0;
    }
    free(reg);
    return 1;
}

static int verify_regexs(const strarray_t *sa, char *comp)
{
    int i;
    int cflags = REG_EXTENDED | REG_NOSUB;

    if (!strcmp(comp, "i;ascii-casemap")) {
	cflags |= REG_ICASE;
    }

    for (i = 0 ; i < sa->count ; i++) {
	if ((verify_regex(sa->data[i], cflags)) == 0)
	    return 0;
    }
    return 1;
}
#endif

/*
 * Valid UTF-8 check (from RFC 2640 Annex B.1)
 *
 * The following routine checks if a byte sequence is valid UTF-8. This
 * is done by checking for the proper tagging of the first and following
 * bytes to make sure they conform to the UTF-8 format. It then checks
 * to assure that the data part of the UTF-8 sequence conforms to the
 * proper range allowed by the encoding. Note: This routine will not
 * detect characters that have not been assigned and therefore do not
 * exist.
 */
static int verify_utf8(char *s)
{
    const char *buf = s;
    const char *endbuf = s + strlen(s);
    unsigned char byte2mask = 0x00, c;
    int trailing = 0;  /* trailing (continuation) bytes to follow */

    while (buf != endbuf) {
	c = *buf++;
	if (trailing) {
	    if ((c & 0xC0) == 0x80) {		/* Does trailing byte
						   follow UTF-8 format? */
		if (byte2mask) {		/* Need to check 2nd byte
						   for proper range? */
		    if (c & byte2mask)		/* Are appropriate bits set? */
			byte2mask = 0x00;
		    else
			break;
		}
		trailing--;
	    }
	    else
		break;
	}
	else {
	    if ((c & 0x80) == 0x00)		/* valid 1 byte UTF-8 */
		continue;
	    else if ((c & 0xE0) == 0xC0)	/* valid 2 byte UTF-8 */
		if (c & 0x1E) {			/* Is UTF-8 byte
						   in proper range? */
		    trailing = 1;
		}
		else
		    break;
	    else if ((c & 0xF0) == 0xE0) {	/* valid 3 byte UTF-8 */
		if (!(c & 0x0F)) {		/* Is UTF-8 byte
						   in proper range? */
		    byte2mask = 0x20;		/* If not, set mask
						   to check next byte */
		}
		trailing = 2;
	    }
	    else if ((c & 0xF8) == 0xF0) {	/* valid 4 byte UTF-8 */
		if (!(c & 0x07)) {		/* Is UTF-8 byte
						   in proper range? */
		    byte2mask = 0x30;		/* If not, set mask
						   to check next byte */
		}
		trailing = 3;
	    }
	    else if ((c & 0xFC) == 0xF8) {	/* valid 5 byte UTF-8 */
		if (!(c & 0x03)) {		/* Is UTF-8 byte
						   in proper range? */
		    byte2mask = 0x38;		/* If not, set mask
						   to check next byte */
		}
		trailing = 4;
	    }
	    else if ((c & 0xFE) == 0xFC) {	/* valid 6 byte UTF-8 */
		if (!(c & 0x01)) {		/* Is UTF-8 byte
						   in proper range? */
		    byte2mask = 0x3C;		/* If not, set mask
						   to check next byte */
		}
		trailing = 5;
	    }
	    else
		break;
	}
    }

    if ((buf != endbuf) || trailing) {
	snprintf(errbuf, ERR_BUF_SIZE,
		 "string '%s': not valid utf8", s);
	yyerror(errbuf);
	return 0;
    }

    return 1;
}
