/* bytecode.h -- bytecode definition
 */
/***********************************************************
        Copyright 1999 by Carnegie Mellon University

                      All Rights Reserved

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both that copyright notice and this permission notice appear in
supporting documentation, and that the name of Carnegie Mellon
University not be used in advertising or publicity pertaining to
distribution of the software without specific, written prior
permission.

CARNEGIE MELLON UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO
THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS, IN NO EVENT SHALL CARNEGIE MELLON UNIVERSITY BE LIABLE FOR
ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT
OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*****************************************************************/

#ifndef SIEVE_BYTECODE_H
#define SIEVE_BYTECODE_H

/*for finding correctly aligned bytes on strings*/
/* bump to the next multiple of 4 bytes */
#define ROUNDUP(num) (((num) + 3) & 0xFFFFFFFC)


/* yes, lots of these are superfluous, it's for clarity */
typedef union 
{
    int op; /* OPTYPE */
    int value;

    int jump;

    int listlen;

    /* store strings (need 2 consecutive bytecodes) */
    int len;
    char *str;
    char str_begin; /* For re-interpretation. */
} bytecode_t;


#define BYTECODE_VERSION 0x01

/* IMPORTANT: To maintain forward compatibility of bytecode, please only add
 * new instructions to the end of these enums.  (The reason these values
 * are all duplicated here is to avoid silliness if this caveat is forgotten
 * about in the other tables. */
enum bytecode {
    B_STOP,

    B_KEEP,
    B_DISCARD,
    B_REJECT,
    B_FILEINTO,
    B_REDIRECT,

    B_IF,
    B_IFELSE,

    B_MARK,
    B_UNMARK,

    B_ADDFLAG,
    B_SETFLAG,
    B_REMOVEFLAG,

    B_NOTIFY,
    B_DENOTIFY,

    B_VACATION,
    B_NULL
};

enum bytecode_comps {
    BC_FALSE,
    BC_TRUE,
    BC_NOT,
    BC_EXISTS,
    BC_SIZE,
    BC_ANYOF,
    BC_ALLOF,
    BC_ADDRESS,
    BC_ENVELOPE,
    BC_HEADER    
};

enum bytecode_tags {
    /* Address Part Tags */
    B_ALL,
    B_LOCALPART,
    B_DOMAIN,
    B_USER,  /* not required?*/
    B_DETAIL, /* not required?*/

    /* Sizes */
    B_OVER,
    B_UNDER,
    /*sizes, pt 2*/
    B_GT, /* not required*/
    B_GE, /* not required*/
    B_LT, /* not required*/
    B_LE, /* not required*/
    B_EQ, /* not required*/
    B_NE, /* not required*/
 
    /* Comparators */
    B_ASCIICASEMAP,
    B_OCTET,
    B_ASCIINUMERIC, /* not required*/
    
    /*match types*/
    B_IS,
    B_CONTAINS,
    B_MATCHES,
    B_REGEX,/* not required*/
    B_COUNT,/* not required*/
    B_VALUE /* not required*/

    /*priorities*/
    /*B_LOW
      B_MEDIUM 
      B_HIGH*/
};

#endif
