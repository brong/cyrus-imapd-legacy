/* bytecode.c -- sieve bytecode functions
 * Rob Siemborski
 * $Id: bytecode.c,v 1.1.2.2 2002/03/06 01:55:38 rjs3 Exp $
 */
/***********************************************************
        Copyright 2001 by Carnegie Mellon University

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
******************************************************************/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <string.h>
#include <md5global.h>
#include <md5.h>
#include <ctype.h>
#include <unistd.h>
#include <syslog.h>

#include "xmalloc.h"

#include "sieve_interface.h"
#include "interp.h"
#include "script.h"
#include "tree.h"
#include "sieve.h"
#include "message.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

/* yes, lots of these are superfluous, it's for clarity */
typedef union bytecode 
{
    int op; /* OPTYPE */
    int value;

    int jump;

    int listlen;

    /* store strings (need 2 consecutive bytecodes) */
    int len;
    char *str;
} bytecode_t;

struct bytecode_info 
{
    bytecode_t *data;
    size_t curlen;
    size_t reallen;
};

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
    B_FORWARD,

    B_IF,
    B_IFELSE,

    B_MARK,
    B_UNMARK,

    B_ADDFLAG,
    B_SETFLAG,
    B_REMOVEFLAG,

    B_NOTIFY,
    B_DENOTIFY,

    B_VACATION
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
    B_USER,
    B_DETAIL,

    /* Sizes */
    B_OVER,
    B_UNDER,
 
    /* Comparitors */
    B_IS,
    B_CONTAINS,
    B_MATCHES,
    B_REGEX
};


static int bc_test_generate(int codep, bytecode_info_t *retval, test_t *t);

static int atleast(bytecode_info_t *arr, size_t len) 
{
    if(arr->reallen < len) {
	arr->reallen = (len > arr->reallen * 2 ? len : arr->reallen * 2);
	arr->data = realloc(arr->data, arr->reallen*sizeof(bytecode_info_t));
	if(!arr->data) return 0;
    }
    
    return 1;
}

/* given a location and a string list, compile it in the form
 * <list len> <string len><string><string len><string> etc... */
static int bc_stringlist_generate(int codep, bytecode_info_t *retval,
				  stringlist_t *sl) 
{
    int len_codep = codep;
    int strcount = 0;
    stringlist_t *cur;
    
    codep++;

    /* Bounds check the string list length */
    if(!atleast(retval,codep+1)) return -1;

    for(cur=sl; cur; cur=cur->next) {
	strcount++;

	/* Bounds check for each string before we allocate it */
	if(!atleast(retval,codep+2)) return -1;
	retval->data[codep++].len = strlen(cur->s);
	retval->data[codep++].str = cur->s;
    }

    retval->data[len_codep].listlen = strcount;
    retval->curlen+=(2*strcount) + 1;
    return codep;
}

static int stringlist_len(int codep, bytecode_info_t *bc)
{
    int len = bc->data[codep++].len;
    int ret = sizeof(int);
    int i;

    for(i = 0;i < 2*len; i+=2) {
	ret += bc->data[codep+i].len;
    }

    return ret;
}

static int bc_testlist_generate(int codep, bytecode_info_t *retval, 
				testlist_t *tl) 
{
    int len_codep = codep;
    int testcount = 0;
    testlist_t *cur;
    
    codep++;

    /* Bounds check the test list length */
    if(!atleast(retval,codep+1)) return -1;
    retval->curlen++;
    
    for(cur=tl; cur; cur=cur->next) {
	int oldcodep = codep;

	/* Make room for tail marker */
	if(!atleast(retval,codep+1)) return -1;

	testcount++;
	codep = bc_test_generate(codep+1, retval, cur->t);

	retval->data[oldcodep].jump = codep;
	retval->curlen++;
    }

    retval->data[len_codep].listlen = testcount;
        
    return codep;
}

static int bc_test_generate(int codep, bytecode_info_t *retval, test_t *t)
{
    if(!retval) return -1;
    switch(t->type) {
	case STRUE:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_TRUE;
	    retval->curlen++;
	    return codep;

	case SFALSE:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_FALSE;
	    retval->curlen++;
	    return codep;

        case NOT:
        {
	    int safe_codep;
	
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = BC_NOT;

	    /* save a spot for the end location */
	    safe_codep = codep++;
	    retval->curlen+=2;
	    
	    codep = bc_test_generate(codep, retval, t->u.t);
	    retval->data[safe_codep].jump = codep;
	    return codep;
	}

	case SIZE:
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = BC_SIZE;
	    retval->data[codep++].value = (t->u.sz.t == OVER
					   ? B_OVER : B_UNDER);
	    retval->data[codep++].value = t->u.sz.n;
	    retval->curlen+=3;
	    return codep;

	case EXISTS:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_EXISTS;
	    retval->curlen++;
	    return bc_stringlist_generate(codep, retval, t->u.sl);

	case ANYOF:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_ANYOF;
	    retval->curlen++;
	    return bc_testlist_generate(codep, retval, t->u.tl);

	case ALLOF:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_ALLOF;
	    retval->curlen++;
	    return bc_testlist_generate(codep, retval, t->u.tl);

        case HEADER:
	    /* FIXME: not done */
	    /* header, comparitor type, headers, patterns */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = BC_HEADER;
	    switch(t->u.h.comptag) {
	        case IS:
		    retval->data[codep++].value = B_IS;
		    break;
      	        case CONTAINS:
		    retval->data[codep++].value = B_CONTAINS;
		    break;
	        case MATCHES:
		    retval->data[codep++].value = B_MATCHES;
		    break;
#ifdef ENABLE_REGEX
	        case REGEX:
		    retval->data[codep++].value = B_REGEX;
		    break;
#endif
	        default:
		    return -1;
	    }
	    retval->curlen+=2;	    
	    codep = bc_stringlist_generate(codep, retval, t->u.h.sl);
	    return bc_stringlist_generate(codep, retval, t->u.h.pl);	    

        case ADDRESS:
        case ENVELOPE:
	    /* FIXME: not done */
	    /* header, comparitor type, headers, patterns */
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = (t->type == ADDRESS)
		                         ? BC_ADDRESS : BC_ENVELOPE;
	    switch(t->u.h.comptag) {
	        case IS:
		    retval->data[codep++].value = B_IS;
		    break;
      	        case CONTAINS:
		    retval->data[codep++].value = B_CONTAINS;
		    break;
	        case MATCHES:
		    retval->data[codep++].value = B_MATCHES;
		    break;
#ifdef ENABLE_REGEX
	        case REGEX:
		    retval->data[codep++].value = B_REGEX;
		    break;
#endif
	        default:
		    return -1;
	    }
	    switch(t->u.ae.addrpart) {
	        case ALL:
		    retval->data[codep++].value = B_ALL;
		    break;
	        case LOCALPART:
		    retval->data[codep++].value = B_LOCALPART;
		    break;
	        case DOMAIN:
		    retval->data[codep++].value = B_DOMAIN;
		    break;
	        case USER:
		    retval->data[codep++].value = B_USER;
		    break;
	        case DETAIL:
		    retval->data[codep++].value = B_DETAIL;
		    break;
	        default:
		    return -1;
	    }
	    retval->curlen+=3;	    
	    codep = bc_stringlist_generate(codep, retval, t->u.h.sl);
	    return bc_stringlist_generate(codep, retval, t->u.h.pl);
	    
	default:
	    return -1;
    }
}

/* generate a not-quite-flattened bytecode */
/* returns address of next instruction */
/* needs current instruction, buffer for the code, and a current parse tree */
/* sieve is cool because everything is immediate! */
static int bc_generate(int codep, bytecode_info_t *retval, commandlist_t *c) 
{
    int jumploc,baseloc;

    if(!retval) return -1;
    do {
      switch(c->type) {
        case STOP:
	    /* STOP (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_STOP;
	    retval->curlen++;
	    break;
	case DISCARD:
	    /* DISCARD (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_DISCARD;
	    retval->curlen++;
	    break;
        case KEEP:
	    /* KEEP (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_KEEP;
	    retval->curlen++;
	    break;
        case MARK:
	    /* MARK (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_MARK;
	    retval->curlen++;
	    break;
        case UNMARK:
	    /* UNMARK (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_UNMARK;
	    retval->curlen++;
	    break;
	case DENOTIFY:
	    /* DENOTIFY (no arguments) */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_DENOTIFY;
	    retval->curlen++;
	    break;
        case REJCT:
	    /* REJECT (STRING: len + dataptr) */
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = B_REJECT;
	    retval->data[codep++].len = strlen(c->u.str);
	    retval->data[codep++].str = c->u.str;
	    retval->curlen+=3;
	    break;
	case FILEINTO:
	    /* FILEINTO stringlist */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = B_FILEINTO;
	    retval->curlen++;
	    codep = bc_stringlist_generate(codep,retval,c->u.sl);

	    if(codep == -1) return -1;
	    break;
	case FORWARD:
	    /* FORWARD stringlist */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = B_FORWARD;
	    retval->curlen++;
	    codep = bc_stringlist_generate(codep,retval,c->u.sl);

	    if(codep == -1) return -1;
	    break;
	case ADDFLAG:
	    /* ADDFLAG stringlist */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = B_ADDFLAG;
	    retval->curlen++;
	    codep = bc_stringlist_generate(codep,retval,c->u.sl);

	    if(codep == -1) return -1;
	    break;
	case SETFLAG:
	    /* SETFLAG stringlist */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = B_SETFLAG;
	    retval->curlen++;
	    codep = bc_stringlist_generate(codep,retval,c->u.sl);

	    if(codep == -1) return -1;
	    break;
        case REMOVEFLAG:
	    /* REMOVEFLAG stringlist */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = B_REMOVEFLAG;
	    retval->curlen++;
	    codep = bc_stringlist_generate(codep,retval,c->u.sl);

	    if(codep == -1) return -1;
	    break;
        case NOTIFY:
	    /* NOTIFY 
	     * (STRING: len + dataptr)/(STRING len + dataptr)/stringlist
	     * priority / message / headers_list */
	    if(!atleast(retval,codep+5)) return -1;
	    retval->data[codep++].op = B_NOTIFY;
	    retval->data[codep++].len = strlen(c->u.n.priority);
	    retval->data[codep++].str = c->u.n.priority;
	    retval->data[codep++].len = strlen(c->u.n.message);
	    retval->data[codep++].str = c->u.n.message;
	    retval->curlen+=5;
	    codep = bc_stringlist_generate(codep,retval,c->u.n.headers_list);

	    if(codep == -1) return -1;
	    break;
      case VACATION:
	   /* VACATION
	      STRING subject (if len is -1, then subject was NULL)
	      STRING message (again, len == -1 means subject was NULL)
	      VALUE days
	      VALUE mime
	      STRINGLIST addresses */

	    if(!atleast(retval,codep+7)) return -1;
	    retval->data[codep++].op = B_VACATION;
	    if(c->u.v.subject) {
	      retval->data[codep++].len = strlen(c->u.v.subject);
	      retval->data[codep++].str = c->u.v.subject;
            } else {
	      retval->data[codep++].len = -1;
	      retval->data[codep++].str = NULL;
	    }
	    if(c->u.v.message) {
	      retval->data[codep++].len = strlen(c->u.v.message);
	      retval->data[codep++].str = c->u.v.message;
            } else {
	      retval->data[codep++].len = -1;
	      retval->data[codep++].str = NULL;
	    }
            retval->data[codep++].value = c->u.v.days;
            retval->data[codep++].value = c->u.v.mime;
	    retval->curlen+=7;
	    codep = bc_stringlist_generate(codep,retval,c->u.n.headers_list);

	    if(codep == -1) return -1;
	    break;
      case IF:
	    /* IF (test / codep else / codep done) */
	    baseloc = codep;

	    /* Allocate operator + jump table offsets */
	    if(!atleast(retval,codep+3)) return -1;

	    if(c->u.i.do_else) {
	        jumploc = codep+4;
		/* we need an extra */
		if(!atleast(retval,jumploc)) return -1;
	        retval->curlen+=4;
	        retval->data[codep++].op = B_IFELSE;
	    } else {
		jumploc = codep+3;
	        retval->curlen+=3;
	    	retval->data[codep++].op = B_IF;
	    }

	    /* offset to if code */
	    retval->data[codep].jump = 
		bc_test_generate(jumploc,retval,c->u.i.t);
	    codep++;
	    if(retval->data[codep-1].jump == -1) return -1;

	    /* find then code and offset to else code,
	     * we want to write this code starting at the offset we
	     * just found */
	    retval->data[codep].jump =
		bc_generate(retval->data[codep-1].jump, retval,
			    c->u.i.do_then);
	    if(retval->data[codep].jump == -1) return -1;

	    /* write else code */
	    if(c->u.i.do_else) {
		codep++;
		retval->data[codep].jump =
		    bc_generate(retval->data[codep-1].jump, retval,
				c->u.i.do_else);
		codep++;
		if(retval->data[codep-1].jump == -1) return -1;

		/* Update code pointer to end of else code */
		codep = retval->data[codep-1].jump;
	    } else {
		/* Update code pointer to end of then code */
		codep = retval->data[codep].jump;
	    }

	    break;
      default:
	    return -1;
      }

      /* generate from next command */
      c = c->next;
    } while(c);

    return codep;
}

/* Pad null bytes onto the end of the string we just wrote */
/* returns -1 on failure or number of bytes written on success */
static int align_string(int fd, int string_len) 
{
    /* Keep in mind that we always have to pad a string with *atleast*
     * one zero, that's why sometimes we have to pad with 4 */
    int needed = sizeof(int) - (string_len % sizeof(int));
    int i;
    
    for(i = 0; i < needed; i++) {
	if(write(fd, "\0", 1) == -1) return -1;
    }

    return needed;
}

/* Write out a stringlist to a given file descriptor.
 * return # of bytes written on success and -1 on error */
static int emit_stringlist(int fd, int *codep, bytecode_info_t *bc) 
{
    int len = bc->data[(*codep)++].len;
    int i;
    int ret;
    int wrote = sizeof(int);

    /* Write out number of items in the list */
    ret = write(fd, &len, sizeof(int));
    if(ret == -1) return 0;

    /* Loop through all the items of the list, writing out lenght and string
     * in sequence */
    for(i=0; i < len; i++) {
	int datalen = bc->data[(*codep)++].len;

	if(write(fd, &datalen, sizeof(int)) == -1) return 0;
	wrote += sizeof(int);
	
	if(write(fd, bc->data[(*codep)++].str, datalen) == -1) return 0;
	wrote += datalen;

	ret = align_string(fd,datalen);
	if(ret == -1) return -1;
	
	wrote+=ret;
    }

    return wrote;
}

static int emit_bytecode_test(int fd, int codep, bytecode_info_t *bc);

/* Write out a testlist to a given file descriptor.
 * return # of bytes written on success and -1 on error */
static int emit_testlist(int fd, int *codep, bytecode_info_t *bc) 
{
    int len = bc->data[(*codep)++].len;
    int i;
    int ret;
    int wrote = sizeof(int);

    /* Write out number of items in the list */
    ret = write(fd, &len, sizeof(int));
    if(ret == -1) return -1;

    /* Loop through all the items of the list, writing out each
     * test as we reach it in sequence. */
    for(i=0; i < len; i++) {
	int nextcodep = bc->data[(*codep)++].jump;
	
	ret = emit_bytecode_test(fd, *codep, bc);
	if(ret == -1) return -1;
	
	wrote+=ret;
	*codep = nextcodep;
    }

    return wrote;
}

/* emit the bytecode for a test.  returns -1 on failure or size of
 * emitted bytecode on success */
static int emit_bytecode_test(int fd, int codep, bytecode_info_t *bc) 
{
    int filelen = 0; /* Relative offset to account for interleaved strings */
    int ret; /* Temporary Return Value Variable */
    
    /* Output this opcode */
    if(write(fd, &bc->data[codep].op, sizeof(bc->data[codep].op)) == -1)
	return -1;
    
    filelen += sizeof(int);

    switch(bc->data[codep++].op) {
        case BC_TRUE:
        case BC_FALSE:
	    /* No parameter opcodes */
	    break;

        case BC_NOT:
	{
	    /* Single parameter: another test */
	    ret = emit_bytecode_test(fd, codep, bc);
	    if(ret != -1)
		filelen+=ret;
	    else
		return ret;
	    break;
	}
	
        case BC_ALLOF:
        case BC_ANYOF:
	    /* Just drop a testlist */
	    ret = emit_testlist(fd, &codep, bc);
	    if(ret != -1)
		filelen+=ret;
	    else
		return ret;
	    break;

        case BC_SIZE:
	    /* Drop tag and number */
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
		return -1;
	    if(write(fd, &bc->data[codep+1].value,
		     sizeof(bc->data[codep+1].value)) == -1)
		return -1;
    
	    filelen += 2 * sizeof(int);
	    codep += 2;
	    break;

        case BC_EXISTS:
        {
	    int ret;
	    ret = emit_stringlist(fd, &codep, bc);
	    if(ret < 0) return -1;
	    filelen += ret;
	    break;
	}

        case BC_HEADER:
        {
	    int ret;
	    /* Drop comparitor */
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
		return -1;
	    filelen += sizeof(int);
	    codep++;
	    /* Now drop headers */
	    ret = emit_stringlist(fd, &codep, bc);
	    if(ret < 0) return -1;
	    filelen+=ret;
	    /* Now drop data */
	    ret = emit_stringlist(fd, &codep, bc);
	    if(ret < 0) return -1;
	    filelen+=ret;
	    break;
        }

        case BC_ADDRESS:
        case BC_ENVELOPE:
        {
	    int ret;
	    /* Drop Comparitor & type */
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
		return -1;
	    if(write(fd, &bc->data[codep+1].value,
		     sizeof(bc->data[codep+1].value)) == -1)
		return -1;
	    filelen += 2*sizeof(int);
	    codep += 2;
	    /* Now drop headers */
	    ret = emit_stringlist(fd, &codep, bc);
	    if(ret < 0) return -1;
	    filelen+=ret;
	    /* Now drop data */
	    ret = emit_stringlist(fd, &codep, bc);
	    if(ret < 0) return -1;
	    filelen+=ret;
	    break;
	}

        default:
	    /* Unknown testcode? */
	    return -1;
    }

    return filelen;
}

/* emit the bytecode to a file descriptor given a flattened parse tree
 * returns -1 on failure, size of emitted bytecode on success.
 *
 * this takes care of everything except the comparisons */
static int emit_bytecode_act(int fd, int codep, int stopcodep,
			     bytecode_info_t *bc, int filelen) 
{
    int len; /* Temporary Length Variable */
    int ret; /* Temporary Return Value Variable */
    int start_filelen = filelen;
    int i;

    syslog(LOG_ERR, "entered with filelen: %d", filelen);
    
    /* All non-string data MUST be sizeof(int)
       byte alligned so the end of each string may require a pad */
    /*
     * Note that for purposes of jumps you must multiply codep by sizeof(int)
     */
    while(codep < stopcodep) {
	/* Output this opcode */
	if(write(fd, &bc->data[codep].op, sizeof(bc->data[codep].op)) == -1)
	    return -1;

	filelen+=sizeof(int);

	switch(bc->data[codep++].op) {
	    case B_IF: 
	    {
		int teststart, testend, realend, testdist, enddist;

		/* first skip 2 words so we can write in offsets later */
		ret = lseek(fd, 2 * sizeof(int), SEEK_CUR);
		if(ret == -1) return ret;

		/* save location of 2 offsets */
		testend = teststart = filelen;
		testend += 2 * sizeof(int);

		/* spew the test */
		testdist = emit_bytecode_test(fd, codep+2, bc);
		if(testdist == -1)
		    return -1;
		testend += testdist;
		
		realend = testend;
		/* spew the then code */
		enddist = emit_bytecode_act(fd, bc->data[codep].value,
					    bc->data[codep+1].value, bc,
					    filelen + testdist + 2*sizeof(int));
		realend += enddist;
		
		/* now, jump back to the two offset locations and write them */
		if(lseek(fd, teststart, SEEK_SET) == -1)
		    return -1;
		if(write(fd,&testend,sizeof(testend)) == -1)
		    return -1;
		if(write(fd,&realend,sizeof(realend)) == -1)
		    return -1;
		if(lseek(fd,realend,SEEK_SET) == -1)
		    return -1;

		codep = bc->data[codep+1].value;

		/* update file length to the length of the test and the
		 * then code, plus the 2 offsets we need. */
		filelen += testdist + enddist + 2*sizeof(int);

		break;
	    }
	    case B_IFELSE:
	    {
		int teststart, testend, thenend, realend,
		               testdist, thendist, enddist;

		/* first skip 3 words so we can write in offsets later */
		ret = lseek(fd, 3 * sizeof(int), SEEK_CUR);
		if(ret == -1) return ret;

		/* save location of 3 offsets */
		testend = teststart = filelen;
		testend += 3 * sizeof(int);

		/* spew the test */
		testdist = emit_bytecode_test(fd, codep+3, bc);
		if(testdist == -1)
		    return -1;
		testend += testdist;
		
		thenend = testend;
		/* spew the then code */
		thendist = emit_bytecode_act(fd, bc->data[codep].value,
					     bc->data[codep+1].value, bc,
					     filelen + testdist + 3*sizeof(int));
		thenend += thendist;

		realend = thenend;
		/* spew the else code */
		enddist = emit_bytecode_act(fd, bc->data[codep+1].value,
					    bc->data[codep+2].value, bc,
					    filelen + testdist + thendist
					      + 3*sizeof(int));
		realend += enddist;
		
		/* now, jump back to the two offset locations and write them */
		if(lseek(fd, teststart+sizeof(int), SEEK_SET) == -1)
		    return -1;
		if(write(fd,&testend,sizeof(testend)) == -1)
		    return -1;
		if(write(fd,&thenend,sizeof(testend)) == -1)
		    return -1;
		if(write(fd,&realend,sizeof(realend)) == -1)
		    return -1;
		if(lseek(fd,realend,SEEK_SET) == -1)
		    return -1;

		codep = bc->data[codep+2].value;

		/* update file length to the length of the test and the
		 * then code, plus the 2 offsets we need. */
		filelen += testdist + thendist + enddist + 3*sizeof(int);

		break;
	    }

	    case B_REJECT:
		len = bc->data[codep++].len;
		if(write(fd,&len,sizeof(len)) == -1)
		    return -1;
		filelen+=sizeof(int);

       		if(write(fd,bc->data[codep++].str,len) == -1)
		    return -1;
		filelen+=sizeof(int);

		ret = align_string(fd, len);
		if(ret == -1) return -1;
		
		filelen += len + ret;
	        break; 

	    case B_FILEINTO:
	    case B_FORWARD:
	    case B_SETFLAG:
	    case B_ADDFLAG:
	    case B_REMOVEFLAG:
		/* Dump just a stringlist */
		ret = emit_stringlist(fd, &codep, bc);
		if(ret < 0) return -1;
		filelen += ret;
		break;

	    case B_NOTIFY:
		/* Priority String, Message String */
		/* In other words, the same thing twice */
		for(i=0; i<2; i++) {
		    len = bc->data[codep++].len;
		    if(write(fd,&len,sizeof(len)) == -1)
			return -1;
		    filelen += sizeof(int);

       		    if(write(fd,bc->data[codep++].str,len) == -1)
			return -1;
		    
		    ret = align_string(fd, len);
		    if(ret == -1) return -1;
		
		    filelen += len + ret;
		}
	        break;

	    case B_VACATION:
		/* Subject String, Message String, Days (word), Mime (word) */
		for(i=0; i<2; i++) {
		    len = bc->data[codep++].len;
		    if(write(fd,&len,sizeof(len)) == -1)
			return -1;
		    filelen += sizeof(int);
		    
		    if(len == -1) {
			/* this is a nil string */
			/* skip the null pointer and make up for it 
			 * by adjusting the offset */
			codep++;
			continue;
		    }

       		    if(write(fd,bc->data[codep++].str,len) == -1)
			return -1;
		    filelen += sizeof(int);

		    ret = align_string(fd, len);
		    if(ret == -1) return -1;
		
		    filelen += len + ret;
		}
		if(write(fd,&bc->data[codep++].value,
			 sizeof(bc->data[codep++].value)) == -1)
		   return -1;
		filelen += sizeof(int);
		if(write(fd,&bc->data[codep++].value,
			 sizeof(bc->data[codep++].value)) == -1)
		   return -1;
		filelen += sizeof(int);
		break;

	    case B_STOP:
	    case B_DISCARD:
	    case B_KEEP:
	    case B_MARK:
	    case B_UNMARK:
	    case B_DENOTIFY:
		/* No Parameters! */
		break;

	    default:
	        /* Unknown opcode? */
	        return -1;
	}
    }
    return filelen - start_filelen;
}

/* spew the bytecode to disk */
int sieve_emit_bytecode(int fd, bytecode_info_t *bc)  
{
    /* First output version number (4 bytes) */
    int data = BYTECODE_VERSION;
    
    if(write(fd, &data, sizeof(data)) == -1)
	return -1;

    return emit_bytecode_act(fd, 0, bc->curlen, bc, 0);
}

#if 0
#include <errno.h>
#endif

/* Entry point to the bytecode emitter module */	
int sieve_generate_bytecode(bytecode_info_t **retval, sieve_script_t *s) 
{
    commandlist_t *c;

    if(!retval) return -1;
    if(!s) return -1;
    c = s->cmds;
    if(!c) return -1;
    
    *retval = xmalloc(sizeof(bytecode_info_t));
    if(!(*retval)) return -1;

    memset(*retval, 0, sizeof(bytecode_info_t));

    return bc_generate(0, *retval, c);
/*    if(ret == -1) return -1; */
#if 0    
    fd = open("foo.bc",O_CREAT | O_TRUNC | O_WRONLY);
    if(fd == -1) {
	printf("no opening foo.bc");
	return -1;
    }
    
    ret = emit_bytecode(fd, *retval);
    if(ret == -1) {
	printf("eb error: %s\n",strerror(errno));
    } else {
	printf("emitted %d bytes\n", ret);
    }
    return ret;
#endif  
}

void sieve_free_bytecode(bytecode_info_t **p) 
{
    if(!p || !*p) return;
    if((*p)->data) free((*p)->data);
    free(*p);
    *p = NULL;
}
    

#if 0

/* Dump a stringlist.  Return the last address used by the list */
static int dump_sl(bytecode_info_t *d, int ip) 
{
    int numstr = d->data[ip].listlen;
    int i;
    
    for(i=0; i<numstr; i++) {
	printf(" {%d}",d->data[++ip].len);
	printf("%s\n",d->data[++ip].str);
    }
    
    return ip;
}

static int dump_test(bytecode_info_t *d, int ip);

/* Dump a testlist.  Return the last address used by the list */
static int dump_tl(bytecode_info_t *d, int ip) 
{
    int numtest = d->data[ip].listlen;
    int i;
    
    for(i=0; i<numtest; i++) {
	printf(" (until %d)\n", d->data[++ip].jump);
	ip = dump_test(d, ++ip);
    }
    
    return ip;
}

/* Dump a test, return the last address used by the test */
static int dump_test(bytecode_info_t *d, int ip) {
    switch(d->data[ip].op) {
	case BC_TRUE:
	    printf("%d: TRUE\n",ip);
	    break;

	case BC_FALSE:
	    printf("%d: FALSE\n",ip);
	    break;

	case BC_NOT:
	    printf("%d: NOT TEST(\n",ip++);
	    printf("  (until %d)\n", d->data[ip++].jump);
	    ip = dump_test(d,ip);
	    printf("    )\n");
	    break;

	case BC_SIZE:
	    printf("%d: SIZE TAG(%d) NUM(%d)\n",ip,
		   d->data[ip+1].value, d->data[ip+2].value);
	    ip+=2;
	    break;

	case BC_EXISTS:
	    printf("%d: EXISTS\n",ip++);
	    ip = dump_sl(d,ip);
	    break;

        case BC_ALLOF:
	    printf("%d: ALLOF (\n",ip++);
	    ip = dump_tl(d,ip);
	    printf(")\n");
	    break;

        case BC_ANYOF:
	    printf("%d: ANYOF (\n",ip++);
	    ip = dump_tl(d,ip);
	    printf(")\n");
	    break;

        case BC_HEADER:
	    printf("%d: HEADER (\n",ip++);
	    printf("      COMP:%d HEADERS:\n",d->data[ip++]);
	    ip = dump_sl(d,ip); ip++;
	    printf("      DATA:\n");
	    ip = dump_sl(d,ip);
	    break;

        case BC_ADDRESS:
        case BC_ENVELOPE:
	    printf("%d: %s (\n",ip+1,
		   d->data[ip].op == BC_ADDRESS ? "ADDRESS" : "ENVELOPE");
	    ip++;
	    printf("      COMP:%d TYPE:%d HEADERS:\n",
		   d->data[ip+1],d->data[ip+2]);
	    ip+=2;
	    ip = dump_sl(d,ip); ip++;
	    printf("      DATA:\n");
	    ip = dump_sl(d,ip);
	    break;

	default:
	    printf("%d: TEST(%d)\n",ip,d->data[ip].op);
	    break;
    }

    return ip;
}

void dump(bytecode_info_t *d) 
{
    int i, j;
    
    if(!d) return;
    
    for(i=0; i<d->curlen; i++) {
	switch(d->data[i].op) {
	case B_REJECT:
	    printf("%d: REJECT {%d}%s\n",i,
		   d->data[i+1].len,d->data[i+2].str);
	    i+=2;
	    break;
	    
	case B_IF:
	    printf("%d: IF THEN(%d) POST(%d) TEST(\n",i,
		   d->data[i+1].jump,d->data[i+2].jump);
	    i = dump_test(d,i+3);
	    printf(")\n");
	    break;

	case B_IFELSE:
	    printf("%d: IF THEN(%d) ELSE(%d) POST(%d) TEST(\n",i,
		   d->data[i+1].jump,d->data[i+2].jump,
		   d->data[i+3].jump);
	    i = dump_test(d,i+4);
	    printf(")\n");
	    break;

	case B_STOP:
	    printf("%d: STOP\n",i);
	    break;

	case B_DISCARD:
	    printf("%d: DISCARD\n",i);
	    break;
	    
	case B_KEEP:
	    printf("%d: KEEP\n",i);
	    break;

	case B_MARK:
	    printf("%d: MARK\n",i);
	    break;

	case B_UNMARK:
	    printf("%d: UNMARK\n",i);
	    break;

	case B_FILEINTO:
	    printf("%d: FILEINTO\n",i);
	    i=dump_sl(d,++i);
	    break;

	case B_FORWARD:
	    printf("%d: FORWARD\n",i);
	    i=dump_sl(d,++i);
	    break;

	case B_SETFLAG:
	    printf("%d: SETFLAG\n",i);
	    i=dump_sl(d,++i);
	    break;

	case B_ADDFLAG:
	    printf("%d: ADDFLAG\n",i);
	    i=dump_sl(d,++i);
	    break;

	case B_REMOVEFLAG:
	    printf("%d: REMOVEFLAG\n",i);
	    i=dump_sl(d,++i);
	    break;

	case B_DENOTIFY:
	    printf("%d: DENOTIFY\n",i);
	    break;

	case B_NOTIFY:
	    printf("%d: NOTIFY PRIORITY({%d}%s) MESSAGE({%d}%s)\n",i,
		   d->data[i+1].len,d->data[i+2].str,
		   d->data[i+3].len,d->data[i+4].str);
	    i+=5;
	    i=dump_sl(d,i);
	    break;

	case B_VACATION:
	    printf("%d: VACATION SUBJ({%d}%s) MESG({%d}%s) DAYS(%d) MIME(%d)\n", i,
		   d->data[i+1].len, (d->data[i+1].len == -1 ? "[nil]" : d->data[i+2].str),
		   d->data[i+3].len, (d->data[i+3].len == -1 ? "[nil]" : d->data[i+4].str),
		   d->data[i+5].value, d->data[i+6].value);
	    i+=7;
	    i=dump_sl(d,i);
	    break;

	default:
	    printf("%d: %d\n",i,d->data[i].op);
	    break;
	}
    }
    printf("full len is: %d\n", d->curlen);
}
#endif
