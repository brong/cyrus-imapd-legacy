/* bytecode.c -- sieve bytecode functions
 * Rob Siemborski
 * $Id: bytecode.c,v 1.1.2.19 2003/01/10 17:03:24 jsmith2 Exp $
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

#include "bytecode.h"
#include "comparator.h"
 


#define DUMPCODE 0
#define VERBOSE 0

#if DUMPCODE
void dump(bytecode_info_t *d);
#endif


struct bytecode_info 
{
    bytecode_t *data;
    size_t curlen;
    size_t reallen;
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
	if (cur->s!=NULL)
	  /* Bounds check for each string before we allocate it */
	if(!atleast(retval,codep+2)) return -1;
	retval->data[codep++].len = strlen(cur->s);
	retval->data[codep++].str = cur->s;
    }
 
    retval->data[len_codep].listlen = strcount;
    retval->curlen+=(2*strcount) + 1;
    return codep;
}


/*this is used by notify to pass the options list*/
char ** bc_makeArray(int len, int i, bytecode_t *bc) 
{ 
  int x;
  char** array;
  array=(char**)xmalloc(len);
  for (x=0; x<len; x++)
    {
      array[x]=(char*)xmalloc(bc[i].len);
      strncpy(array[x], (char*)&(bc[i+1].str), bc[i].len); 
    }
  
  return array;
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

static int bc_relation_generate(int codep, bytecode_info_t *retval, int relat)
{
 
  switch (relat)
    {
    case GT:
      retval->data[codep].value= B_GT;
      break;
    case GE:
      retval->data[codep].value= B_GE;
      break; 
    case LT:
      retval->data[codep].value= B_LT;
      break;
    case LE:
      retval->data[codep].value= B_LE;
      break;
    case EQ:
      retval->data[codep].value= B_EQ;
      break;
    case NE:
      retval->data[codep].value= B_NE;
      break;
    default:
      retval->data[codep].value=  -1;
    }
  retval->curlen++;
  return 0;
}



static int bc_test_generate(int codep, bytecode_info_t *retval, test_t *t)
{
    if(!retval) return -1;
    switch(t->type) {
    case STRUE:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_TRUE;
	    retval->curlen++;
	    break;
    case SFALSE:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_FALSE;
	    retval->curlen++;
	    break;
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
	    break;
	}

    case SIZE:
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = BC_SIZE;
	    retval->data[codep++].value = (t->u.sz.t == OVER
					   ? B_OVER : B_UNDER);
	    retval->data[codep++].value = t->u.sz.n;
	    retval->curlen+=3;
	    break;

    case EXISTS:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_EXISTS;
	    retval->curlen++;
	    codep= bc_stringlist_generate(codep, retval, t->u.sl);
	    break;
    case ANYOF:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_ANYOF;
	    retval->curlen++;
	    codep=bc_testlist_generate(codep, retval, t->u.tl);
	    break;
    case ALLOF:
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = BC_ALLOF;
	    retval->curlen++;
	    codep= bc_testlist_generate(codep, retval, t->u.tl);
	    break;
    case HEADER:
	    /* FIXME: not done */
	    /* header, comparitor type, headers, patterns */
	    if(!atleast(retval,codep+2)) return -1;
	    retval->data[codep++].op = BC_HEADER;
	    switch(t->u.h.comptag) {
	        case IS: 
		   retval->data[codep++].value = B_IS; 	 break;
	        case CONTAINS:
		  retval->data[codep++].value = B_CONTAINS; break;
	        case MATCHES:
		  retval->data[codep++].value = B_MATCHES;  break;
#ifdef ENABLE_REGEX
	        case REGEX:
		  retval->data[codep++].value = B_REGEX;  break;
#endif
	        case COUNT:
		  retval->data[codep++].value = B_COUNT; break;
	        case VALUE:
		  retval->data[codep++].value = B_VALUE; break;
	        default:
		  return -1;
	    }
	    /*relation*/
	    bc_relation_generate(codep++, retval, t->u.h.relation);
	    /*comparator*/
	    if (!strcmp (t->u.h.comparator, "i;octet"))
	      retval->data[codep++].value = B_OCTET;
	    else if (!strcmp (t->u.h.comparator, "i;ascii-casemap"))
	      retval->data[codep++].value = B_ASCIICASEMAP;
	    else if (!strcmp (t->u.h.comparator, "i;ascii-numeric"))
	      retval->data[codep++].value = B_ASCIINUMERIC;

	    retval->curlen+=3;	    
	    codep = bc_stringlist_generate(codep, retval, t->u.h.sl);
	    codep=bc_stringlist_generate(codep, retval, t->u.h.pl);
	    break;
    case ADDRESS:
    case ENVELOPE:
	    /* FIXME: not done */
	    /* header, comparitor type, headers, patterns */
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = (t->type == ADDRESS)
		                         ? BC_ADDRESS : BC_ENVELOPE;
	    switch(t->u.ae.comptag) {
	        case IS:
		    retval->data[codep++].value = B_IS;break;
      	        case CONTAINS:
		    retval->data[codep++].value = B_CONTAINS;break;
	        case MATCHES:
		    retval->data[codep++].value = B_MATCHES; break;
		    break;
#ifdef ENABLE_REGEX
	        case REGEX:
		    retval->data[codep++].value = B_REGEX; break;
#endif
	        case COUNT:
		   retval->data[codep++].value = B_COUNT; break;
	    case VALUE:
		   retval->data[codep++].value = B_VALUE;break;
	        default:
		    return -1;
	    }
	    /*relation*/
	    bc_relation_generate(codep++, retval, t->u.ae.relation);
	    /*comparator*/
	    if (!strcmp (t->u.ae.comparator, "i;octet"))
	      retval->data[codep++].value = B_OCTET;
	    else if (!strcmp (t->u.ae.comparator, "i;ascii-casemap"))
	      retval->data[codep++].value = B_ASCIICASEMAP;
	    else if (!strcmp (t->u.ae.comparator, "i;ascii-numeric"))
	      retval->data[codep++].value = B_ASCIINUMERIC;
	    /*address part*/
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
	    retval->curlen+=4;	    
	    codep = bc_stringlist_generate(codep, retval, t->u.h.sl);
	    codep = bc_stringlist_generate(codep, retval, t->u.h.pl);
	    break;
    default:
      return -1;
      
    }
    return codep;
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
	    /* DENOTIFY  */
	    if(!atleast(retval,codep+1)) return -1;
	    retval->data[codep++].op = B_DENOTIFY;
	    switch(c->u.d.comptag) {
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
	    retval->data[codep++].len = strlen(c->u.d.pattern);
	    retval->data[codep++].str = c->u.d.pattern;

	    retval->data[codep++].len = strlen(c->u.d.priority);
	    retval->data[codep++].str = (c->u.d.priority);

	    retval->curlen+=6;
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
	    /* FILEINTO (STRING: len + dataptr) */
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = B_FILEINTO;
	    retval->data[codep++].len = strlen(c->u.str);
	    retval->data[codep++].str = c->u.str;
	    retval->curlen+=3;
	    break;
	case REDIRECT:
	    /* REDIRECT (STRING: len + dataptr) */
	    if(!atleast(retval,codep+3)) return -1;
	    retval->data[codep++].op = B_REDIRECT;
	    retval->data[codep++].len = strlen(c->u.str);
	    retval->data[codep++].str = c->u.str;
	    retval->curlen+=3;
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
	     * (STRING: len + dataptr)/(STRING len + dataptr)/stringlist/(STRING: len + dataptr)/(STRING len + dataptr)
	     *method/id /options list/priority/message */
	    if(!atleast(retval,codep+9)) return -1;
	    retval->data[codep++].op = B_NOTIFY;
	    retval->data[codep++].len = strlen(c->u.n.method);
	    retval->data[codep++].str = c->u.n.method;
	    retval->data[codep++].len = strlen(c->u.n.id);
	    retval->data[codep++].str = c->u.n.id;
	    retval->curlen+=5;
	    codep = bc_stringlist_generate(codep,retval,c->u.n.options);
	    /*	    if(codep == -1) return -1;*/
	    retval->data[codep++].len = strlen(c->u.n.priority);
	    retval->data[codep++].str = c->u.n.priority;
	    retval->data[codep++].len = strlen(c->u.n.message);
	    retval->data[codep++].str = c->u.n.message;
	    retval->curlen+=4;
	    break;
      case VACATION:
	   /* VACATION
	      STRINGLIST addresses
	      STRING subject (if len is -1, then subject was NULL)
	      STRING message (again, len == -1 means subject was NULL)
	      VALUE days
	      VALUE mime
	    */

	    if(!atleast(retval,codep+7)) return -1;
	    retval->data[codep++].op = B_VACATION;

	    codep = bc_stringlist_generate(codep,retval,c->u.v.addresses);

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


	    if(codep == -1) return -1;
	    break;
      case IF:
	{int jumpVal; /* do not remove this variable. 
			 the function test_generate might change the value 
			 of retval and this makes things unhappy*/

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
	    
	    jumpVal= bc_test_generate(jumploc,retval,c->u.i.t);
	    if(jumpVal == -1) 
	      {return -1;}
	    else 
	      {retval->data[codep].jump = jumpVal;
	      codep++;}
	    
	    /* find then code and offset to else code,
	     * we want to write this code starting at the offset we
	     * just found */
	
	    jumpVal= bc_generate(jumpVal,retval, c->u.i.do_then);
	    if(jumpVal == -1) 
	      {return -1;}
	    else 
	      {retval->data[codep].jump = jumpVal;
	      }
	    
	    /* write else code */
	    if(c->u.i.do_else) {
	      codep++;
	      
	      jumpVal= bc_generate(jumpVal,retval, c->u.i.do_else);
	      if(jumpVal == -1) 
		{return -1;}
	      else 
		{retval->data[codep].jump = jumpVal;
		codep++;
		}
	      
	      
	      /* Update code pointer to end of else code */
	      codep = retval->data[codep-1].jump;
	    } else {
	      /* Update code pointer to end of then code */
	      codep = retval->data[codep].jump;
	    }
	    
	    break;
	}
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
    /* Keep in mind that we always want to pad a string with *atleast*
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
    int wrote = 2*sizeof(int);
   int begin,end;
    /* Write out number of items in the list */
    ret = write(fd, &len, sizeof(int));
    if(ret == -1) return 0;

    begin=lseek(fd,0,SEEK_CUR);
    lseek(fd,sizeof(int),SEEK_CUR);

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
    end=lseek(fd,0,SEEK_CUR);
 

    lseek(fd,begin,SEEK_SET);
    if(write(fd, &end, sizeof(int)) == -1) return 0;
    lseek(fd,end,SEEK_SET);
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
{/*general opinion is that the 4 makes no sense*/
  int filelen=0;/* = 4; *//* Relative offset to account for interleaved strings */
 

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
	  { codep++;
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
	  /*where we jump to?*/
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
	    /* Drop match type and comparator */
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
		return -1;
	    if(write(fd, &bc->data[codep+1].value,
		     sizeof(bc->data[codep+1].value)) == -1)
		return -1;
	    filelen += 2*sizeof(int);
	    codep += 2;    
	    /*now drop relation*/
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
	    /* Drop match type and Comparator  */
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
		return -1;
	    if(write(fd, &bc->data[codep+1].value,
		     sizeof(bc->data[codep+1].value)) == -1)
		return -1;
	    filelen += 2*sizeof(int);
	    codep += 2;    
	    /*now drop relation*/
	    if(write(fd, &bc->data[codep].value,
		     sizeof(bc->data[codep].value)) == -1)
	      return -1;
	    filelen += sizeof(int);
	    codep++;
	    /*now drop address part*/
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

    /*debugging variable to check filelen*/
    int location;

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
		if(lseek(fd, filelen, SEEK_SET) == -1)
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
		location=lseek(fd,0,SEEK_CUR);

		testdist = emit_bytecode_test(fd, codep+3, bc);
		if(testdist == -1)
		    return -1;
		testend += testdist;
		location=lseek(fd,0,SEEK_CUR);

		thenend = testend;
		/* spew the then code */ 
		thendist = emit_bytecode_act(fd, bc->data[codep].value,
					     bc->data[codep+1].value, bc,
					     filelen + testdist + 3*sizeof(int));
		/*thendist-=sizeof(int);*/
		thenend += thendist;
	
		realend = thenend;
		/* spew the else code */
		enddist = emit_bytecode_act(fd, bc->data[codep+1].value,
					    bc->data[codep+2].value, bc,
					    filelen + testdist + thendist
					      + 3*sizeof(int));
		realend += enddist;
		


		/* now, jump back to the two offset locations and write them */
		if(lseek(fd, filelen, SEEK_SET) == -1)
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
		 * then code, plus the 3 offsets we need. */
		filelen += testdist  +thendist + enddist + 3*sizeof(int);
	
       		break;
	    }

	    case B_REJECT:
	    case B_FILEINTO:
	    case B_REDIRECT:
	      /*just a string*/
	      len = bc->data[codep++].len;
		if(write(fd,&len,sizeof(len)) == -1)
		    return -1;
		filelen+=sizeof(int);

		if(write(fd,bc->data[codep++].str,len) == -1)
		    return -1;
		
		ret = align_string(fd, len);
		if(ret == -1) return -1;
		filelen += len + ret;

	        break; 
	    case B_SETFLAG:
	    case B_ADDFLAG:
	    case B_REMOVEFLAG:
		/* Dump just a stringlist */
		ret = emit_stringlist(fd, &codep, bc);
		if(ret < 0) return -1;
		filelen += ret;
		break;

	    case B_NOTIFY:
		/* method string, id string, options string list,Priority String, Message String */
		
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
		ret = emit_stringlist(fd, &codep, bc);
		if(ret < 0) return -1;
		filelen+=ret;

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

		
	case B_DENOTIFY:
	  /*comptype  num, comp string,priority string*/ 
	  if(write(fd, &bc->data[codep].value,
		   sizeof(bc->data[codep].value)) == -1)
	    return -1;
	  filelen += sizeof(int);
	  codep++;
	  for(i=0; i<2; i++) 
	    {
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
		/* Address list, Subject String, Message String, Days (word), Mime (word) */
	   
	        /*new code-this might be broken*/
	        ret = emit_stringlist(fd, &codep, bc);
		if(ret < 0) return -1;
		filelen += ret;
		/*end of new code*/

		for(i=0; i<2; i++) {/*writing strings*/

		  /*write length of string*/
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
		    /*write string*/
       		    if(write(fd,bc->data[codep++].str,len) == -1)
			return -1;
		 
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

#if DUMPCODE
    dump(bc);
#endif
    /*teh 4 is to account for the version at hte begining*/
    return emit_bytecode_act(fd, 0, bc->curlen, bc, 4);
}

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
}

void sieve_free_bytecode(bytecode_info_t **p) 
{
    if(!p || !*p) return;
    if((*p)->data) free((*p)->data);
    free(*p);
    *p = NULL;
}
/**************************************************************************/
/**************************************************************************/
/**************************************************************************/
/**************************EXECUTING BYTECODE******************************/
/**************************************************************************/
/**************************************************************************/
/**************************************************************************/
/**************************************************************************/


static int sysaddr(char *addr)
{
    if (!strncasecmp(addr, "MAILER-DAEMON", 13))
	return 1;

    if (!strncasecmp(addr, "LISTSERV", 8))
	return 1;

    if (!strncasecmp(addr, "majordomo", 9))
	return 1;

    if (strstr(addr, "-request"))
	return 1;

    if (!strncmp(addr, "owner-", 6))
	return 1;

    return 0;
}

/* look for myaddr and myaddrs in the body of a header - return the match */
static char* look_for_me(char *myaddr, int numaddresses, bytecode_t *bc, int i, const char **body)
{
    char *found = NULL;
    int l;
    int curra,x ;

    /* loop through each TO header */
    for (l = 0; body[l] != NULL && !found; l++) {
	void *data = NULL, *marker = NULL;
	char *addr;
	
	parse_address(body[l], &data, &marker);
	/* loop through each address in the header */
	while (!found && ((addr = get_address(ADDRESS_ALL,&data, &marker, 1))!= NULL)) 
	  {
	    if (!strcmp(addr, myaddr)) 
	      {found = myaddr;
		break;}
	    curra=i;
	    for(x=0; x<numaddresses; x++)
	      {	void *altdata = NULL, *altmarker = NULL;
		char *altaddr;
		/* is this address one of my addresses? */
		parse_address((char *)&(bc[curra+1].str), &altdata, &altmarker);
		altaddr = get_address(ADDRESS_ALL, &altdata, &altmarker, 1);
		if (!strcmp(addr,altaddr))
		  {found=(char *)&(bc[curra+1].str);}
		curra+=1+((ROUNDUP(bc[curra].len+1))/sizeof(bytecode_t));
		free_address(&altdata, &altmarker);
	      }
	  }
	free_address(&data, &marker);
    }
    return found;
}
 


int shouldRespond(void * m, sieve_interp_t *interp, int numaddresses, bytecode_t* bc, int i, char ** from, char **to )
{
  const char **body;
  char buf[128];
  char *myaddr = NULL;
  int l = SIEVE_OK;
  void *data = NULL, *marker = NULL;
  char *tmp;
  int curra, x;
  char * found=NULL;
  char * reply_to=NULL;
  
  /* is there an Auto-Submitted keyword other than "no"? */
  strcpy(buf, "auto-submitted");
  if (interp->getheader(m, buf, &body) == SIEVE_OK) {
    /* we don't deal with comments, etc. here */
    /* skip leading white-space */
    while (*body[0] && isspace((int) *body[0])) body[0]++;
    if (strcasecmp(body[0], "no")) l = SIEVE_DONE;
  }
  /* Note: the domain-part of all addresses are canonicalized */
  /* grab my address from the envelope */
  if (l == SIEVE_OK) {
    strcpy(buf, "to");
    l = interp->getenvelope(m, buf, &body);
   
	
    if (body[0]) {  

      parse_address(body[0], &data, &marker);
      tmp = get_address(ADDRESS_ALL, &data, &marker, 1);
      myaddr = (tmp != NULL) ? xstrdup(tmp) : NULL;
      free_address(&data, &marker);
    }  
  }  
  
  if (l == SIEVE_OK) {
    strcpy(buf, "from");
    l = interp->getenvelope(m, buf, &body);
  }
  if (l == SIEVE_OK && body[0]) {
    /* we have to parse this address & decide whether we
       want to respond to it */
    parse_address(body[0], &data, &marker);
    tmp = get_address(ADDRESS_ALL, &data, &marker, 1);
    reply_to = (tmp != NULL) ? xstrdup(tmp) : NULL;
    free_address(&data, &marker);
      /* first, is there a reply-to address? */
    if (reply_to == NULL) {
      l = SIEVE_DONE;
    }
    
    /* first, is it from me? */
    if (l == SIEVE_OK && !strcmp(myaddr, reply_to)) {
      l = SIEVE_DONE;
    }
   
    /* ok, is it any of the other addresses i've
       specified? */
    if (l == SIEVE_OK)
      {
	curra=i;
	for(x=0; x<numaddresses; x++)
	  {if (!strcmp((char *)&(bc[curra+1].str), reply_to))
	      {l=SIEVE_DONE;}
	    curra+=1+((ROUNDUP(bc[curra].len+1))/sizeof(bytecode_t));
	  }
      }
   
    /* ok, is it a system address? */
    if (l == SIEVE_OK && sysaddr(reply_to)) {
      l = SIEVE_DONE;
    }
  }
    if (l == SIEVE_OK) {
    /* ok, we're willing to respond to the sender.
       but is this message to me?  that is, is my address
       in the TO, CC or BCC fields? */
    if (strcpy(buf, "to"), 
	interp->getheader(m, buf, &body) == SIEVE_OK)
      found = look_for_me(myaddr, numaddresses ,bc, i, body);
      if (!found && (strcpy(buf, "cc"),
		   (interp->getheader(m, buf, &body) == SIEVE_OK)))
      found = look_for_me(myaddr, numaddresses, bc, i, body);
      if (!found && (strcpy(buf, "bcc"),
		   (interp->getheader(m, buf, &body) == SIEVE_OK)))
      found = look_for_me(myaddr, numaddresses, bc, i, body);
      if (!found)
      l = SIEVE_DONE;
  }
    /* ok, ok, if we got here maybe we should reply */
  if (myaddr) free(myaddr);
  *from=found;
  *to=reply_to;
  return l;
}


int eval_bc_test(sieve_interp_t *interp, void* m, bytecode_t * bc, int * ip)
{
  int res=0; 
  int i=*ip;
  int x,y,z;/*loop variable*/
  int l;/*for allof/anyof*/
  int address=0;/*to differentiate between address and envelope*/
  comparator_t * comp=NULL;
  void * comprock=NULL;

  switch(bc[i].value)
    {
    case BC_FALSE:res=0; i++;break;
    case BC_TRUE:res=1; i++;break;
    case BC_NOT:/*2*/
      i+=1;
      res= !(eval_bc_test(interp,m, bc, &i));
      break;
    case BC_EXISTS:/*3*/
      {
	int headersi=i+1;
	int numheaders=bc[headersi].len;
	const char** val;
	int currh;
	int blah;
	res=1;
	currh=headersi+2;
	for(x=0; x<numheaders && res; x++)
	  { blah=(interp->getheader(m,(char*)&(bc[currh+1].str), &val));
	    if (blah!=SIEVE_OK)
	      {return 0;}
	    currh+=1+((ROUNDUP(bc[currh].len+1))/sizeof(bytecode_t));
	  }
	i=(bc[headersi+1].value/4);
	break;
      }
    case BC_SIZE:/*4*/
      {int s;
      res=0;
      if (interp->getsize(m, &s) != SIEVE_OK)
	break;
      if (bc[i+1].value==B_OVER)
	{res=s>bc[i+2].value;}
      else /*under*/
	{res=s<bc[i+2].value;}
      i+=2;
      break;
      }
    case BC_ANYOF:/*5*/
	res = 0;
	l=bc[i+1].len;
	i+=2;
	/*return 0 unless you find one, then return 1*/
	for (x=0;x<l && !res; x++) 
	  {res|= eval_bc_test(interp,m,bc,&i);}
	break;
    case BC_ALLOF:/*6*/
        res=1;     
	l=bc[i+1].len;
	i+=2;
	/*return 1 unless you find one that isn't true, then return 0*/
	for (x=0;x<l && res; x++) 
	  {res &= eval_bc_test(interp,m,bc,&i);}
	break;
    case BC_ADDRESS:/*7*/
      address=1;
    case BC_ENVELOPE:/*8*/
      {
	const char ** val;
	void * data=NULL;
	void * marker=NULL;
	char * addr;
	int addrpart=ADDRESS_ALL;/*is this the correct default behavior?*/

 	int headersi=i+5;/*the i value for the begining of hte headers*/
	int datai=(bc[headersi+1].value/4);

	int numheaders=bc[headersi].len;
	int numdata=bc[datai].len;

	int currh, currd; /*current header, current data*/

	int match=bc[i+1].value;
	int relation=bc[i+2].value;
	int comparator=bc[i+3].value;
	int count=0;
	char scount[3];
	res=0;
	
	/*find the correct comparator fcn*/
	comp=lookup_comp(comparator, match, relation, &comprock);
	
	/*find the part of the address that we want*/

	switch(bc[i+4].value)
	  {
	  case B_ALL: addrpart = ADDRESS_ALL; break;
	  case B_LOCALPART: addrpart = ADDRESS_LOCALPART; break;
	  case B_DOMAIN: addrpart = ADDRESS_DOMAIN; break;
	  case B_USER: addrpart = ADDRESS_USER; break;
	  case B_DETAIL: addrpart = ADDRESS_DETAIL; break;
	  default:/*this shouldn't happen with correcct bytecode*/;
	  }

      /*loop through all the headers*/
      currh=headersi+2;
      for (x=0; x<numheaders && !res; x++)
	{
	  if ((address) ? 
	      interp->getheader(m, (char*)&(bc[currh+1].str), &val) :
	      interp->getenvelope(m, (char*)&(bc[currh+1].str), &val) != SIEVE_OK) 
	    {continue; /* try next header */}
	  
	  /*header exists, now to test it*/
	  /*search through all teh headers that match*/
	  if  (match == B_COUNT )
	    {count++;}
	  else
	    {
	      for (y=0; val[y]!=NULL && !res; y++)
		{
		  if (parse_address(val[y], &data, &marker)!=SIEVE_OK) 
		    {return 0;}
		  addr=get_address(addrpart, &data, &marker, 0);
		  /*search through all the data*/ 
		  currd=datai+2;
		  for (z=0; z<numdata && !res; z++)
		    {
		      res|= comp(addr, (char*)&(bc[currd+1].str), comprock);
		      currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
		    }
		}
	    }
	  currh+=1+((ROUNDUP(bc[currh].len+1))/sizeof(bytecode_t));
	}

	  if  (match == B_COUNT )
	    {
	      sprintf(scount, "%u", count);
	      /*search through all the data*/ 
	      currd=datai+2;
	      for (z=0; z<numdata && !res; z++)
		{ 
		  res |= comp(scount,(char*)&(bc[currd+1].str), comprock);
		  currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
		}
	    }
	  i=(bc[datai+1].value/4);
	  break;
      }
    case BC_HEADER:/*9*/
      {
	const char** val;

	int headersi=i+4;/*the i value for the begining of hte headers*/
	int datai=(bc[headersi+1].value/4);

	int numheaders=bc[headersi].len;
	int numdata=bc[datai].len;

	int currh, currd; /*current header, current data*/
	int blah;

	int match=bc[i+1].value;
	int relation=bc[i+2].value;
	int comparator=bc[i+3].value;
	int count=0;	
	char scount[3];
	/*find the correct comparator fcn*/
	comp=lookup_comp(comparator, match, relation, &comprock);

	/*search through all the flags for the header*/
	currh=headersi+2;
	for(x=0; x<numheaders && !res; x++)
	  { 
	    blah=(interp->getheader(m,(char*)&(bc[currh+1].str), &val));
	    if (blah!=SIEVE_OK)
	      {currh+=1+((ROUNDUP(bc[currh].len+1))/sizeof(bytecode_t));
	      continue; /*this header does not exist, search the next*/ 
	      }
	    /*search through all teh headers that match*/
	    if  (match == B_COUNT )
	      {count++;}
	    else
	      {
		for (y=0; val[y]!=NULL&&!res; y++)
		  {	
		    /*search through all the data*/ 
		    currd=datai+2;
		    for (z=0; z<numdata && !res; z++)
		      { 
			res|= comp(val[y],(char *)&(bc[currd+1].str), comprock);
			currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
		      }
		  }
	      }
	    currh+=1+((ROUNDUP(bc[currh].len+1))/sizeof(bytecode_t));
	  }


	  if  (match == B_COUNT )
	    {
	      sprintf(scount, "%u", count);
	      /*search through all the data*/ 
	      currd=datai+2;
	      for (z=0; z<numdata && !res; z++)
		{ 	
		  if (comp !=NULL)
		    res |= comp(scount,(char*)&(bc[currd+1].str), comprock);
		  currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
		}
	    }
	i=(bc[datai+1].value/4);
	break;
      }
    default:
#if VERBOSE
      printf("WERT, can't evaluate if statement.");
#endif     
      exit(1);
    }
  *ip=i;
  return res;
}

int sieve_eval_bc(sieve_interp_t *i, void *bc_in, unsigned int bc_len,
		  void *m, sieve_imapflags_t * imapflags, action_list_t *actions,
		  notify_list_t *notify_list,
		  const char **errmsg) 
{
  /*i is a struct with useful function calls such as getheader*/
    int ip, res=0;
    int needtojump=0;
    int jumpat=-1;
    int jumpto=-1;

    bytecode_t *bc = (bytecode_t *)bc_in;
    
    if(!bc) return SIEVE_FAIL;
#if VERBOSE
    printf("version number %d\n",bc[0].op); 
#endif
    for(ip=1; ip<=bc_len; ) { 
      if (needtojump)
	{if (jumpat==ip)
	  {
#if VERBOSE
	    printf("jumping from %d to %d\n",ip, jumpto);
#endif
	    ip=jumpto;
	    jumpto=-1;
	    jumpat=-1;
	    needtojump=0;
	  }
	else if (ip>jumpat)
	  {res= -1; /*if this ever happens there is somethign wrong with teh bytecode*/
	  *errmsg ="Bytecode Error in IF statement."; 
	  return res;
	  }
	}
      switch(bc[ip].op) {
      case B_STOP:/*0*/
	  res=1;
	  break;
      case B_KEEP:/*1*/
	  res = do_keep(actions, imapflags);
	  if (res == SIEVE_RUN_ERROR)
	    *errmsg = "Keep can not be used with Reject";
	  ip++;
	  break;
      case B_DISCARD:/*2*/
	  res=do_discard(actions);
	  ip++;
	  break;
      case B_REJECT:/*3*/
	res = do_reject(actions, (char*)&bc[ip+2].str);
	
	if (res == SIEVE_RUN_ERROR)
	    *errmsg = "Reject can not be used with any other action";  
	  /* Skip length + string */
	  ip+=1+(ROUNDUP(bc[ip+1].len+1))/sizeof(bytecode_t);
	  ip++;
	  break;
      case B_FILEINTO:/*4*/
	  {
	    res = do_fileinto(actions,(char*)&(bc[ip+2].str), imapflags);
	    if (res == SIEVE_RUN_ERROR)
	      *errmsg = "Fileinto can not be used with Reject";
	    ip+=1+((ROUNDUP(bc[ip+1].len+1))/sizeof(bytecode_t));
	    ip++;
	    break;
	  }
      case B_REDIRECT:/*5*/
	  {
	    res = do_redirect(actions,(char*)&( bc[ip+2].str));
	    if (res == SIEVE_RUN_ERROR)
	      *errmsg = "Redirect can not be used with Reject";
	    ip+=1+((ROUNDUP(bc[ip+1].len+1))/sizeof(bytecode_t));
	    ip++;
	    break;
	  }
      case B_IF:/*6*/
	  {
	    int testtemp=ip;
	    ip+=3;
	    if (eval_bc_test(i,m, bc, &ip))
	      {ip=bc[testtemp+1].jump/4;}	  
	    else
	      {ip=bc[testtemp+2].jump/4;}
	    break;
	  }
      case B_IFELSE:/*7*/
	  {
	    int testtemp=ip;
	    ip+=4;
	    needtojump=1;
	    jumpto=bc[testtemp+3].jump/4;
	    
	    if(eval_bc_test(i,m,bc, &ip))
	      {ip=bc[testtemp+1].jump/4;
	       jumpat=(bc[testtemp+2].jump/4);
	      }	  
	    else
	      {ip=bc[testtemp+2].jump/4;
	       jumpat=(bc[testtemp+3].jump/4);
	      }
	  }
	  break;
      case B_MARK:/*8*/
	  res = do_mark(actions);
	  ip++;
	  break;
      case B_UNMARK:/*9*/
	  res = do_unmark(actions);
	  ip++;
	  break;
      case B_ADDFLAG:/*10*/ 
	  {
	    int x;
	    int l=bc[ip+1].len;
	    ip+=3;
	    for (x=0; x<l; x++)\
	      {
		res = do_addflag(actions,(char*)&( bc[ip+1].str));
		if (res == SIEVE_RUN_ERROR)
		  *errmsg = "addflag can not be used with Reject";
		ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	      } 
	    break;
	  }

      case B_SETFLAG:
	  {
	    int x;
	    int l=bc[ip+1].len;
	    ip+=3;
	    res = do_setflag(actions, (char*)&( bc[ip+1].str));
	    ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	    for (x=1; x<l; x++)\
	      {
		res = do_addflag(actions, (char*)&( bc[ip+1].str));
		if (res == SIEVE_RUN_ERROR)
		  *errmsg = "setflag can not be used with Reject";
		ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	      } 
	    break;
	  }
      case B_REMOVEFLAG:
	  {
	    int x;
	    int l=bc[ip+1].len;
	    ip+=3;
	    for (x=0; x<l; x++)\
	      {
		res = do_removeflag(actions, (char*)&( bc[ip+1].str));
		if (res == SIEVE_RUN_ERROR)
		  *errmsg = "removeflag can not be used with Reject";
		ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	      } 
	    break;
	  }
      case B_NOTIFY:
	{
	  char * id;
	  char * method;
	  char **options=NULL;
	  const char * priority;
	  char * message;
	  
	  ip++;
	  method= (char*)&(bc[ip+1].str); 
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*	  printf("%s\n", method);*/
	  
	  id=(char*)&(bc[ip+1].str);
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*	  printf("%s\n", id);*/
	  
	  options=bc_makeArray(bc[ip].len, ip+2,bc); 
	  ip=(bc[ip+1].value/4);
  
	  priority= (const char*)&(bc[ip+1].str); 
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*printf("priority %s\n", priority);*/

	  message=(char*)&(bc[ip+1].str);
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*	  printf("%s\n", message);*/

	  res = do_notify(notify_list, id, method, &options, priority, message);
	  
	  break;
	}
      case B_DENOTIFY:
	{
	  comparator_t * comp=NULL;
	  char * pattern;
	  char * priority;
	  void * comprock=NULL;
	  
	  comp=lookup_comp("i;ascii-casemap",bc[ip+1].value, -1, comprock);
	  
	  ip+=2;
	  pattern= (char*)&(bc[ip+1].str); 
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*printf("priority %s\n", priority);*/
	  
	  priority= (char*)&(bc[ip+1].str); 
	  ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  /*printf("priority %s\n", priority);*/
	  
	  res = do_denotify(notify_list, comp, pattern, comprock, priority);
	  
	  break;
	}
      case B_VACATION:
	  {
	    int respond;
	    char * fromaddr=NULL;/*from address in message we are sending*/
	    char * toaddr=NULL;
	    int messageip=0;
	    char buf[128];
	    ip++;
	    respond=shouldRespond(m,i, bc[ip].len, bc, ip+2, &fromaddr, &toaddr);
	    
	    ip=bc[ip+1].value/4;	
	    if (respond==SIEVE_OK)
	      {	 
		if ((bc[ip].value) == -1) 
		  {
		    /* we have to generate a subject */
		    const char **s;	    
		    strcpy(buf, "subject");
		    if (i->getheader(m, buf, &s) != SIEVE_OK || s[0] == NULL) 
		      {strcpy(buf, "Automated reply");}
		    else 
		      {
			/* s[0] contains the original subject */
			const char *origsubj = s[0];
			while (!strncasecmp(origsubj, "Re: ", 4)) 
			  {origsubj += 4;}
			snprintf(buf, sizeof(buf), "Re: %s", origsubj);
		      }
		  } 
		else 
		  { /* user specified subject */
		    strncpy(buf, (char *)&(bc[ip+1].str), sizeof(buf));}
		
		ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
		messageip=ip+1;
		ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
		res = do_vacation(actions, toaddr, strdup(fromaddr),
				  strdup(buf),strdup((char *)&(bc[messageip].str)),
				  bc[ip].value, bc[ip+1].value);
		ip+=2;		
		if (res == SIEVE_RUN_ERROR)
		  *errmsg = "Vacation can not be used with Reject or Vacation";
	      }
	    else if (respond == SIEVE_DONE) {
	      ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));/*skip subj*/
	      ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));/*skip msg*/
	      ip+=2;/*skip days and mime flag*/
	    }
	    else res = -1; /* something is bad */ 
	    break;
	  }
      default:
	
	if(errmsg) *errmsg = "Invalid sieve bytecode";
	return SIEVE_FAIL;
      }
      
      if (res) /* we've either encountered an error or a stop */
	break;
	}
      return res;
      
}

#if DUMPCODE

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
	    if (d->data[ip].value == B_COUNT || d->data[ip].value == B_VALUE)
	      {printf("      MATCH:%d  RELATION:%d  COMP:%d HEADERS:\n", 
		   d->data[ip].value, d->data[ip+1].value,d->data[ip+2].value);}
	    else
	      {printf("      MATCH:%d COMP:%d HEADERS:\n",d->data[ip].value, d->data[ip+2].value);}
	    ip+=3;
	    ip = dump_sl(d,ip); ip++;
	    printf("      DATA:\n");
	    ip = dump_sl(d,ip);
	    break;

        case BC_ADDRESS:
        case BC_ENVELOPE:
	    printf("%d: %s (\n",ip++,
		   d->data[ip].op == BC_ADDRESS ? "ADDRESS" : "ENVELOPE");
	    /*  ip++;*/
	    if (d->data[ip].value == B_COUNT || d->data[ip].value == B_VALUE)
	      {printf("      MATCH:%d RELATION: %d COMP: %d TYPE: %d HEADERS:\n", 
		  d->data[ip].value, d->data[ip+1].value, d->data[ip+2].value, d->data[ip+3].value);}
	    else
	      {printf("      MATCH:%d COMP:%d TYPE:%d HEADERS:\n",
		      d->data[ip].value,d->data[ip+1].value,d->data[ip+3].value);}
	    ip+=4;
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
    int i;
    
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
	    printf("%d: FILEINTO {%d}%s\n",i,
		   d->data[i+1].len,d->data[i+2].str);
	    i+=2;
	    break;

	case B_REDIRECT:
	    printf("%d: REDIRECT {%d}%s\n",i,
		   d->data[i+1].len,d->data[i+2].str);
	    i+=2;
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
	    printf("%d: DENOTIFY comp,%d %s  %s\n",i, d->data[i+1].value,d->data[i+3].str,d->data[i+5].str);
	    i+=5;
	    break;

	case B_NOTIFY: 
	    printf("%d: NOTIFY\n   METHOD(%s),\n   ID(%s),\n   OPTIONS",
		   i,d->data[i+2].str,d->data[i+4].str);
	    i+=5;
	    i=dump_sl(d,i);
	    printf("   PRIORITY(%s),\n   MESSAGE({%d}%s)\n", 
		   d->data[i+2].str, d->data[i+3].len,d->data[i+4].str);
	    i+=4;
	    break;

	case B_VACATION:
	  printf("%d:VACATION\n",i);
	  i++;
	    i=dump_sl(d,i);
	    printf("SUBJ({%d}%s) MESG({%d}%s)\n DAYS(%d) MIME(%d)\n", 
		   d->data[i+1].len, (d->data[i+1].len == -1 ? "[nil]" : d->data[i+2].str),
		   d->data[i+3].len, (d->data[i+3].len == -1 ? "[nil]" : d->data[i+4].str),
		   d->data[i+5].value, d->data[i+6].value);
	    i+=6;
	
	    break;

	default:
	    printf("%d: %d\n",i,d->data[i].op);
	    break;
	}
    }
    printf("full len is: %d\n", d->curlen);
}
#endif

