/* bc_generate.c -- sieve bytecode- almost flattened bytecode
 * Rob Siemborski
 * $Id: bc_dump.c,v 1.1.2.1 2003/01/15 23:31:16 jsmith2 Exp $
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
 
#include "sieve_interface.h"
#include "bytecode.h"


struct bytecode_info 
{
  bytecode_t *data;/* pointer to almost-flat bytecode */
  size_t scriptend; /* used by emit code to know final length of bytecode */
  size_t reallen; /* allocated length of 'data' */
};





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
	    /*   printf("  (until %d)\n", d->data[ip++].jump);*/
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
    
    for(i=0; i<d->scriptend; i++) {
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
	case B_NULL:
	    printf("%d: NULL\n",i);
	    break;

	default:
	    printf("%d: %d\n",i,d->data[i].op);
	    break;
	}
    }
    printf("full len is: %d\n", d->scriptend);
}
#endif

