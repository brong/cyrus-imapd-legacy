/* bc_generate.c -- sieve bytecode- almost flattened bytecode
 * Rob Siemborski
 * $Id: bc_emit.c,v 1.1.2.2 2003/01/16 17:39:57 jsmith2 Exp $
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

#include "xmalloc.h"
#include "sieve_interface.h"

 
#include "bytecode.h"

#include <syslog.h>
#include <sys/types.h>
#include <unistd.h>


#if DUMPCODE
void dump(bytecode_info_t *d);
#endif


struct bytecode_info 
{
  bytecode_t *data;/* pointer to almost-flat bytecode */
  size_t scriptend; /* used by emit code to know final length of bytecode  */
  size_t reallen; /* allocated length of 'data' */
};

/* Pad null bytes onto the end of the string we just wrote */
/* returns -1 on failure or number of bytes written on success */
static int align_string(int fd, int string_len) 
{
    /* Keep in mind that we always want to pad a string with *at least*
     * one zero, that's why sometimes we have to pad with 4 */
    int needed = sizeof(int) - (string_len % sizeof(int));
    int i;
    
    for(i = 0; i < needed; i++) 
      {
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
	    case B_NULL:
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
    /*the 4 is to account for the version # at the begining*/
    return emit_bytecode_act(fd, 0, bc->scriptend, bc, 4);
}

void sieve_free_bytecode(bytecode_info_t **p) 
{
    if(!p || !*p) return;
    if((*p)->data) free((*p)->data);
    free(*p);
    *p = NULL;
}
 
