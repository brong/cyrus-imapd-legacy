/* dump.c -- bytecode decompiler
 * Jen Smith
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



#include <sieve_interface.h>

#include "bytecode.h"
#include "script.h"

#include "xmalloc.h"
#include <sys/types.h> 
#include <sys/stat.h>
#include <fcntl.h> 
#include <unistd.h> 

#include "map.h"

void dump2(bytecode_t *d, int len);
int dump2_test(bytecode_t * d, int i);
 
/*this is called by xmalloc*/
void fatal(const char *s, int code)
{  
    printf("Fatal error: %s (%d)\r\n", s, code);
                           
    exit(1);
}

int load(int fd, bytecode_t ** d)
{  
  const char * data=NULL;
  struct stat sbuf;
  unsigned long len=0;
/*int i;*/
  if (fstat(fd, &sbuf) == -1) {
     /*	syslog(LOG_ERR, "IOERROR: fstating sieve script: %m");*/
	return SIEVE_FAIL;
    }
   /*
     data=xmalloc(sbuf.st_size);
     len=read(fd,data,sbuf.st_size)/sizeof(int);
   */  
   /*this reads in data and length from file*/
    map_refresh(fd, 1, &(data), &len, sbuf.st_size,
		"sievescript", "");
    *d=(bytecode_t *)data;
    /*  for(i=0; i<len; i++)
      {printf("%s",&(data[i]));}
    */
    printf("\n");

    /*  for (i=0; i<(len); i+=4)
      {printf ("%d ", (int)data[i]);}
      printf("\n\n");*/
   return (len/sizeof(int));



}


int main(int argc, char * argv[])
{

   bytecode_t * bc;
   int script_fd;

   unsigned long len;

   if (argc!=2)
     {
       fprintf(stderr, "usage:\n %s script\n", argv[0]);
       exit(1);
     }
   /*get script*/
   script_fd = open(argv[1], O_RDONLY);
   if (script_fd == -1) 
     {
       printf("can not open script '%s'\n", argv[1]);
       exit(1);
     }
   
   len=load(script_fd,&bc);
   close(script_fd);
   
   if (bc !=NULL)
     { dump2(bc, len );
       exit(0);}
   else
     {exit(1);}
}

int write_list(int list_len, int i, bytecode_t * d)
{int x;
/* int endoflist=d[i].value;*/
 i++;
 for (x=0; x<list_len; x++)
   {
     printf("%s (takes up %d )\n", (char*)&(d[i+1].str), (ROUNDUP(d[i].len+1))/sizeof(bytecode_t));

      i+=1+((ROUNDUP(d[i].len+1))/sizeof(bytecode_t));
   }
 /*  printf("%d (predicted %d)\n", i, endoflist/4);*/
 return i;
}
int printComparison(bytecode_t *d ,int i)
{
  printf("Comparison: ");
   switch(d[i].value)
    {
    case B_IS: printf("Is");break;
    case B_CONTAINS:printf("Contains");break;
    case B_MATCHES:printf("Matches");break;
    case B_REGEX:printf("Regex");break;
    case B_COUNT: printf("Count");
     
      switch(d[i+1].value)
	{
	case B_GT: printf(" greater than "); break;   
	case B_GE: printf(" greater than or equal ");break;
	case B_LT: printf(" less than ");    break;
	case B_LE: printf(" less than or equal ");break;
	case B_NE: printf(" not equal ");    break;
	case B_EQ: printf(" equal ");break;
	}
      break;
    case B_VALUE:printf("Value");
     
      switch(d[i+1].value)
	{
	case B_GT: printf(" greater than "); break;   
	case B_GE: printf(" greater than or equal ");break;
	case B_LT: printf(" less than ");    break;
	case B_LE: printf(" less than or equal ");break;
	case B_NE: printf(" not equal ");    break;
	case B_EQ: printf(" equal ");break;
	}
  
    default: exit(1);
	
      break;
    }
   switch (d[i+2].value)
     {
     case B_ASCIICASEMAP: printf("   (ascii-casemap) "); break;
     case B_OCTET: printf("    (octet) "); break;
     case B_ASCIINUMERIC:  printf("   (ascii-numeric) "); break;
     default: exit(1);
     }
   printf("\n");
  return i+3;
}


int dump2_test(bytecode_t * d, int i)
{int l,x;
  switch(d[i].value) {
  case BC_FALSE:
    printf("false");
   i++;
    break;
  case BC_TRUE:
    printf("true");
    i++;
    break;
  case BC_NOT:/*2*/
    /*there is a value being skipped in the second pass...no idea what it does, but it isn't carried to here...see bytecodee.c*/
    printf(" not(");
    i=dump2_test(d, i+1);
    printf(")\n");
    break;
  case BC_EXISTS:
    printf("exists");
    i=write_list(d[i+1].len, i+2,d);
    break;
  case BC_SIZE:
    printf("size");
    if (d[i+1].value==B_OVER)
      {printf("over %d", d[i+2].value);}
    else /*under*/
      {printf("over %d", d[i+2].value);}
    
    i+=3;
    break;
  case BC_ANYOF:/*5*/
  
  printf("any of \n(");
    l=d[i+1].len;
    i+=2;

    for (x=0; x<l; x++)
      {i=dump2_test(d,i);
      printf("OR");}

    printf(")\n");	 
    break;
  case BC_ALLOF:/*6*/
    printf("all of \n(");
    l=d[i+1].len;
    i+=2;

    for (x=0; x<l; x++)
      {i=dump2_test(d,i);
      printf("AND");}

    printf(")\n");
    break;
  case BC_ADDRESS:/*7*/
    printf("Address (");
    i=printComparison(d, i+1);
    printf("               type: ");
    switch(d[i++].value)
      {
      case B_ALL: printf("all");break;
      case B_LOCALPART:printf("localpart");break;
      case B_DOMAIN:printf("domain");break;
      case B_USER:printf("user");break;
      case B_DETAIL:printf("detail");break;
      }
    printf("              Headers:");
    i=write_list(d[i].len, i+1, d);
    printf("              Data:");
    i=write_list(d[i].len, i+1, d);
    printf("             ]\n");
    break;
  case BC_ENVELOPE:/*8*/
    printf("Envelope (");
    i=printComparison(d, i+1);
    printf("                type: ");
    switch(d[i++].value)
      {
      case B_ALL: printf("all");break;
      case B_LOCALPART:printf("localpart");break;
      case B_DOMAIN:printf("domain");break;
      case B_USER:printf("user");break;
      case B_DETAIL:printf("detail");break;
      }
    printf("              Headers:");
    i=write_list(d[i].len, i+1, d);
    printf("              Data:");
    i=write_list(d[i].len, i+1, d);
    printf("             ]\n");
    break;
  case BC_HEADER:/*9*/
    printf("Header [");
    i= printComparison(d, i+1);
    printf("              Headers: ");
    i=write_list(d[i].len, i+1, d);
    printf("              Data: ");
    i=write_list(d[i].len, i+1, d);
    printf("             ]\n");
    break;
  default:
    printf("WERT %d ",d[i].value);
  }   
  return i;
}


void dump2(bytecode_t *d, int len) 
{int testtemp;
    int i;
    printf("Sievecode version %d\n", d[0].op);
    if(!d) return;
    
    for(i=1; i<len;) 
      {
	switch(d[i].op) {

	case B_STOP:/*0*/
	    printf("%d: STOP\n",i);
	    i++;
	    break;

	case B_KEEP:/*1*/
	    printf("%d: KEEP\n",i);
	    i++;
	    break;

	case B_DISCARD:/*2*/
	    printf("%d: DISCARD\n",i);
	    i++;
	    break;
	    
	case B_REJECT:/*3*/
	    printf("%d: REJECT {length %d}\n%s  ",i, d[i+1].len,(char *)&(d[i+2].str));
	    printf("(%d words)\n", (ROUNDUP(d[i+1].len+1))/sizeof(bytecode_t));
	    i+=(1+(ROUNDUP(d[i+1].len+1))/sizeof(bytecode_t));
	    i++;
	    break;

	case B_FILEINTO: /*4*/
	    printf("%d: FILEINTO {%s}\n",i,(char *)&(d[i+2].str));
	    i+=(1+(ROUNDUP(d[i+1].len+1))/sizeof(bytecode_t));
	    i++;
	    break;

	case B_REDIRECT: /*5*/
	    printf("%d: REDIRECT {%s}\n",i,(char *)&(d[i+2].str));
	    i+=(1+(ROUNDUP(d[i+1].len+1))/sizeof(bytecode_t));
	    i++;
	    break;
	     
	case B_IF:/*6*/
	    printf("%d: IF ",i);
	    testtemp=i;
	    i = dump2_test(d,i+3);
	    printf("   THEN(%d) \n   POST(%d)\n",  d[testtemp+1].jump/4,d[testtemp+2].jump/4);
	    break;
	case B_IFELSE:/*7*/
	    printf("%d: IF ",i);
	    testtemp=i;
	    i = dump2_test(d,i+4);
	    printf("   THEN(%d) \n   ELSE(%d) \n   POST(%d)\n",
		   d[testtemp+1].jump/4,d[testtemp+2].jump/4,
		   d[testtemp+3].jump/4);
	    break;

	case B_MARK:/*8*/
	    printf("%d: MARK\n",i);
	    i++;
	    break;

	case B_UNMARK:/*9*/
	    printf("%d: UNMARK\n",i);
	    i++;
	    break;

	case B_ADDFLAG: /*10*/
	    printf("%d: ADDFLAG  {%d}\n",i,d[i+1].len);
	    i=write_list(d[i+1].len,i+2,d);
	    break;

	case B_SETFLAG: /*11*/
	  printf("%d: SETFLAG  {%d}\n",i,d[i+1].len);
	 	    i=write_list(d[i+1].len,i+2,d);
	    break;

	case B_REMOVEFLAG: /*12*/
	    printf("%d: REMOVEFLAG  {%d}\n",i,d[i+1].len);
	    i=write_list(d[i+1].len,i+2,d);
	    break;
	    
	case B_DENOTIFY:/*14*/
	    printf("%d: DENOTIFY\n",i);
	    i++; 
	    printf("            PRIORITY(%d) Comparison type %d (relat %d)\n",d[i].value,d[i+1].value, d[i+2].value);
	    i+=3;
	    
	    printf("           ({%d}%s)\n", d[i].len,(d[i].len == -1 ? "[nil]" : (char*)&(d[i+1].str)));
      	    i+=1+((ROUNDUP(d[i].len+1))/sizeof(bytecode_t));
	    break;
	    
	case B_NOTIFY: /*13*/
	    printf("%d: NOTIFY METHOD({%d}%s)\n",i,
		   d[i+1].len,(char*)&(d[i+2].str));  
	    i+=2+((ROUNDUP(d[i+1].len+1))/sizeof(bytecode_t));

	    printf("            ID({%d}%s) OPTIONS ",d[i].len,(d[i].len == -1 ? "[nil]" : (char*)&(d[i+1].str)));
	    i+=1+((ROUNDUP(d[i].len+1))/sizeof(bytecode_t));
	    printf("len%d\n",d[i].len);
	    
	    i=write_list(d[i].len,i+1,d);
	    
	    printf("            PRIORITY(%d)\n",d[i].value);
      	    i++;
		  
	    printf("            MESSAGE({%d}%s)\n", d[i].len,(char*)&(d[i+1].str));
	    i+=1+((ROUNDUP(d[i].len+1))/sizeof(bytecode_t));

	    break;

	case B_VACATION:/*15*/
	  printf("%d: VACATION\n",i);
	  /*add address list here!*/
	  i=write_list(d[i+1].len,i+2,d);
	  
	  printf("%d SUBJ((%d b)%s) \n",i,
		 d[i].len, (d[i].len == -1 ? "[nil]" : (char*)&(d[i+1].str)));
	  i+=1+((ROUNDUP(d[i].len+1))/sizeof(bytecode_t));

	  printf("%d MESG((%d b)%s) \n", i,
		 d[i].len, (d[i].len == -1 ? "[nil]" : (char*)&(d[i+1].str)));
	  i+=1+(ROUNDUP(d[i].len+1))/sizeof(bytecode_t);

	  printf("DAYS(%d) MIME(%d)\n",d[i].value, d[i+1].value);
	  i+=2;

	  break;
	case B_NULL:/*16*/
	  printf("%d:NULL\n",i);
	  i++;
	  break;		  
	default:
	    printf("%d: %d (NOT AN OP)\n",i,d[i].op);
	    exit(1);
	}
    }
    printf("full len is: %d\n", len);
}


