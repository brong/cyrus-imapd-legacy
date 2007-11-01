/* sieved.c -- bytecode decompiler
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


#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include "sieve_interface.h"

#include "bytecode.h"
#include "script.h"

#include "xmalloc.h"
#include <sys/types.h> 
#include <sys/stat.h>
#include <fcntl.h> 
#include <unistd.h> 
#include <netinet/in.h>

#include <string.h>

#include "map.h"

/* config.c stuff */
const int config_need_data = 0;

static void dump2(bytecode_input_t *d, int len);
static int dump2_test(bytecode_input_t * d, int i);
 
/* from bc_eval.c */
int unwrap_string(bytecode_input_t *bc, int pos, const char **str, int *len);

/*this is called by xmalloc*/
void fatal(const char *s, int code)
{  
    printf("Fatal error: %s (%d)\r\n", s, code);
                           
    exit(1);
}

static int load(int fd, bytecode_input_t ** d)
{  
    const char * data=NULL;
    struct stat sbuf;
    unsigned long len=0;
    
    if (fstat(fd, &sbuf) == -1) {
	printf("IOERROR: fstating sieve script: %m");
	return SIEVE_FAIL;
    }
    
    /*this reads in data and length from file*/
    map_refresh(fd, 1, &(data), &len, sbuf.st_size,
		"sievescript", "");
    *d=(bytecode_input_t *)data;
    
    printf("\n");
    
    return (len/sizeof(int));
}


int main(int argc, char * argv[])
{
    bytecode_input_t *bc = NULL;
    int script_fd;
    
    unsigned long len;
    
    if (argc!=2) {
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
    
    if (bc) {
	dump2(bc, len );
	exit(0);
    } else {
	exit(1);
    }
}

static int write_list(int list_len, int i, bytecode_input_t * d)
{
    int x;
    i++;
    for (x=0; x<list_len; x++)
    {
	const char *data;
	int len;
	
	i = unwrap_string(d, i, &data, &len);
	
	printf("{%d}%s\n", len, data);
    }
    return i;
}

static int printComparison(bytecode_input_t *d ,int i)
{
    printf("Comparison: ");
    switch(ntohl(d[i].value))
    {
    case B_IS: printf("Is"); break;
    case B_CONTAINS:printf("Contains"); break;
    case B_MATCHES: printf("Matches"); break;
    case B_REGEX: printf("Regex"); break;
    case B_COUNT:
	printf("Count");
	
	switch(ntohl(d[i+1].value))
	{
	case B_GT: printf(" greater than "); break;   
	case B_GE: printf(" greater than or equal "); break;
	case B_LT: printf(" less than "); break;
	case B_LE: printf(" less than or equal "); break;
	case B_NE: printf(" not equal "); break;
	case B_EQ: printf(" equal "); break;
	}

	break;
    case B_VALUE:
	printf("Value");
	
	switch(ntohl(d[i+1].value))
	{
	case B_GT: printf(" greater than "); break;   
	case B_GE: printf(" greater than or equal ");break;
	case B_LT: printf(" less than ");    break;
	case B_LE: printf(" less than or equal ");break;
	case B_NE: printf(" not equal ");    break;
	case B_EQ: printf(" equal ");break;
	}
	
	break;
    default:
	exit(1);
    }

    switch (ntohl(d[i+2].value))
    {
    case B_ASCIICASEMAP: printf("   (ascii-casemap) "); break;
    case B_OCTET: printf("    (octet) "); break;
    case B_ASCIINUMERIC:  printf("   (ascii-numeric) "); break;
    default: exit(1);
    }
    
    printf("\n");
    return i+3;
}


static int dump2_test(bytecode_input_t * d, int i)
{
    int l,x;
    switch(ntohl(d[i].value)) {
    case BC_FALSE:
	printf("false");
	i++;
	break;
    case BC_TRUE:
	printf("true");
	i++;
	break;
    case BC_NOT:/*2*/
	/* XXX 
	   there is a value being skipped in the second pass...
	   no idea what it does, but it isn't carried to here...
	   see bytecodee.c */
	printf(" not(");
	i=dump2_test(d, i+1);
	printf(")\n");
	break;
    case BC_EXISTS:
	printf("exists");
	i=write_list(ntohl(d[i+1].len), i+2, d);
	break;
    case BC_SIZE:
	printf("size");
	if (ntohl(d[i+1].value)==B_OVER) {
	    /* over */
	    printf("over %d", ntohl(d[i+2].value));
	} else {
	    /* under */
	    printf("under %d", ntohl(d[i+2].value));
	}
	i+=3;
	break;
    case BC_ANYOF:/*5*/
	printf("any of \n(");
	l=ntohl(d[i+1].len);
	i+=3;
	
	for (x=0; x<l; x++)
	{
	    i=dump2_test(d,i);
	    if((x+1)<l)
		printf(" OR ");
	}
	
	printf(")\n");	 
	break;
    case BC_ALLOF:/*6*/
	printf("all of \n(");
	l=ntohl(d[i+1].len);
	i+=3;
	
	for (x=0; x<l; x++)
	{
	    i=dump2_test(d,i);
	    if((x+1)<l)
		printf(" AND ");
	}
	
	printf(")\n");
	break;
    case BC_ADDRESS:/*7*/
	printf("Address [");
	i=printComparison(d, i+1);
	printf("               type: ");
	switch(ntohl(d[i++].value))
	{
	case B_ALL: printf("all"); break;
	case B_LOCALPART:printf("localpart"); break;
	case B_DOMAIN:printf("domain"); break;
	case B_USER:printf("user"); break;
	case B_DETAIL:printf("detail"); break;
	}
	printf("              Headers:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("              Data:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("             ]\n");
	break;
    case BC_ENVELOPE:/*8*/
	printf("Envelope [");
	i=printComparison(d, i+1);
	printf("                type: ");
	switch(ntohl(d[i++].value))
	{
	case B_ALL: printf("all"); break;
	case B_LOCALPART:printf("localpart"); break;
	case B_DOMAIN:printf("domain"); break;
	case B_USER:printf("user"); break;
	case B_DETAIL:printf("detail"); break;
	}
	printf("              Headers:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("              Data:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("             ]\n");
	break;
    case BC_HEADER:/*9*/
	printf("Header [");
	i= printComparison(d, i+1);
	printf("              Headers: ");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("              Data: ");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("             ]\n");
	break;
    case BC_BODY:/*10*/
	printf("Body [");
	i=printComparison(d, i+1);
	printf("              Transform: ");
	switch(ntohl(d[i++].value))
	{
	case B_RAW: printf("raw"); break;
	case B_TEXT:printf("text"); break;
	case B_CONTENT:printf("content"); break;
	}
	printf("\tOffset: %d\n", ntohl(d[i++].value));
	printf("              Content-Types:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("              Data:");
	i=write_list(ntohl(d[i].len), i+1, d);
	printf("             ]\n");
	break;
    default:
	printf("WERT %d ", ntohl(d[i].value));
    }   
    return i;
}

static void dump2(bytecode_input_t *d, int bc_len)
{
    int i;
    int version;
    const char *data;
    int len;
    
    if(memcmp(d, BYTECODE_MAGIC, BYTECODE_MAGIC_LEN)) {
	printf("not a bytecode file [magic number test failed]\n");
	return;
    }

    i = BYTECODE_MAGIC_LEN / sizeof(bytecode_input_t);

    version = ntohl(d[i].op);
    printf("Sievecode version %d\n", version);
    if(!d) return;
    
    for(i++; i<bc_len;) 
    {
	int copy = 0;

	printf("%d: ",i);

	switch(ntohl(d[i++].op)) {
	    
	case B_STOP:/*0*/
	    printf("STOP\n");
	    break;
	    
	case B_KEEP:/*1*/
	    printf("KEEP\n");
	    break;
	    
	case B_DISCARD:/*2*/
	    printf("DISCARD\n");
	    break;
	    
	case B_REJECT:/*3*/
	    i = unwrap_string(d, i, &data, &len);
	    printf("REJECT {%d}%s\n", len, data);
	    break;

	case B_FILEINTO: /*19*/
	    copy = ntohl(d[i++].value);
	case B_FILEINTO_ORIG: /*4*/
	    i = unwrap_string(d, i, &data, &len);
	    printf("FILEINTO COPY(%d) FOLDER({%d}%s)\n",copy,len,data);
	    break;

	case B_REDIRECT: /*20*/
	    copy = ntohl(d[i++].value);
	case B_REDIRECT_ORIG: /*5*/
	    i = unwrap_string(d, i, &data, &len);
	    printf("REDIRECT COPY(%d) ADDRESS({%d}%s)\n",copy,len,data);
	    break;
	     
	case B_IF:/*6*/
	    printf("IF (ends at %d)", ntohl(d[i].value));

            /* there is no short circuiting involved here*/
	    i = dump2_test(d,i+1);
	    printf("\n");

	    break;

	case B_MARK:/*7*/
	    printf("MARK\n");
	    break;

	case B_UNMARK:/*8*/
	    printf("UNMARK\n");
	    break;

	case B_ADDFLAG: /*9*/
	    printf("ADDFLAG  {%d}\n",ntohl(d[i].len));
	    i=write_list(ntohl(d[i].len),i+1,d);
	    break;

	case B_SETFLAG: /*10*/
	    printf("SETFLAG  {%d}\n",ntohl(d[i].len));
	    i=write_list(ntohl(d[i].len),i+1,d);
	    break;
	    
	case B_REMOVEFLAG: /*11*/
	    printf("REMOVEFLAG  {%d}\n",ntohl(d[i].len));
	    i=write_list(ntohl(d[i].len),i+1,d);
	    break;
	    
	case B_DENOTIFY:/*12*/
	    printf("DENOTIFY\n");
	    printf("            PRIORITY(%d) Comparison type %d (relat %d)\n",
		   ntohl(d[i].value), ntohl(d[i+1].value), ntohl(d[i+2].value));
	    i+=3;

	    i = unwrap_string(d, i+1, &data, &len);
	    
	    printf("           ({%d}%s)\n", len, (!data ? "[nil]" : data));
	    break;
	    
	case B_NOTIFY: /*13*/
	    i = unwrap_string(d, i, &data, &len);

	    printf("NOTIFY METHOD({%d}%s)\n",len,data);

	    i = unwrap_string(d, i, &data, &len);

	    printf("            ID({%d}%s) OPTIONS ", len,
		   (!data ? "[nil]" : data));

	    i=write_list(ntohl(d[i].len),i+1,d);
	    
	    printf("            PRIORITY(%d)\n", ntohl(d[i].value));
      	    i++;
		  
	    i = unwrap_string(d, i, &data, &len);

	    printf("            MESSAGE({%d}%s)\n", len, data);

	    break;

	case B_VACATION:/*14*/
	    printf("VACATION\n");
	    /*add address list here!*/
	    i=write_list(ntohl(d[i].len),i+1,d);

	    i = unwrap_string(d, i, &data, &len);
	  
	    printf("%d SUBJ({%d}%s) \n",i, len, (!data ? "[nil]" : data));
	    
	    i = unwrap_string(d, i, &data, &len);

	    printf("%d MESG({%d}%s) \n", i, len, (!data ? "[nil]" : data));

	    printf("DAYS(%d) MIME(%d)\n", ntohl(d[i].value), ntohl(d[i+1].value));
	    i+=2;

	    if (version >= 0x05) {
		i = unwrap_string(d, i, &data, &len);

		printf("%d FROM({%d}%s) \n",i, len, (!data ? "[nil]" : data));

		i = unwrap_string(d, i, &data, &len);

		printf("%d HANDLE({%d}%s) \n",i, len, (!data ? "[nil]" : data));
	    }

	    break;
	case B_NULL:/*15*/
	    printf("NULL\n");
	    break;
	case B_JUMP:/*16*/
	    printf("JUMP %d\n", ntohl(d[i].jump));
	    i+=1;
	    break;		  

	case B_INCLUDE:/*17*/
	    printf("INCLUDE ");
	    switch (ntohl(d[i].value)) {
	    case B_PERSONAL: printf("Personal"); break;
	    case B_GLOBAL: printf("Global"); break;
	    }
	    i = unwrap_string(d, i+1, &data, &len);
	    printf(" {%d}%s\n", len, data);
	    break;

	case B_RETURN:/*18*/
	    printf("RETURN\n");
	    break;
	    
	default:
	    printf("%d (NOT AN OP)\n",ntohl(d[i-1].op));
	    exit(1);
	}
    }
    printf("full len is: %d\n", bc_len);
}


