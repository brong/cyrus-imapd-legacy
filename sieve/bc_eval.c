/* bc_generate.c -- sieve bytecode- almost flattened bytecode
 * Rob Siemborski
 * $Id: bc_eval.c,v 1.1.2.6 2003/01/23 21:27:49 jsmith2 Exp $
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
#include "interp.h"
#include "message.h"

#include "bytecode.h"

#include "xmalloc.h"

#include <string.h>
#include <ctype.h>

/**************************************************************************/
/**************************************************************************/
/**************************************************************************/
/**************************EXECUTING BYTECODE******************************/
/**************************************************************************/
/**************************************************************************/
/**************************************************************************/
/**************************************************************************/


/* this is used by notify to pass the options list */


char ** bc_makeArray(int len, int i, bytecode_t *bc) 
{ 
    int x;
    char** array;
/* int endoflist=bc[i].value;*/
    i++;
  
    array=(char**)xmalloc(len* sizeof(char *));
    for (x=0; x<len; x++)
    { 
	/* array[x]=(char*)xmalloc(bc[i].len);
	   strncpy(array[x], (char*)&(bc[i+1].str), bc[i].len);*/
	array[x]= xstrdup(&bc[i+1].str);
	
    }
  
    return array;
}

regex_t * bc_compile_regex(char * s, int ctag, char * errmsg)
{
    int ret;
    regex_t *reg = (regex_t *) xmalloc(sizeof(regex_t));
    
    if ( (ret=regcomp(reg, s, ctag)) != 0)
    {
	(void) regerror(ret, reg, errmsg, sizeof(errmsg));
	free(reg);
	return NULL;
    }
    return reg;
}

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
	int isReg = (match==B_REGEX);
	int ctag;
	regex_t *reg;
	char *errbuf;/* this is a silly variable.
		      * we currently have nothing in place for reporting errors in this fcn,
		      * the compiling of a regex should work, we tested it on parsing*/ 
	
	/*set up variables needed for compiling regex*/
	if (isReg)
	{
	    if (comparator== B_ASCIICASEMAP)
	    {
		ctag= REG_EXTENDED | REG_NOSUB | REG_ICASE;
	    }
	    else
	    {
		ctag= REG_EXTENDED | REG_NOSUB;
	    }
     
	}
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
		    if (addr)
		    {
		      
			/*search through all the data*/ 
			currd=datai+2;
			for (z=0; z<numdata && !res; z++)
			{
			    if (isReg)
			    {
				reg= bc_compile_regex((char*)&bc[currd+1].str, ctag, errbuf);
				if (!reg) exit (1);
				res|= comp(val[y], reg, comprock);
				free(reg);
			    }
			    else
			    {
				res|= comp(addr, (char*)&(bc[currd+1].str), comprock);
			    }
			    currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
			}
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
	int isReg = (match==B_REGEX);
	int ctag;
	regex_t *reg;
	char errbuf[100];/* this is a silly variable.
			  * we currently have nothing in place for reporting errors in this fcn,
			  * the compiling of a regex should work, we tested it on parsing*/ 

	/*set up variables needed for compiling regex*/
	if (isReg)
	{
	    if (comparator== B_ASCIICASEMAP)
	    {
		ctag= REG_EXTENDED | REG_NOSUB | REG_ICASE;
	    }
	    else
	    {
		ctag= REG_EXTENDED | REG_NOSUB;
	    }
     
	}
	
      
	
	
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
			if (isReg)
			{
			    reg= bc_compile_regex((char *)&bc[currd+1].str, ctag, errbuf);
			    if (!reg) exit (1);
			    res|= comp(val[y],reg, comprock);
			    free( reg);
			}
			else
			{
			    res|= comp(val[y],(char *)&(bc[currd+1].str), comprock);
			}
			
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
		{
		    res |= comp(scount,(char*)&(bc[currd+1].str), comprock);
		    currd+=1+((ROUNDUP(bc[currd].len+1))/sizeof(bytecode_t));
		}
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
	    /*method*/
	    method= (char*)&(bc[ip+1].str); 
	    ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	    /*id*/
	    if (bc[ip].len ==-1)
	    {
		id=NULL;
	    }else
	    {
		id=(char*)&(bc[ip+1].str);
	    }
	    ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));

	    /*options*/
	    options=bc_makeArray(bc[ip].len, ip+1,bc); 
	    ip=(bc[ip+1].value/4);
	    /*priority*/
	    switch (bc[ip++].value)
	    {
	    case B_LOW:
		priority="low";
	    case B_NORMAL:
		priority="normal";
		break;
	    case B_HIGH: 
		priority="high";
		break; 
	    case B_ANY:
		priority="any";
		break;
	    default:
		res=SIEVE_RUN_ERROR;
	    }
	    /*message*/
	    message=(char*)&(bc[ip+1].str);
	    ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  
	    res = do_notify(notify_list, id, method, &options, priority, message);
	 	  
	    break;
	}
	case B_DENOTIFY:
	{/* i really have no idea what the count matchtype should do here.
	  * the sanest thing would be to use 1.
	  * however that would require passing on the match type to do_notify.
	  * it is also a completly stupid idea to use count for denotify, so i doubt it will
	  * ever be used.   if it is it will work approximately the same as value
	  */
	    comparator_t * comp=NULL;
	    
	    char * pattern;
	    regex_t *reg;
	    
	    char * priority;
	    void * comprock=NULL;
	    
	    int comparator;
	    
	    ip++;
	    switch (bc[ip++].value)
	    {
	    case B_LOW:
		priority="low";
		
	    case B_NORMAL:
		priority="normal";
		break;
	    case B_HIGH: 
		priority="high";
		break; 
	    case B_ANY:
		priority="any";
		break;
	    default:
		res=SIEVE_RUN_ERROR;
	    }
	   
	    comparator = bc[ip++].value;
	   
	    
	    if (comparator == B_ANY)
	    { 
		ip++;/*skip relat*/
		comp=NULL;
	    }else
	    {
		comp=lookup_comp(B_ASCIICASEMAP,comparator, bc[ip++].value, &comprock);
	    }
	    
	    if (bc[ip].len ==-1)
	    {
		pattern=NULL;
	    }else
	    {
		pattern= (char*)&(bc[ip+1].str);
	    }
	    
	    ip+=1+((ROUNDUP(bc[ip].len+1))/sizeof(bytecode_t));
	  
	    if (comparator == B_REGEX)
	    {	
		reg=bc_compile_regex(pattern, REG_EXTENDED | REG_NOSUB | REG_ICASE, *errmsg);
		if (!reg) {res = SIEVE_RUN_ERROR;}
		res = do_denotify(notify_list, comp, reg, comprock, priority);
		free(reg);
	    }else
	    {
		res = do_denotify(notify_list, comp, pattern, comprock, priority);
	    }
	    
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
	case B_NULL:/*16*/
	    ip++;
	    break;
	default:
	
	    if(errmsg) *errmsg = "Invalid sieve bytecode";
	    return SIEVE_FAIL;
	}
      
	if (res) /* we've either encountered an error or a stop */
	    break;
    }
    return res;
      
}
