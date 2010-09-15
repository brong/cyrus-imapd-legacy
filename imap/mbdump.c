/* mbdump.c -- Mailbox dump routines
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
 * $Id: mbdump.c,v 1.46 2010/01/06 17:01:36 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <syslog.h>
#include <sys/types.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <ctype.h>
#include <unistd.h>
#include <dirent.h>

#include "assert.h"
#include "annotate.h"
#include "exitcodes.h"
#include "global.h"
#include "imap_err.h"
#include "imparse.h"
#include "mailbox.h"
#include "map.h"
#include "mbdump.h"
#include "mboxkey.h"
#include "mboxlist.h"
#include "prot.h"
#include "quota.h"
#include "seen.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "user.h"
#include "util.h"
#include "index.h"

/* is this the active script? */
static int sieve_isactive(char *sievepath, char *name)
{
    char filename[1024];
    char linkname[1024];
    char activelink[1024];
    char *file, *link;
    int len;

    snprintf(filename, sizeof(filename), "%s/%s", sievepath, name);
    snprintf(linkname, sizeof(linkname), "%s/defaultbc", sievepath);

    len = readlink(linkname, activelink, sizeof(activelink)-1);
    if(len < 0) {
	if(errno != ENOENT) syslog(LOG_ERR, "readlink(defaultbc): %m");
	return 0;
    }

    activelink[len] = '\0';
    
    /* Only compare the part of the file after the last /,
     * since that is what timsieved does */
    file = strrchr(filename, '/');
    link = strrchr(activelink, '/');
    if(!file) file = filename;
    else file++;
    if(!link) link = activelink;
    else link++;

    if (!strcmp(file, link)) {
	return 1;
    } else {
	return 0;
    }
}

struct dump_annotation_rock
{
    struct protstream *pout;
    const char *tag;
};

static int dump_annotations(const char *mailbox __attribute__((unused)),
			    const char *entry,
			    const char *userid,
			    struct annotation_data *attrib, void *rock) 
{
    struct dump_annotation_rock *ctx = (struct dump_annotation_rock *)rock;

    /* "A-" userid entry */
    /* entry is delimited by its leading / */
    unsigned long ename_size = 2 + strlen(userid) +  strlen(entry);

    /* Transfer all attributes for this annotation, don't transfer size
     * separately since that can be implicitly determined */
    prot_printf(ctx->pout,
		" {%ld%s}\r\nA-%s%s (%ld {" SIZE_T_FMT "%s}\r\n%s"
		" {" SIZE_T_FMT "%s}\r\n%s)",
		ename_size, (!ctx->tag ? "+" : ""),
		userid, entry,
		attrib->modifiedsince,
		attrib->size, (!ctx->tag ? "+" : ""),
		attrib->value,
		strlen(attrib->contenttype), (!ctx->tag ? "+" : ""),
		attrib->contenttype);

    return 0;
}

static int dump_file(int first, int sync,
		     struct protstream *pin, struct protstream *pout,
		     const char *filename, const char *ftag)
{
    int filefd;
    const char *base;
    unsigned long len;
    struct stat sbuf;
    char c;

    /* map file */
    syslog(LOG_DEBUG, "wanting to dump %s", filename);
    filefd = open(filename, O_RDONLY, 0666);
    if (filefd == -1) {
	syslog(LOG_ERR, "IOERROR: open on %s: %m", filename);
	return IMAP_SYS_ERROR;
    }
    
    if (fstat(filefd, &sbuf) == -1) {
	syslog(LOG_ERR, "IOERROR: fstat on %s: %m", filename);
	fatal("can't fstat message file", EC_OSFILE);
    }	

    base = NULL;
    len = 0;

    map_refresh(filefd, 1, &base, &len, sbuf.st_size, filename, NULL);

    close(filefd);

    /* send: name, size, and contents */
    if (first) {
	prot_printf(pout, " {" SIZE_T_FMT "}\r\n", strlen(ftag));

	if (sync) {
	    /* synchronize */
	    c = prot_getc(pin);
	    eatline(pin, c); /* We eat it no matter what */
	    if (c != '+') {
		/* Synchronization Failure, Abort! */
		syslog(LOG_ERR, "Sync Error: expected '+' got '%c'",c);
		return IMAP_SERVER_UNAVAILABLE;
	    }
	}

	prot_printf(pout, "%s {%lu%s}\r\n",
		    ftag, len, (sync ? "+" : ""));
    } else {
	prot_printf(pout, " {" SIZE_T_FMT "%s}\r\n%s {%lu%s}\r\n",
		    strlen(ftag), (sync ? "+" : ""),
		    ftag, len, (sync ? "+" : ""));
    }
    prot_write(pout, base, len);
    map_free(&base, &len);

    return 0;
}

struct data_file {
    int metaname;
    char *fname;
};

static struct data_file data_files[] = {
    { META_HEADER, "cyrus.header" },
    { META_INDEX,  "cyrus.index"  },
    { META_CACHE,  "cyrus.cache"  },
    { 0, NULL }
};

enum { SEEN_DB = 0, SUBS_DB = 1, MBOXKEY_DB = 2 };
static int NUM_USER_DATA_FILES = 3;

int dump_mailbox(const char *tag, const char *mbname, int uid_start,
		 struct protstream *pin, struct protstream *pout,
		 struct auth_state *auth_state)
{
    DIR *mbdir = NULL;
    int r = 0;
    struct dirent *next = NULL;
    char filename[MAX_MAILBOX_PATH + 1024];
    char *fname;
    int first = 1;
    struct mailbox *mailbox;
    int i;
    struct data_file *df;

    /* non-null userid means we are moving the user */
    const char *userid = NULL;
    int domainlen = 0;
    char *p = NULL, userbuf[81];
    
    if (config_virtdomains && (p = strchr(mbname, '!')))
	domainlen = p - mbname + 1; /* include separator */

    if (!strncmp(mbname+domainlen, "user.", 5) &&
	!strchr(mbname+domainlen+5, '.')) {
	strcpy(userbuf, mbname+domainlen+5);
	if (domainlen)
	    sprintf(userbuf+strlen(userbuf), "@%.*s", domainlen-1, mbname);
	userid = userbuf;
    }

    r = mailbox_open_irl(mbname, &mailbox);
    if (r) return r;

    mbdir = opendir(mailbox_datapath(mailbox));
    if (!mbdir && errno == EACCES) {
	syslog(LOG_ERR,
	       "could not dump mailbox %s (permission denied)", mailbox->name);
	mailbox_close(&mailbox);
	return IMAP_PERMISSION_DENIED;
    } else if (!mbdir) {
	syslog(LOG_ERR,
	       "could not dump mailbox %s (unknown error)", mailbox->name);
	mailbox_close(&mailbox);
	return IMAP_SYS_ERROR;
    }

    /* after this point we have to both close the directory and unlock
     * the mailbox */

    if (tag) prot_printf(pout, "%s DUMP ", tag);
    (void)prot_putc('(', pout);

    /* The first member is either a number (if it is a quota root), or NIL
     * (if it isn't) */
    {
	struct quota q;

	q.root = mbname;
	r = quota_read(&q, NULL, 0);

	if (!r) {
	    prot_printf(pout, "%d", q.limit);
	} else {
	    prot_printf(pout, "NIL");
	    if (r == IMAP_QUOTAROOT_NONEXISTENT) r = 0;
	}
    }

    /* Dump cyrus data files */
    for (df = data_files; df->metaname; df++) {
	fname = mailbox_meta_fname(mailbox, df->metaname);

	r = dump_file(first, !tag, pin, pout, fname, df->fname);
	if (r) goto done;

	first = 0;
    }

    /* Dump message files */
    while ((next = readdir(mbdir)) != NULL) {
	char *name = next->d_name;  /* Alias */
	char *p = name;
	unsigned long uid;

	/* special case for '.' (well, it gets '..' too) */
	if (name[0] == '.') continue;

	/* skip non-message files */
	while (*p && Uisdigit(*p)) p++;
	if (p[0] != '.' || p[1] != '\0') continue;

	/* ensure (number) is >= our target uid */
        uid = atoi(name);
	if (uid < uid_start) continue;

	/* construct path/filename */
	fname = mailbox_message_fname(mailbox, uid);

	r = dump_file(0, !tag, pin, pout, fname, name);
	if (r) goto done;
    }

    closedir(mbdir);
    mbdir = NULL;

    /* Dump annotations */
    {
	struct dump_annotation_rock actx;
	actx.tag = tag;
	actx.pout = pout;
	annotatemore_findall(mbname, "*", dump_annotations,
			     (void *) &actx, NULL);
    }

    /* Dump user files */
    if (userid) {
	char sieve_path[MAX_MAILBOX_PATH];
	int sieve_usehomedir = config_getswitch(IMAPOPT_SIEVEUSEHOMEDIR);
	char *fname = NULL, *ftag = NULL;

	/* Dump seen and subs files */
	for (i = 0; i< NUM_USER_DATA_FILES; i++) {

	    /* construct path/filename */
	    switch (i) {
	    case SEEN_DB:
		fname = seen_getpath(userid);
		ftag = "SEEN";
		break;
	    case SUBS_DB:
		fname = user_hash_subs(userid);
		ftag = "SUBS";
		break;
	    case MBOXKEY_DB:
		fname = mboxkey_getpath(userid);
		ftag = "MBOXKEY";
		break;
	    default:
		fatal("unknown user data file", EC_OSFILE);
	    }

	    r = dump_file(0, !tag, pin, pout, fname, ftag);
	    free(fname);
	    if (r) {
		/* If an optional file doesn't exist, skip it */
		if (errno == ENOENT) {
		    r = 0;
		    continue;
		}

		goto done;
	    }
	}

	/* Dump sieve files
	 *
	 * xxx can't use home directories currently
	 * (it makes almost no sense in the conext of a murder) */
	if (!sieve_usehomedir) {
	    if (domainlen) {
		*p = '\0'; /* separate domain!mboxname */
		snprintf(sieve_path, sizeof(sieve_path), "%s%s%c/%s/%c/%s",
			 config_getstring(IMAPOPT_SIEVEDIR),
			 FNAME_DOMAINDIR,
			 (char) dir_hash_c(mbname, config_fulldirhash), mbname, 
			 (char) dir_hash_c(p+6, config_fulldirhash), p+6); /* unqualified userid */
		*p = '!'; /* reassemble domain!mboxname */
	    }
	    else {
		snprintf(sieve_path, sizeof(sieve_path), "%s/%c/%s",
			 config_getstring(IMAPOPT_SIEVEDIR),
			 (char) dir_hash_c(userid, config_fulldirhash), userid);
	    }
	    mbdir = opendir(sieve_path);

	    if (!mbdir) {
		syslog(LOG_ERR,
		       "could not dump sieve scripts in %s: %m)", sieve_path);
	    } else {
		char tag_fname[2048];
	    
		while((next = readdir(mbdir)) != NULL) {
		    int length=strlen(next->d_name);
		    /* 7 == strlen(".script"); 3 == strlen(".bc") */
		    if ((length >= 7 &&
			 !strcmp(next->d_name + (length - 7), ".script")) ||
			(length >= 3 &&
			 !strcmp(next->d_name + (length - 3), ".bc")))
		    {
			/* create tagged name */
			if(sieve_isactive(sieve_path, next->d_name)) {
			    snprintf(tag_fname, sizeof(tag_fname),
				     "SIEVED-%s", next->d_name);
			} else {
			    snprintf(tag_fname, sizeof(tag_fname),
				     "SIEVE-%s", next->d_name);
			}

			/* construct path/filename */
			snprintf(filename, sizeof(filename), "%s/%s",
				 sieve_path, next->d_name);

			/* dump file */
			r = dump_file(0, !tag, pin, pout, filename, tag_fname);
			if (r) goto done;
		    }
		}

		closedir(mbdir);
		mbdir = NULL;
	    }
	} /* end if !sieve_userhomedir */
	    
    } /* end if userid */

    prot_printf(pout,")\r\n");
 done:
    prot_flush(pout);

    mailbox_close(&mailbox);
    if (mbdir) closedir(mbdir);

    return r;
}

int undump_mailbox(const char *mbname, 
		   struct protstream *pin, struct protstream *pout,
		   struct auth_state *auth_state)
{
    struct buf file, data;
    char c;
    int r = 0;
    int curfile = -1;
    struct mailbox *mailbox;
    char sieve_path[2048];
    int sieve_usehomedir = config_getswitch(IMAPOPT_SIEVEUSEHOMEDIR);
    int domainlen = 0;
    char *p = NULL, userbuf[81];
    char *userid, *annotation, *contenttype, *content;
    char *seen_file, *mboxkey_file;

    memset(&file, 0, sizeof(file));
    memset(&data, 0, sizeof(data));

    c = getword(pin, &data);

    if (config_virtdomains && (p = strchr(mbname, '!')))
	domainlen = p - mbname + 1; /* include separator */

    if (!strncmp(mbname+domainlen, "user.", 5) &&
       !strchr(mbname+domainlen+5, '.')) {
	strcpy(userbuf, mbname+domainlen+5);
	if (domainlen)
	    sprintf(userbuf+strlen(userbuf), "@%.*s", domainlen-1, mbname);
	userid = userbuf;

	if(!sieve_usehomedir) {
	    if (domainlen) {
		*p = '\0'; /* separate domain!mboxname */
		snprintf(sieve_path, sizeof(sieve_path), "%s%s%c/%s/%c/%s",
			 config_getstring(IMAPOPT_SIEVEDIR),
			 FNAME_DOMAINDIR,
			 (char) dir_hash_c(mbname, config_fulldirhash), mbname, 
			 (char) dir_hash_c(p+6, config_fulldirhash), p+6); /* unqualified userid */
		*p = '!'; /* reassemble domain!mboxname */
	    }
	    else {
		snprintf(sieve_path, sizeof(sieve_path), "%s/%c/%s",
			 config_getstring(IMAPOPT_SIEVEDIR),
			 (char) dir_hash_c(userid, config_fulldirhash), userid);
	    }
	}
    }

    /* we better be in a list now */
    if (c != '(' || data.s[0]) {
	buf_free(&data);
	eatline(pin, c);
	return IMAP_PROTOCOL_BAD_PARAMETERS;
    }
    
    /* We should now have a number or a NIL */
    c = getword(pin, &data);
    if(!strcmp(data.s, "NIL")) {
	/* Remove any existing quotaroot */
	mboxlist_unsetquota(mbname);
    } else if(imparse_isnumber(data.s)) {
	/* Set a Quota */ 
	mboxlist_setquota(mbname, atoi(data.s), 0);
    } else {
	/* Huh? */
	buf_free(&data);
	eatline(pin, c);
	return IMAP_PROTOCOL_BAD_PARAMETERS;
    }

    if(c != ' ' && c != ')') {
	buf_free(&data);
	eatline(pin, c);
	return IMAP_PROTOCOL_BAD_PARAMETERS;
    } else if(c == ')') {
	goto done;
    }
    
    r = mailbox_open_iwl(mbname, &mailbox);
    if(r) goto done;

    while(1) {
	char fnamebuf[MAX_MAILBOX_PATH + 1024];
	int isnowait, sawdigit;
	unsigned long size;
	unsigned long cutoff = ULONG_MAX / 10;
	unsigned digit, cutlim = ULONG_MAX % 10;
	annotation = NULL;
	contenttype = NULL;
	content = NULL;
	seen_file = NULL;
	mboxkey_file = NULL;
	
	c = getastring(pin, pout, &file);
	if(c != ' ') {
	    r = IMAP_PROTOCOL_ERROR;
	    goto done;
	}

	if(!strncmp(file.s, "A-", 2)) {
	    /* Annotation */
	    size_t contentsize;
	    uint32_t modtime = 0;
	    int i;
	    char *tmpuserid;
	    const char *ptr;

	    for(i=2; file.s[i]; i++) {
		if(file.s[i] == '/') break;
	    }
	    if(!file.s[i]) {
		r = IMAP_PROTOCOL_ERROR;
		goto done;
	    }
	    tmpuserid = xmalloc(i-2+1);
	    
	    memcpy(tmpuserid, &(file.s[2]), i-2);
	    tmpuserid[i-2] = '\0';
	    
	    annotation = xstrdup(&(file.s[i]));

	    if(prot_getc(pin) != '(') {
		r = IMAP_PROTOCOL_ERROR;
		free(tmpuserid);
		goto done;
	    }	    

	    /* Parse the modtime */
	    c = getword(pin, &data);
	    if (c != ' ')  {
		r = IMAP_PROTOCOL_ERROR;
		free(tmpuserid);
		goto done;
	    }

	    r = parseuint32(data.s, &ptr, &modtime);
	    if (r || *ptr) {
		r = IMAP_PROTOCOL_ERROR;
		free(tmpuserid);
		goto done;
	    }

	    c = getbastring(pin, pout, &data);
	    /* xxx binary */
	    content = xstrdup(data.s);
	    contentsize = data.len;

	    if(c != ' ') {
		r = IMAP_PROTOCOL_ERROR;
		free(tmpuserid);
		goto done;
	    }

	    c = getastring(pin, pout, &data);
	    contenttype = xstrdup(data.s);
	    
	    if(c != ')') {
		r = IMAP_PROTOCOL_ERROR;
		free(tmpuserid);
		goto done;
	    }

	    annotatemore_write_entry(mbname, annotation, tmpuserid, content,
				     contenttype, contentsize, modtime, NULL);
    
	    free(tmpuserid);
	    free(annotation);
	    free(content);
	    free(contenttype);

	    c = prot_getc(pin);
	    if(c == ')') break; /* that was the last item */
	    else if(c != ' ') {
		r = IMAP_PROTOCOL_ERROR;
		goto done;
	    }

	    continue;
	}

	/* read size of literal */
	c = prot_getc(pin);
	if (c != '{') {
	    r = IMAP_PROTOCOL_ERROR;
	    goto done;
	}

	size = isnowait = sawdigit = 0;
	while ((c = prot_getc(pin)) != EOF && isdigit(c)) {
	    sawdigit = 1;
	    digit = c - '0';
	    /* check for overflow */
	    if (size > cutoff || (size == cutoff && digit > cutlim)) {
		fatal("literal too big", EC_IOERR);
	    }
	    size = size*10 + digit;
	}
	if (c == '+') {
	    isnowait++;
	    c = prot_getc(pin);
	}
	if (c == '}') {
	    c = prot_getc(pin);
	    if (c == '\r') c = prot_getc(pin);
	}
	if (!sawdigit || c != '\n') {
	    r = IMAP_PROTOCOL_ERROR;
	    goto done;
	}

	if (!isnowait) {
	    /* Tell client to send the message */
	    prot_printf(pout, "+ go ahead\r\n");
	    prot_flush(pout);
	}

	if(userid && !strcmp(file.s, "SUBS")) {
	    /* overwriting this outright is absolutely what we want to do */
	    char *s = user_hash_subs(userid);
	    strlcpy(fnamebuf, s, sizeof(fnamebuf));
	    free(s);
	} else if (userid && !strcmp(file.s, "SEEN")) {
	    seen_file = seen_getpath(userid);

	    snprintf(fnamebuf,sizeof(fnamebuf),"%s.%d",seen_file,getpid());
	} else if (userid && !strcmp(file.s, "MBOXKEY")) {
	    mboxkey_file = mboxkey_getpath(userid);

	    snprintf(fnamebuf,sizeof(fnamebuf),"%s.%d",mboxkey_file,getpid());
	} else if (userid && !strncmp(file.s, "SIEVE", 5)) {
	    int isdefault = !strncmp(file.s, "SIEVED", 6);
	    char *realname;
	    int ret;
	    
	    /* skip prefixes */
	    if(isdefault) realname = file.s + 7;
	    else realname = file.s + 6;

	    if(sieve_usehomedir) {
		/* xxx! */
		syslog(LOG_ERR,
		       "dropping sieve file %s since this host is " \
		       "configured for sieve_usehomedir",
		       realname);
		continue;
	    } else {
		if(snprintf(fnamebuf, sizeof(fnamebuf),
			    "%s/%s", sieve_path, realname) == -1) {
		    r = IMAP_PROTOCOL_ERROR;
		    goto done;
		} else if(isdefault) {
		    char linkbuf[2048];
		    		    
		    snprintf(linkbuf, sizeof(linkbuf), "%s/defaultbc",
			     sieve_path);
		    ret = symlink(realname, linkbuf);
		    if(ret && errno == ENOENT) {
			if(cyrus_mkdir(linkbuf, 0750) == 0) {
			    ret = symlink(realname, linkbuf);
			}
		    }
		    if(ret) {
			syslog(LOG_ERR, "symlink(%s, %s): %m", realname,
			       linkbuf);
			/* Non-fatal,
			   let's get the file transferred if we can */
		    }
		    
		}
	    }
	} else {
	    struct data_file *df;
	    const char *path;

	    /* see if its one of our datafiles */
	    for (df = data_files; df->fname && strcmp(df->fname, file.s); df++);
	    path = mailbox_meta_fname(mailbox, df->metaname);
	    if (df->metaname && path) {
		strncpy(fnamebuf, path, MAX_MAILBOX_PATH);
	    } else {
		r = IMAP_PROTOCOL_ERROR;
		goto done;
	    }
	}

	/* if we haven't opened it, do so */
	curfile = open(fnamebuf, O_WRONLY|O_TRUNC|O_CREAT, 0640);
	if(curfile == -1 && errno == ENOENT) {
	    if(cyrus_mkdir(fnamebuf, 0750) == 0) {
		curfile = open(fnamebuf, O_WRONLY|O_TRUNC|O_CREAT, 0640);
	    }
	}

	if(curfile == -1) {
	    syslog(LOG_ERR, "IOERROR: creating %s: %m", fnamebuf);
	    r = IMAP_IOERROR;
	    goto done;
	}

	/* write data to file */
	while (size) {
	    char buf[4096+1];
	    int n = prot_read(pin, buf, size > 4096 ? 4096 : size);
	    if (!n) {
		syslog(LOG_ERR,
		       "IOERROR: reading message: unexpected end of file");
		r = IMAP_IOERROR;
		goto done;
	    }

	    size -= n;

	    if (write(curfile, buf, n) != n) {
		syslog(LOG_ERR, "IOERROR: writing %s: %m", fnamebuf);
		r = IMAP_IOERROR;
		goto done;
	    }
	}

	close(curfile);

	/* we were operating on the seen state, so merge it and cleanup */
	if (seen_file) {
	    r = rename(fnamebuf, seen_file);
	    free(seen_file);
	    seen_file = NULL;
	}
	/* we were operating on the seen state, so merge it and cleanup */
	else if (mboxkey_file) {
	    mboxkey_merge(fnamebuf, mboxkey_file);
	    free(mboxkey_file);
	    mboxkey_file = NULL;

	    unlink(fnamebuf);
	}
	
	c = prot_getc(pin);
	if (c == ')') break;
	if (c != ' ') {
	    r = IMAP_PROTOCOL_ERROR;
	    goto done;
	}
    }

 done:
    /* eat the rest of the line, we have atleast a \r\n coming */
    eatline(pin, c);
    buf_free(&file);
    buf_free(&data);

    if (curfile >= 0) close(curfile);
    mailbox_close(&mailbox);
    
    free(annotation);
    free(content);
    free(contenttype);
    free(seen_file);
    free(mboxkey_file);

    mailbox_close(&mailbox);
    
    return r;
}
