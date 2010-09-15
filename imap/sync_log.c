/* sync_log.c -- Cyrus synchonization logging functions
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
 * $Id: sync_log.c,v 1.7 2010/01/06 17:01:41 murch Exp $
 *
 * Original version written by David Carter <dpc22@cam.ac.uk>
 * Rewritten and integrated into Cyrus by Ken Murchison <ken@oceana.com>
 */

/* YYY Need better quoting for obscure filenames: use literals? */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#ifdef HAVE_STDARG_H
#include <stdarg.h>
#else
#include <varargs.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <syslog.h>
#include <errno.h>

#include "sync_log.h"
#include "global.h"
#include "lock.h"
#include "mailbox.h"
#include "retry.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"

static int sync_log_enabled = 0;

struct sync_log_target {
   char file[MAX_MAILBOX_PATH+1];
   struct sync_log_target *next;
};
static struct sync_log_target *sync_target = NULL;

void sync_log_init(void)
{
    struct sync_log_target *item = NULL;
    char *names;
    char *copy;
    char *start;
    char *end;

    sync_log_enabled = config_getswitch(IMAPOPT_SYNC_LOG);
    names = config_getstring(IMAPOPT_SYNC_LOG_NAMES);

    if (names) {
	copy = start = xstrdup(names);
	while (start[0]) {
	    end = strchr(start, ' ');
	    if (end) {
		*end = '\0';
	    }
	    item = sync_target;
	    sync_target = (struct sync_log_target *) xmalloc(sizeof(struct sync_log_target));
	    sync_target->next = item;
	    snprintf(sync_target->file, MAX_MAILBOX_PATH,
	             "%s/sync/%s/log", config_dir, start);
	    if (!end) break;
	    start = end + 1;
	}
	free(copy);
    } else {
	sync_target = (struct sync_log_target *) xmalloc(sizeof(struct sync_log_target));
	sync_target->next = NULL;
	snprintf(sync_target->file, MAX_MAILBOX_PATH,
	         "%s/sync/log", config_dir);
    }
}

void sync_log_done(void)
{
    struct sync_log_target *item = NULL;
    while (sync_target) {
	item = sync_target->next;
	free(sync_target);
	sync_target = item;
    }
}

static void sync_log_base(const char *string, int len)
{
    int fd, rc;
    struct stat sbuffile, sbuffd;
    int retries = 0;
    struct sync_log_target *item = sync_target;

    if (!sync_log_enabled) return;

    while (item) {
	while (retries++ < SYNC_LOG_RETRIES) {
	    fd = open(item->file, O_WRONLY|O_APPEND|O_CREAT, 0640);
	    if (fd < 0 && errno == ENOENT) {
		if (!cyrus_mkdir(item->file, 0755)) {
		    fd = open(item->file, O_WRONLY|O_APPEND|O_CREAT, 0640);
		}
	    }
	    if (fd < 0) {
		syslog(LOG_ERR, "sync_log(): Unable to write to log file %s: %s",
		       item->file, strerror(errno));
		return;
	    }

	    if (lock_blocking(fd) == -1) {
		syslog(LOG_ERR, "sync_log(): Failed to lock %s for %s: %m",
		       item->file, string);
		close(fd);
		return;
	    }

	    /* Check that the file wasn't renamed after it was opened above */
	    if ((fstat(fd, &sbuffd) == 0) &&
		(stat(item->file, &sbuffile) == 0) &&
		(sbuffd.st_ino == sbuffile.st_ino))
		break;

	    close(fd);
	}
	if (retries >= SYNC_LOG_RETRIES) {
	    close(fd);
	    syslog(LOG_ERR,
		   "sync_log(): Failed to lock %s for %s after %d attempts",
		   item->file, string, retries);
	    return;
	}

	if ((rc = retry_write(fd, string, len)) < 0)
	    syslog(LOG_ERR, "write() to %s failed: %s",
		   item->file, strerror(errno));
    
	if (rc < len)
	    syslog(LOG_ERR, "Partial write to %s: %d out of %d only written",
		   item->file, rc, len);

	fsync(fd); /* paranoia */
	close(fd);
	item = item->next;
    }
}

static const char *sync_quote_name(const char *name)
{
    static char buf[MAX_MAILBOX_BUFFER]; /* 2 * MAX_MAILBOX_NAME + 3 */
    const char *s;
    char *p = buf;
    char c;
    int  need_quote = 0;

    if (!name || !*name) return "\"\"";

    s = name;
    while ((c=*s++)) {
        if ((c == ' ') || (c == '\t') || (c == '\\') || (c == '\"') ||
            (c == '(') || (c == ')')  || (c == '{')  || (c == '}'))
            need_quote = 1;
        else if ((c == '\r') || (c == '\n'))
            fatal("Illegal line break in folder name", EC_IOERR);
    }

    if ((s-name) > MAX_MAILBOX_NAME+64) /* XXX: hope that's safe! */
        fatal("word too long", EC_IOERR);

    if (!need_quote) return(name);

    s = name;
    *p++ = '\"';
    while ((c=*s++)) {
        if ((c == '\\') || (c == '\"') || (c == '{') || (c == '}'))
            *p++ = '\\';
        *p++ = c;
    }

    *p++ = '\"';
    *p++ = '\0';
    
    return(buf);
}

#define BUFSIZE 4096

void sync_log(char *fmt, ...)
{
    va_list ap;
    char buf[BUFSIZE+1], *p;
    size_t len;
    int ival;
    const char *sval;

    if (!sync_log_enabled) return;

    va_start(ap, fmt);
    for (len = 0, p = fmt; *p && len < BUFSIZE; p++) {
	if (*p != '%') {
	    buf[len++] = *p;
	    continue;
	}
	switch (*++p) {
	case 'd':
	    ival = va_arg(ap, int);
	    len += snprintf(buf+len, BUFSIZE-len, "%d", ival);
	case 's':
	    sval = va_arg(ap, const char *);
	    sval = sync_quote_name(sval);
	    strlcpy(buf+len, sval, BUFSIZE-len);
	    len += strlen(sval);
	    break;
	default:
	    buf[len++] = *p;
	    break;
	}
    }
    va_end(ap);

    if (buf[len-1] != '\n') buf[len++] = '\n';
    buf[len] = '\0';

    sync_log_base(buf, len);
}
