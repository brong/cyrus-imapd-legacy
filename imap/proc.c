/* proc.c -- Server process registry
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
 * $Id: proc.c,v 1.27 2010/01/06 17:01:38 murch Exp $
 */

#include <config.h>

#include <stdlib.h>
#include <stdio.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <syslog.h>
#include <string.h>

#include "global.h"
#include "exitcodes.h"
#include "xmalloc.h"

#define FNAME_PROCDIR "/proc/"

static char *procfname = 0;
static FILE *procfile = 0;

extern void setproctitle_init(int argc, char **argv, char **envp);
extern void setproctitle(const char *fmt, ...);

int proc_register(progname, clienthost, userid, mailbox)
const char *progname;
const char *clienthost;
const char *userid;
const char *mailbox;
{
    unsigned pid;
    int pos;

    if (!procfname) {
	pid = getpid();
    
	procfname = xmalloc(strlen(config_dir)+sizeof(FNAME_PROCDIR)+10);
	sprintf(procfname, "%s%s%u", config_dir, FNAME_PROCDIR, pid);

	procfile = fopen(procfname, "w+");
	if (!procfile) {
	    syslog(LOG_ERR, "IOERROR: creating %s: %m", procfname);
	    fatal("can't write proc file", EC_IOERR);
	}
    }

    rewind(procfile);
    fprintf(procfile, "%s", clienthost);
    if (userid) {
	fprintf(procfile, "\t%s", userid);
	if (mailbox) {
	    fprintf(procfile, "\t%s", mailbox);
	}
    }
    putc('\n', procfile);
    fflush(procfile);
    pos = ftell(procfile);
    if (pos < 0 || ftruncate(fileno(procfile), pos)) {
	syslog(LOG_ERR, "IOERROR: creating %s: %m", procfname);
	fatal("can't write proc file", EC_IOERR);
    }
	

    setproctitle("%s: %s %s %s", progname, clienthost, 
		 userid ? userid : "",
		 mailbox ? mailbox : "");

    return 0;
}

void proc_cleanup(void)
{
    if (procfname) {
	fclose(procfile);
	unlink(procfname);
	free(procfname);
	procfname = NULL;
    }
}
