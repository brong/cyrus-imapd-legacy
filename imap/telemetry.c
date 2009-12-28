/* telemetry.c -- common server telemetry
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
 * $Id: telemetry.c,v 1.8.6.1 2009/12/28 21:51:40 murch Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>

#include "prot.h"
#include "global.h"

/* create telemetry log; return fd of log */
int telemetry_log(const char *userid, struct protstream *pin, 
		  struct protstream *pout, int usetimestamp)
{
    char buf[1024];
    int fd = -1;
    time_t now;

    if(usetimestamp) {
	struct timeval tv;

	gettimeofday(&tv, NULL);

	/* use sec.clocks */
	snprintf(buf, sizeof(buf), "%s%s%s/%lu.%lu",
		 config_dir, FNAME_LOGDIR, userid,
		 (unsigned long)tv.tv_sec, (unsigned long)tv.tv_usec);
    } else {
	/* use pid */
	snprintf(buf, sizeof(buf), "%s%s%s/%lu", 
		 config_dir, FNAME_LOGDIR, userid, (unsigned long)
		 getpid());
    }

    fd = open(buf, O_CREAT | O_APPEND | O_WRONLY, 0644);

    if (fd != -1) {
	now = time(NULL);
	snprintf(buf, sizeof(buf), "---------- %s %s\n", 
		 userid, ctime(&now));
	write(fd, buf, strlen(buf));

	prot_setlog(pin, fd);
	prot_setlog(pout, fd);
    }
    
    return fd;
}
