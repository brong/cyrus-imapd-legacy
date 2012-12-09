/* signals.c -- signal handling functions to allow clean shutdown
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
 * $Id: signals.c,v 1.17 2010/01/06 17:01:40 murch Exp $
 */

#include <config.h>

#include <stdlib.h>
#include <signal.h>
#include <syslog.h>

#include "signals.h"
#include "xmalloc.h"
#include "exitcodes.h"


static volatile sigset_t gotsignals;

static void sighandler(int sig)
{
    /* syslog(LOG_DEBUG, "got signal %d", sig); */
    sigaddset(&gotsignals, sig);
}

static const int catch[] = { SIGHUP, SIGINT, SIGQUIT, SIGALRM, SIGUSR1, SIGUSR2, 0 };

static void signals_handle(int sig)
{
    struct sigaction action;

    sigemptyset(&action.sa_mask);

    action.sa_flags = 0;
#ifdef SA_RESETHAND
    action.sa_flags |= SA_RESETHAND;
#endif

    action.sa_handler = sighandler;

    /* otherwise what?  We're going to break idle pretty hard */
#ifdef SA_RESTART
    action.sa_flags |= SA_RESTART;
#endif
    
    if (sigaction(sig, &action, NULL) < 0)
	fatal("unable to install signal handler for %d: %m", sig);
}

void signals_add_handlers(int alarm)
{
    int i;

    sigemptyset(&gotsignals);
    
    for (i = 0; catch[i] != 0; i++) {
	signals_handle(catch[i]);
    }
}

static shutdownfn *shutdown_cb = NULL;

void signals_set_shutdown(shutdownfn *s)
{
    shutdown_cb = s;
}

/* this is a dodgy type reuse */
static shutdownfn *idle_cb = NULL;

void signals_set_idle(shutdownfn *s)
{
    idle_cb = s;
}

int signals_poll(void)
{
    int i;
    
    for (i = 0; catch[i] != 0; i++) {
	int sig = catch[i];
	if (sigismember(&gotsignals, sig)) {
	    switch(sig) {
	    case SIGINT:
	    case SIGQUIT:
		if (shutdown_cb) shutdown_cb(EC_TEMPFAIL);
		else exit(EC_TEMPFAIL);
		break;
	    case SIGUSR1:
	    case SIGUSR2:
	    case SIGALRM:
		if (!idle_cb) return sig;
		idle_cb(sig);
		sigdelset(&gotsignals, sig);
		break;
	    default:
		return sig;
		break;
	    }
	}
    }

    /* no unhandled signal found */
    return 0;
}
