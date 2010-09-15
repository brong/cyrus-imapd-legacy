/* service.c -- skeleton for Cyrus service; calls the real main
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
 * $Id: service.c,v 1.61 2010/06/28 12:03:54 brong Exp $
 */

#include <config.h>

#include <stdio.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <fcntl.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <syslog.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <errno.h>
#include <stdlib.h>
#include <sysexits.h>
#include <string.h>
#include <limits.h>

#include "service.h"
#include "libconfig.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "signals.h"

extern int optind, opterr;
extern char *optarg;

/* number of times this service has been used */
static int use_count = 0;
static int verbose = 0;
static int lockfd = -1;
static int newfile = 0;

void notify_master(int fd, int msg)
{
    struct notify_message notifymsg;
    if (verbose) syslog(LOG_DEBUG, "telling master %x", msg);
    notifymsg.message = msg;
    notifymsg.service_pid = getpid();
    if (write(fd, &notifymsg, sizeof(notifymsg)) != sizeof(notifymsg)) {
	syslog(LOG_ERR, "unable to tell master %x: %m", msg);
    }
}

#ifdef HAVE_LIBWRAP
#include <tcpd.h>

int allow_severity = LOG_DEBUG;
int deny_severity = LOG_ERR;

static void libwrap_init(struct request_info *r, char *service)
{
    request_init(r, RQ_DAEMON, service, 0);
}

static int libwrap_ask(struct request_info *r, int fd)
{
    int a;
    struct sockaddr_storage sin;
    socklen_t len = sizeof(sin);

    /* XXX: old FreeBSD didn't fill sockaddr correctly against AF_UNIX */
    sin.ss_family = AF_UNIX;

    /* is this a connection from the local host? */
    if (getpeername(fd, (struct sockaddr *) &sin, &len) == 0) {
	if (((struct sockaddr *)&sin)->sa_family == AF_UNIX) {
	    return 1;
	}
    }
    
    /* i hope using the sock_* functions are legal; it certainly makes
       this code very easy! */
    request_set(r, RQ_FILE, fd, 0);
    sock_host(r);

    a = hosts_access(r);
    if (!a) {
	syslog(deny_severity, "refused connection from %s", eval_client(r));
    }

    return a;
}

#else
struct request_info { int x; };

static void libwrap_init(struct request_info *r __attribute__((unused)),
			 char *service __attribute__((unused)))
{

}

static int libwrap_ask(struct request_info *r __attribute__((unused)),
		       int fd __attribute__((unused)))
{
    return 1;
}

#endif

extern void cyrus_init(const char *, const char *, unsigned);

static int getlockfd(char *service, int id)
{
    char lockfile[1024];
    int fd;

    snprintf(lockfile, sizeof(lockfile), "%s/socket/%s-%d.lock", 
	     config_dir, service, id);
    fd = open(lockfile, O_CREAT | O_RDWR, 0600);
    if (fd < 0) {
	syslog(LOG_ERR, 
	       "locking disabled: couldn't open socket lockfile %s: %m",
	       lockfile);
	lockfd = -1;
	return -1;
    }

    lockfd = fd;
    return 0;
}

static int lockaccept(void)
{
    struct flock alockinfo;
    int rc;

    /* setup the alockinfo structure */
    alockinfo.l_start = 0;
    alockinfo.l_len = 0;
    alockinfo.l_whence = SEEK_SET;

    if (lockfd != -1) {
	alockinfo.l_type = F_WRLCK;
	while ((rc = fcntl(lockfd, F_SETLKW, &alockinfo)) < 0 && 
	       errno == EINTR &&
	       !signals_poll())
	    /* noop */;
	
	if (rc < 0 && signals_poll()) {
	    if (MESSAGE_MASTER_ON_EXIT) 
		notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	    service_abort(0);
	    return -1;
	}

	if (rc < 0) {
	    syslog(LOG_ERR, "fcntl: F_SETLKW: error getting accept lock: %m");
	    if (MESSAGE_MASTER_ON_EXIT) 
		notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	    service_abort(EX_OSERR);
	    return -1;
	}
    }

    return 0;
}

static int unlockaccept(void)
{
    struct flock alockinfo;
    int rc;

    /* setup the alockinfo structure */
    alockinfo.l_start = 0;
    alockinfo.l_len = 0;
    alockinfo.l_whence = SEEK_SET;

    if (lockfd != -1) {
	alockinfo.l_type = F_UNLCK;
	while ((rc = fcntl(lockfd, F_SETLKW, &alockinfo)) < 0 && 
	       errno == EINTR && !signals_poll())
	    /* noop */;

	if (rc < 0) {
	    syslog(LOG_ERR, 
		   "fcntl: F_SETLKW: error releasing accept lock: %m");
	    if (MESSAGE_MASTER_ON_EXIT) 
		notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	    service_abort(EX_OSERR);
	    return -1;
	}
    }

    return 0;
}

#define ARGV_GROW 10

int main(int argc, char **argv, char **envp)
{
    int fdflags;
    int fd;
    char *p = NULL, *service;
    struct request_info request;
    int opt;
    char *alt_config = NULL;
    int call_debugger = 0;
    int max_use = MAX_USE;
    int reuse_timeout = REUSE_TIMEOUT;
    int soctype;
    socklen_t typelen = sizeof(soctype);
    int newargc = 0;
    char **newargv = (char **) xmalloc(ARGV_GROW * sizeof(char *));
    int id;
    char path[PATH_MAX];
    struct stat sbuf;
    ino_t start_ino;
    off_t start_size;
    time_t start_mtime;
    
    opterr = 0; /* disable error reporting,
		   since we don't know about service-specific options */

    newargv[newargc++] = argv[0];

    while ((opt = getopt(argc, argv, "C:U:T:D")) != EOF) {
	if (argv[optind-1][0] == '-' && strlen(argv[optind-1]) > 2) {
	    /* we have merged options */
	    syslog(LOG_ERR,
		   "options and arguments MUST be separated by whitespace");
	    exit(EX_USAGE);
	}

	switch (opt) {
	case 'C': /* alt config file */
	    alt_config = optarg;
	    break;
	case 'U': /* maximum uses */
	    max_use = atoi(optarg);
	    if (max_use < 0) max_use = 0;
	    break;
	case 'T': /* reuse timeout */
	    reuse_timeout = atoi(optarg);
	    if (reuse_timeout < 0) reuse_timeout = 0;
	    break;
	case 'D':
	    call_debugger = 1;
	    break;
	default:
	    if (!((newargc+1) % ARGV_GROW)) { /* time to alloc more */
		newargv = (char **) xrealloc(newargv, (newargc + ARGV_GROW) * 
					     sizeof(char *));
	    }
	    newargv[newargc++] = argv[optind-1];

	    /* option has an argument */
	    if (optind < argc && argv[optind][0] != '-')
		newargv[newargc++] = argv[optind++];

	    break;
	}
    }
    /* grab the remaining arguments */
    for (; optind < argc; optind++) {
	if (!(newargc % ARGV_GROW)) { /* time to alloc more */
	    newargv = (char **) xrealloc(newargv, (newargc + ARGV_GROW) * 
					 sizeof(char *));
	}
	newargv[newargc++] = argv[optind];
    }

    opterr = 1; /* enable error reporting */
    optind = 1; /* reset the option index for parsing by the service */

    p = getenv("CYRUS_VERBOSE");
    if (p) verbose = atoi(p) + 1;

    if (verbose > 30) {
	syslog(LOG_DEBUG, "waiting 15 seconds for debugger");
	sleep(15);
    }

    p = getenv("CYRUS_SERVICE");
    if (p == NULL) {
	syslog(LOG_ERR, "could not getenv(CYRUS_SERVICE); exiting");
	exit(EX_SOFTWARE);
    }
    service = xstrdup(p);

    p = getenv("CYRUS_ID");
    if (p == NULL) {
	syslog(LOG_ERR, "could not getenv(CYRUS_ID); exiting");
	exit(EX_SOFTWARE);
    }
    id = atoi(p);

    /* pick a random timeout between reuse_timeout -> 2*reuse_timeout
     * to avoid massive IO overload if the network connection goes away */
    srand(time(NULL) * getpid());
    reuse_timeout = reuse_timeout + (rand() % reuse_timeout);

    cyrus_init(alt_config, service, 0);

    if (call_debugger) {
	char debugbuf[1024];
	int ret;
	const char *debugger = config_getstring(IMAPOPT_DEBUG_COMMAND);
	if (debugger) {
	    snprintf(debugbuf, sizeof(debugbuf), debugger, 
		     argv[0], getpid(), service);
	    syslog(LOG_DEBUG, "running external debugger: %s", debugbuf);
	    ret = system(debugbuf); /* run debugger */
	    syslog(LOG_DEBUG, "debugger returned exit status: %d", ret);
	}
    }
    syslog(LOG_DEBUG, "executed");

    /* set close on exec */
    fdflags = fcntl(LISTEN_FD, F_GETFD, 0);
    if (fdflags != -1) fdflags = fcntl(LISTEN_FD, F_SETFD, 
				       fdflags | FD_CLOEXEC);
    if (fdflags == -1) {
	syslog(LOG_ERR, "unable to set close on exec: %m");
	if (MESSAGE_MASTER_ON_EXIT) 
	    notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	return 1;
    }
    fdflags = fcntl(STATUS_FD, F_GETFD, 0);
    if (fdflags != -1) fdflags = fcntl(STATUS_FD, F_SETFD, 
				       fdflags | FD_CLOEXEC);
    if (fdflags == -1) {
	syslog(LOG_ERR, "unable to set close on exec: %m");
	if (MESSAGE_MASTER_ON_EXIT) 
	    notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	return 1;
    }

    /* figure out what sort of socket this is */
    if (getsockopt(LISTEN_FD, SOL_SOCKET, SO_TYPE,
		   (char *) &soctype, &typelen) < 0) {
	syslog(LOG_ERR, "getsockopt: SOL_SOCKET: failed to get type: %m");
	if (MESSAGE_MASTER_ON_EXIT) 
	    notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	return 1;
    }

    if (service_init(newargc, newargv, envp) != 0) {
	if (MESSAGE_MASTER_ON_EXIT) 
	    notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	return 1;
    }

    /* determine initial process file inode, size and mtime */
    if (newargv[0][0] == '/')
	strlcpy(path, newargv[0], sizeof(path));
    else
	snprintf(path, sizeof(path), "%s/%s", SERVICE_PATH, newargv[0]);

    stat(path, &sbuf);
    start_ino= sbuf.st_ino;
    start_size = sbuf.st_size;
    start_mtime = sbuf.st_mtime;

    getlockfd(service, id);
    for (;;) {
	/* ok, listen to this socket until someone talks to us */

	/* (re)set signal handlers, including SIGALRM */
	signals_add_handlers(SIGALRM);

	if (use_count > 0) {
	    /* we want to time out after 60 seconds, set an alarm */
	    alarm(reuse_timeout);
	}

	/* lock */
	lockaccept();

	fd = -1;
	while (fd < 0 && !signals_poll()) { /* loop until we succeed */
	    /* check current process file inode, size and mtime */
	    stat(path, &sbuf);
	    if (sbuf.st_ino != start_ino || sbuf.st_size != start_size ||
		sbuf.st_mtime != start_mtime) {
		syslog(LOG_INFO, "process file has changed");
		newfile = 1;
		break;
	    }

	    if (soctype == SOCK_STREAM) {
		fd = accept(LISTEN_FD, NULL, NULL);
		if (fd < 0) {
		    switch (errno) {
		    case EINTR:
            signals_poll();
		    case ENETDOWN:
#ifdef EPROTO
		    case EPROTO:
#endif
		    case ENOPROTOOPT:
		    case EHOSTDOWN:
#ifdef ENONET
		    case ENONET:
#endif
		    case EHOSTUNREACH:
		    case EOPNOTSUPP:
		    case ENETUNREACH:
		    case EAGAIN:
			break;

		    case EINVAL:
			if (signals_poll() == SIGHUP) break;
			
		    default:
			syslog(LOG_ERR, "accept failed: %m");
			if (MESSAGE_MASTER_ON_EXIT) 
			    notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);	
			service_abort(EX_OSERR);
		    }
		}
	    } else {
		/* udp */
		struct sockaddr_storage from;
		socklen_t fromlen;
		char ch;
		int r;
 
		fromlen = sizeof(from);
		r = recvfrom(LISTEN_FD, (void *) &ch, 1, MSG_PEEK,
			     (struct sockaddr *) &from, &fromlen);
		if (r == -1) {
		    syslog(LOG_ERR, "recvfrom failed: %m");
		    if (MESSAGE_MASTER_ON_EXIT) 
			notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
		    service_abort(EX_OSERR);
		}
		fd = LISTEN_FD;
	    }
	}

	/* unlock */
	unlockaccept();

	if (fd < 0 && (signals_poll() || newfile)) {
	    /* timed out (SIGALRM), SIGHUP, or new process file */
	    if (MESSAGE_MASTER_ON_EXIT) 
		notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	    service_abort(0);
	}
	if (fd < 0) {
	    /* how did this happen? - we might have caught a signal. */
	    syslog(LOG_ERR, "accept() failed but we didn't catch it?");
	    if (MESSAGE_MASTER_ON_EXIT) 
		notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	    service_abort(EX_SOFTWARE);
	}

	/* cancel the alarm */
	alarm(0);

	/* tcp only */
	if(soctype == SOCK_STREAM) {
	    libwrap_init(&request, service);

	    if (!libwrap_ask(&request, fd)) {
		/* connection denied! */
		shutdown(fd, SHUT_RDWR);
		close(fd);
		continue;
	    }

	    /* turn on TCP keepalive if set */
	    if (config_getswitch(IMAPOPT_TCP_KEEPALIVE)) {
		int r;
		int optval = 1;
		socklen_t optlen = sizeof(optval);

		r = setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &optval, optlen);
		if (r < 0) {
		    syslog(LOG_ERR, "unable to setsocketopt(SO_KEEPALIVE): %m");
		}
#ifdef TCP_KEEPCNT
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_CNT);
		if (optval) {
		    r = setsockopt(fd, SOL_TCP, TCP_KEEPCNT, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPCNT): %m");
		    }
		}
#endif
#ifdef TCP_KEEPIDLE
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_IDLE);
		if (optval) {
		    r = setsockopt(fd, SOL_TCP, TCP_KEEPIDLE, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPIDLE): %m");
		    }
		}
#endif
#ifdef TCP_KEEPINTVL
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_INTVL);
		if (optval) {
		    r = setsockopt(fd, SOL_TCP, TCP_KEEPINTVL, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPINTVL): %m");
		    }
		}
#endif
	    }
	}

	notify_master(STATUS_FD, MASTER_SERVICE_UNAVAILABLE);
	syslog(LOG_DEBUG, "accepted connection");

	if (fd != 0 && dup2(fd, 0) < 0) {
	    syslog(LOG_ERR, "can't duplicate accepted socket: %m");
	    service_abort(EX_OSERR);
	}
	if (fd != 1 && dup2(fd, 1) < 0) {
	    syslog(LOG_ERR, "can't duplicate accepted socket: %m");
	    service_abort(EX_OSERR);
	}
	if (fd != 2 && dup2(fd, 2) < 0) {
	    syslog(LOG_ERR, "can't duplicate accepted socket: %m");
	    service_abort(EX_OSERR);
	}

	/* tcp only */
	if(soctype == SOCK_STREAM) {
	    if (fd > 2) close(fd);
	}
	
	notify_master(STATUS_FD, MASTER_SERVICE_CONNECTION);
	use_count++;
	service_main(newargc, newargv, envp);
	/* if we returned, we can service another client with this process */

	if (signals_poll() || use_count >= max_use) {
	    /* caught SIGHUP or exceeded max use count */
	    break;
	}

	notify_master(STATUS_FD, MASTER_SERVICE_AVAILABLE);
    }

    service_abort(0);
    return 0;
}
