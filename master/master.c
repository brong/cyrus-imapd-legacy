/* master.c -- IMAP master process to handle recovery, checkpointing, spawning
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
 * $Id: master.c,v 1.117 2010/04/19 19:54:26 murch Exp $
 */

#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#ifdef HAVE_SYS_RESOURCE_H
#include <sys/resource.h>
#endif
#include <fcntl.h>
#include <signal.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <syslog.h>
#include <netdb.h>
#include <ctype.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/un.h>
#include <arpa/inet.h>
#include <sysexits.h>
#include <errno.h>
#include <limits.h>

#ifndef INADDR_NONE
#define INADDR_NONE 0xffffffff
#endif

#ifndef INADDR_ANY
#define INADDR_ANY 0x00000000
#endif

#if !defined(IPV6_V6ONLY) && defined(IPV6_BINDV6ONLY)
#define	IPV6_V6ONLY	IPV6_BINDV6ONLY
#endif

#if defined(HAVE_NETSNMP)
  #include <net-snmp/net-snmp-config.h>
  #include <net-snmp/net-snmp-includes.h>
  #include <net-snmp/agent/net-snmp-agent-includes.h>
#if defined(HAVE_NET_SNMP_AGENT_AGENT_MODULE_CONFIG_H)
    #include <net-snmp/agent/agent_module_config.h>
#endif

  #include "cyrusMasterMIB.h"


  /* Use our own definitions for these */
  #undef TOUPPER
  #undef TOLOWER

#elif defined(HAVE_UCDSNMP)
  #include <ucd-snmp/ucd-snmp-config.h>
  #include <ucd-snmp/ucd-snmp-includes.h>
  #include <ucd-snmp/ucd-snmp-agent-includes.h>

  #include "cyrusMasterMIB.h"

  int allow_severity = LOG_DEBUG;
  int deny_severity = LOG_ERR;
#endif

#include "masterconf.h"

#include "master.h"
#include "service.h"

#include "lock.h"
#include "util.h"
#include "xmalloc.h"

enum {
    become_cyrus_early = 1,
    child_table_size = 10000,
    child_table_inc = 100
};

static int verbose = 0;
static int listen_queue_backlog = 32;
static int pidfd = -1;

static volatile int in_shutdown = 0;

const char *MASTER_CONFIG_FILENAME = DEFAULT_MASTER_CONFIG_FILENAME;

#define SERVICE_NONE -1
#define SERVICE_MAX  INT_MAX-10
#define SERVICENAME(x) ((x) ? x : "unknown")

struct service *Services = NULL;
int allocservices = 0;
int nservices = 0;

/* make libcyrus_min happy */
int config_need_data = 0;

struct event {
    char *name;
    time_t mark;
    time_t period;
    time_t hour;
    time_t min;
    int periodic;
    char *const *exec;
    struct event *next;
};
static struct event *schedule = NULL;

enum sstate {
    SERVICE_STATE_UNKNOWN = 0,  /* duh */
    SERVICE_STATE_INIT    = 1,  /* Service forked - UNUSED */
    SERVICE_STATE_READY   = 2,  /* Service told us it is ready */
    				/* or it just forked and has not
				 * talked to us yet */
    SERVICE_STATE_BUSY    = 3,  /* Service told us it is not ready */
    SERVICE_STATE_DEAD    = 4   /* We received a sigchld from this service */
};

struct centry {
    pid_t pid;
    enum sstate service_state;	/* SERVICE_STATE_* */
    time_t janitor_deadline;	/* cleanup deadline */
    int si;			/* Services[] index */
    struct centry *next;
};
static struct centry *ctable[child_table_size];
static struct centry *cfreelist;

static int janitor_frequency = 1;	/* Janitor sweeps per second */
static int janitor_position;		/* Entry to begin at in next sweep */
static struct timeval janitor_mark;	/* Last time janitor did a sweep */

void limit_fds(rlim_t);
void schedule_event(struct event *a);

void fatal(const char *msg, int code)
{
    syslog(LOG_CRIT, "%s", msg);
    syslog(LOG_NOTICE, "exiting");
    exit(code);
}

void event_free(struct event *a) 
{
    if(a->exec) free((char**)a->exec);
    if(a->name) free((char*)a->name);
    free(a);
}

void get_prog(char *path, unsigned size, char *const *cmd)
{
    if (cmd[0][0] == '/') {
	/* master lacks strlcpy, due to no libcyrus */
	snprintf(path, size, "%s", cmd[0]);
    }
    else snprintf(path, size, "%s/%s", SERVICE_PATH, cmd[0]);
}

void get_statsock(int filedes[2])
{
    int r, fdflags;

    r = pipe(filedes);
    if (r != 0) {
	fatal("couldn't create status socket: %m", 1);
    }

    /* we don't want the master blocking on reads */
    fdflags = fcntl(filedes[0], F_GETFL, 0);
    if (fdflags != -1) fdflags = fcntl(filedes[0], F_SETFL, 
				       fdflags | O_NONBLOCK);
    if (fdflags == -1) {
	fatal("unable to set non-blocking: %m", 1);
    }
    /* we don't want the services to be able to read from it */
    fdflags = fcntl(filedes[0], F_GETFD, 0);
    if (fdflags != -1) fdflags = fcntl(filedes[0], F_SETFD, 
				       fdflags | FD_CLOEXEC);
    if (fdflags == -1) {
	fatal("unable to set close-on-exec: %m", 1);
    }
}

/* return a new 'centry', either from the freelist or by malloc'ing it */
static struct centry *get_centry(void)
{
    struct centry *t;

    if (!cfreelist) {
	/* create child_table_inc more and add them to the freelist */
	struct centry *n;
	int i;

	n = xmalloc(child_table_inc * sizeof(struct centry));
	cfreelist = n;
	for (i = 0; i < child_table_inc - 1; i++) {
	    n[i].next = n + (i + 1);
	}
	/* i == child_table_inc - 1, last item in block */
	n[i].next = NULL;
    }

    t = cfreelist;
    cfreelist = cfreelist->next;

    t->janitor_deadline = 0;

    return t;
}

/* see if 'listen' parameter has both hostname and port, or just port */
char *parse_listen(char *listen)
{
    char *cp;
    char *port = NULL;

    if ((cp = strrchr(listen,']')) != NULL) {
        /* ":port" after closing bracket for IP address? */
        if (*cp++ != '\0' && *cp == ':') {
            *cp++ = '\0';
            if (*cp != '\0') {
                port = cp;
            } 
        }
    } else if ((cp = strrchr(listen,':')) != NULL) {
        /* ":port" after hostname? */
        *cp++ = '\0';
        if (*cp != '\0') {
            port = cp;
        }
    }
    return port;
}

char *parse_host(char *listen)
{
    char *cp;

    /* do we have a hostname, or IP number? */
    /* XXX are brackets necessary  */
    if (*listen == '[') {
        listen++;  /* skip first bracket */
        if ((cp = strrchr(listen,']')) != NULL) {
            *cp = '\0';
        }
    }
    return listen;
}

int verify_service_file(char *const *filename)
{
    char path[PATH_MAX];
    struct stat statbuf;
    
    get_prog(path, sizeof(path), filename);
    if (stat(path, &statbuf)) return 0;
    if (! S_ISREG(statbuf.st_mode)) return 0;
    return statbuf.st_mode & S_IXUSR;
}

void service_create(struct service *s)
{
    struct service service0, service;
    struct addrinfo hints, *res0, *res;
    int error, nsocket = 0;
    struct sockaddr_un sunsock;
    mode_t oldumask;
    int on = 1;
    int res0_is_local = 0;
    int r;

    if (s->associate > 0)
	return;			/* service is already activated */

    if (!s->name)
	fatal("Serious software bug found: service_create() called on unnamed service!",
		EX_SOFTWARE);

    if (s->listen[0] == '/') { /* unix socket */
	res0_is_local = 1;
	res0 = (struct addrinfo *)malloc(sizeof(struct addrinfo));
	if (!res0)
	    fatal("out of memory", EX_UNAVAILABLE);
	memset(res0, 0, sizeof(struct addrinfo));
	res0->ai_flags = AI_PASSIVE;
	res0->ai_family = PF_UNIX;
	if(!strcmp(s->proto, "tcp")) {
	    res0->ai_socktype = SOCK_STREAM;
	} else {
	    /* udp */
	    res0->ai_socktype = SOCK_DGRAM;
	}
 	res0->ai_addr = (struct sockaddr *)&sunsock;
 	res0->ai_addrlen = sizeof(sunsock.sun_family) + strlen(s->listen) + 1;
#ifdef SIN6_LEN
 	res0->ai_addrlen += sizeof(sunsock.sun_len);
 	sunsock.sun_len = res0->ai_addrlen;
#endif
	sunsock.sun_family = AF_UNIX;
	strcpy(sunsock.sun_path, s->listen);
	unlink(s->listen);
    } else { /* inet socket */
	char *listen, *port;
	char *listen_addr;
	
 	memset(&hints, 0, sizeof(hints));
 	hints.ai_flags = AI_PASSIVE;
 	if (!strcmp(s->proto, "tcp")) {
 	    hints.ai_family = PF_UNSPEC;
 	    hints.ai_socktype = SOCK_STREAM;
 	} else if (!strcmp(s->proto, "tcp4")) {
 	    hints.ai_family = PF_INET;
 	    hints.ai_socktype = SOCK_STREAM;
#ifdef PF_INET6
 	} else if (!strcmp(s->proto, "tcp6")) {
 	    hints.ai_family = PF_INET6;
 	    hints.ai_socktype = SOCK_STREAM;
#endif
 	} else if (!strcmp(s->proto, "udp")) {
 	    hints.ai_family = PF_UNSPEC;
 	    hints.ai_socktype = SOCK_DGRAM;
 	} else if (!strcmp(s->proto, "udp4")) {
 	    hints.ai_family = PF_INET;
 	    hints.ai_socktype = SOCK_DGRAM;
#ifdef PF_INET6 
	} else if (!strcmp(s->proto, "udp6")) {
 	    hints.ai_family = PF_INET6;
 	    hints.ai_socktype = SOCK_DGRAM;
#endif
 	} else {
  	    syslog(LOG_INFO, "invalid proto '%s', disabling %s",
		   s->proto, s->name);
 	    s->exec = NULL;
 	    return;
 	}

	/* parse_listen() and resolve_host() are destructive,
	 * so make a work copy of s->listen
	 */
	listen = xstrdup(s->listen);

        if ((port = parse_listen(listen)) == NULL) {
            /* listen IS the port */
	    port = listen;
	    listen_addr = NULL;
        } else {
            /* s->listen is now just the address */
	    listen_addr = parse_host(listen);
	    if (*listen_addr == '\0')
		listen_addr = NULL;	    
        }

	error = getaddrinfo(listen_addr, port, &hints, &res0);

	free(listen);

	if (error) {
	    syslog(LOG_INFO, "%s, disabling %s", gai_strerror(error), s->name);
	    s->exec = NULL;
	    return;
	}
    }

    memcpy(&service0, s, sizeof(struct service));

    for (res = res0; res; res = res->ai_next) {
	if (s->socket > 0) {
	    memcpy(&service, &service0, sizeof(struct service));
	    s = &service;
	}

	s->socket = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
	if (s->socket < 0) {
	    s->socket = 0;
	    if (verbose > 2)
		syslog(LOG_ERR, "unable to open %s socket: %m", s->name);
	    continue;
	}

	/* allow reuse of address */
	r = setsockopt(s->socket, SOL_SOCKET, SO_REUSEADDR, 
		       (void *) &on, sizeof(on));
	if (r < 0) {
	    syslog(LOG_ERR, "unable to setsocketopt(SO_REUSEADDR): %m");
	}
#if defined(IPV6_V6ONLY) && !(defined(__FreeBSD__) && __FreeBSD__ < 3)
	if (res->ai_family == AF_INET6) {
	    r = setsockopt(s->socket, IPPROTO_IPV6, IPV6_V6ONLY,
			   (void *) &on, sizeof(on));
	    if (r < 0) {
		syslog(LOG_ERR, "unable to setsocketopt(IPV6_V6ONLY): %m");
	    }
	}
#endif

	/* set IP ToS if supported */
#if defined(SOL_IP) && defined(IP_TOS)
	r = setsockopt(s->socket, SOL_IP, IP_TOS,
		       (void *) &config_qosmarking, sizeof(config_qosmarking));
	if (r < 0) {
	    syslog(LOG_WARNING, "unable to setsocketopt(IP_TOS): %m");
	}
#endif

	oldumask = umask((mode_t) 0); /* for linux */
	r = bind(s->socket, res->ai_addr, res->ai_addrlen);
	umask(oldumask);
	if (r < 0) {
	    close(s->socket);
	    s->socket = 0;
	    if (verbose > 2)
		syslog(LOG_ERR, "unable to bind to %s socket: %m", s->name);
	    continue;
	}
	
	if (s->listen[0] == '/') { /* unix socket */
	    /* for DUX, where this isn't the default.
	       (harmlessly fails on some systems) */
	    chmod(s->listen, (mode_t) 0777);
	}
	
	if ((!strcmp(s->proto, "tcp") || !strcmp(s->proto, "tcp4")
	     || !strcmp(s->proto, "tcp6"))
	    && listen(s->socket, listen_queue_backlog) < 0) {
	    syslog(LOG_ERR, "unable to listen to %s socket: %m", s->name);
	    close(s->socket);
	    s->socket = 0;
	    continue;
	}
	
	s->ready_workers = 0;
	s->associate = nsocket;
	s->family = res->ai_family;
	
	get_statsock(s->stat);
	
	if (s == &service) {
	    if (nservices == allocservices) {
		if (allocservices > SERVICE_MAX - 5)
		    fatal("out of service structures, please restart", EX_UNAVAILABLE);
		Services = xrealloc(Services, 
				    (allocservices+=5) * sizeof(struct service));
		if (!Services) fatal("out of memory", EX_UNAVAILABLE);
	    }
	    memcpy(&Services[nservices++], s, sizeof(struct service));
	}
	nsocket++;
    }
    if (res0) {
	if(res0_is_local)
	    free(res0);
	else
	    freeaddrinfo(res0);
    }
    if (nsocket <= 0) {
	syslog(LOG_ERR, "unable to create %s listener socket: %m", s->name);
	s->exec = NULL;
	return;
    }
}

void run_startup(char **cmd)
{
    pid_t pid;
    int status;
    char path[PATH_MAX];

    switch (pid = fork()) {
    case -1:
	syslog(LOG_CRIT, "can't fork process to run startup: %m");
	fatal("can't run startup", 1);
	break;
	
    case 0:
	/* Child - Release our pidfile lock. */
	if(pidfd != -1) close(pidfd);

	if (become_cyrus() != 0) {
	    syslog(LOG_ERR, "can't change to the cyrus user: %m");
	    exit(1);
	}

	limit_fds(256);

	get_prog(path, sizeof(path), cmd);
	syslog(LOG_DEBUG, "about to exec %s", path);
	execv(path, cmd);
	syslog(LOG_ERR, "can't exec %s for startup: %m", path);
	exit(EX_OSERR);
	
    default: /* parent */
	if (waitpid(pid, &status, 0) < 0) {
	    syslog(LOG_ERR, "waitpid(): %m");
	} else if (status != 0) {
	    if (WIFEXITED(status)) {
		syslog(LOG_ERR, "process %d exited, status %d\n", pid, 
		       WEXITSTATUS(status));
	    }
	    if (WIFSIGNALED(status)) {
		syslog(LOG_ERR, 
		       "process %d exited, signaled to death by %d\n",
		       pid, WTERMSIG(status));
	    }
	}
	break;
    }
}

void fcntl_unset(int fd, int flag)
{
    int fdflags = fcntl(fd, F_GETFD, 0);
    if (fdflags != -1) fdflags = fcntl(STATUS_FD, F_SETFD, 
				       fdflags & ~flag);
    if (fdflags == -1) {
	syslog(LOG_ERR, "fcntl(): unable to unset %d: %m", flag);
    }
}

void spawn_service(const int si)
{
    /* Note that there is logic that depends on this being 2 */
    const int FORKRATE_INTERVAL = 2;

    pid_t p;
    int i;
    char path[PATH_MAX];
    static char name_env[100], name_env2[100];
    struct centry *c;
    struct service * const s = &Services[si];
    time_t now = time(NULL);

    if (!s->name) {
	fatal("Serious software bug found: spawn_service() called on unnamed service!",
		EX_SOFTWARE);
    }

    /* update our fork rate */
    if(now - s->last_interval_start >= FORKRATE_INTERVAL) {
	int interval;

	s->forkrate = (s->interval_forks/2) + (s->forkrate/2);
	s->interval_forks = 0;
	s->last_interval_start += FORKRATE_INTERVAL;

	/* if there is an even wider window, however, we need
	 * to account for a good deal of zeros, we can do this at once */
	interval = now - s->last_interval_start;

	if(interval > 2) {
	    int skipped_intervals = interval / FORKRATE_INTERVAL;
	    /* avoid a > 30 bit right shift) */
	    if(skipped_intervals > 30) s->forkrate = 0;
	    else {
		/* divide by 2^(skipped_intervals).
		 * this is the logic mentioned in the comment above */
		s->forkrate >>= skipped_intervals;
		s->last_interval_start = now;
	    }
	}
    }

    /* If we've been busy lately, we will refuse to fork! */
    /* (We schedule a wakeup call for sometime soon though to be
     * sure that we don't wait to do the fork that is required forever! */
    if(s->maxforkrate && s->forkrate >= s->maxforkrate) {
	struct event *evt = (struct event *) xmalloc(sizeof(struct event));

	memset(evt, 0, sizeof(struct event));

	evt->name = xstrdup("forkrate wakeup call");
	evt->mark = time(NULL) + FORKRATE_INTERVAL;
	schedule_event(evt);

	return;
    }

    switch (p = fork()) {
    case -1:
	syslog(LOG_ERR, "can't fork process to run service %s: %m", s->name);
	break;

    case 0:
	/* Child - Release our pidfile lock. */
	if(pidfd != -1) close(pidfd);

	if (become_cyrus() != 0) {
	    syslog(LOG_ERR, "can't change to the cyrus user");
	    exit(1);
	}

	get_prog(path, sizeof(path), s->exec);
	if (dup2(s->stat[1], STATUS_FD) < 0) {
	    syslog(LOG_ERR, "can't duplicate status fd: %m");
	    exit(1);
	}
	if (dup2(s->socket, LISTEN_FD) < 0) {
	    syslog(LOG_ERR, "can't duplicate listener fd: %m");
	    exit(1);
	}

	fcntl_unset(STATUS_FD, FD_CLOEXEC);
	fcntl_unset(LISTEN_FD, FD_CLOEXEC);

	/* close all listeners */
	for (i = 0; i < nservices; i++) {
	    if (Services[i].socket > 0) close(Services[i].socket);
	    if (Services[i].stat[0] > 0) close(Services[i].stat[0]);
	    if (Services[i].stat[1] > 0) close(Services[i].stat[1]);
	}
	limit_fds(s->maxfds);

	syslog(LOG_DEBUG, "about to exec %s", path);

	/* add service name to environment */
	snprintf(name_env, sizeof(name_env), "CYRUS_SERVICE=%s", s->name);
	putenv(name_env);
	snprintf(name_env2, sizeof(name_env2), "CYRUS_ID=%d", s->associate);
	putenv(name_env2);

	execv(path, s->exec);
	syslog(LOG_ERR, "couldn't exec %s: %m", path);
	exit(EX_OSERR);

    default:			/* parent */
	s->ready_workers++;
	s->interval_forks++;
	s->nforks++;
	s->nactive++;

	/* add to child table */
	c = get_centry();
	c->pid = p;
	c->service_state = SERVICE_STATE_READY;
	c->si = si;
	c->next = ctable[p % child_table_size];
	ctable[p % child_table_size] = c;
	break;
    }

}

void schedule_event(struct event *a)
{
    struct event *ptr;

    if (! a->name)
	fatal("Serious software bug found: schedule_event() called on unnamed event!",
		EX_SOFTWARE);

    if (!schedule || a->mark < schedule->mark) {
	a->next = schedule;
	schedule = a;
	
	return;
    }
    for (ptr = schedule; ptr->next && ptr->next->mark <= a->mark; 
	 ptr = ptr->next) ;

    /* insert a */
    a->next = ptr->next;
    ptr->next = a;
}

void spawn_schedule(time_t now)
{
    struct event *a, *b;
    int i;
    char path[PATH_MAX];
    pid_t p;
    struct centry *c;

    a = NULL;
    /* update schedule accordingly */
    while (schedule && schedule->mark <= now) {
	/* delete from schedule, insert into a */
	struct event *ptr = schedule;

	/* delete */
	schedule = schedule->next;

	/* insert */
	ptr->next = a;
	a = ptr;
    }

    /* run all events */
    while (a && a != schedule) {
	/* if a->exec is NULL, we just used the event to wake up,
	 * so we actually don't need to exec anything at the moment */
	if(a->exec) {
	    switch (p = fork()) {
	    case -1:
		syslog(LOG_CRIT,
		       "can't fork process to run event %s", a->name);
		break;

	    case 0:
		/* Child - Release our pidfile lock. */
		if(pidfd != -1) close(pidfd);

		if (become_cyrus() != 0) {
		    syslog(LOG_ERR, "can't change to the cyrus user");
		    exit(1);
		}
		
		/* close all listeners */
		for (i = 0; i < nservices; i++) {
		    if (Services[i].socket > 0) close(Services[i].socket);
		    if (Services[i].stat[0] > 0) close(Services[i].stat[0]);
		    if (Services[i].stat[1] > 0) close(Services[i].stat[1]);
		}
		limit_fds(256);
		
		get_prog(path, sizeof(path), a->exec);
		syslog(LOG_DEBUG, "about to exec %s", path);
		execv(path, a->exec);
		syslog(LOG_ERR, "can't exec %s on schedule: %m", path);
		exit(EX_OSERR);
		break;
		
	    default:
		/* we don't wait for it to complete */
		
		/* add to child table */
		c = get_centry();
		c->pid = p;
		c->service_state = SERVICE_STATE_READY;
		c->si = SERVICE_NONE;
		c->next = ctable[p % child_table_size];
		ctable[p % child_table_size] = c;
		
		break;
	    }
	} /* a->exec */
	
	/* reschedule as needed */
	b = a->next;
	if (a->period) {
	    if(a->periodic) {
		a->mark = now + a->period;
	    } else {
		struct tm *tm;
		int delta;
		/* Daily Event */
		while(a->mark <= now) {
		    a->mark += a->period;
		}
		/* check for daylight savings fuzz... */
		tm = localtime(&(a->mark));
		if (tm->tm_hour != a->hour || tm->tm_min != a->min) {
		    /* calculate the same time on the new day */
		    tm->tm_hour = a->hour;
		    tm->tm_min = a->min;
		    delta = mktime(tm) - a->mark;
		    /* bring it within half a period either way */
		    while (delta > (a->period/2)) delta -= a->period;
		    while (delta < -(a->period/2)) delta += a->period;
		    /* update the time */
		    a->mark += delta;
		    /* and let us know about the change */
		    syslog(LOG_NOTICE, "timezone shift for %s - altering schedule by %d seconds", a->name, delta);
		}
	    }
	    /* reschedule a */
	    schedule_event(a);
	} else {
	    event_free(a);
	}
	/* examine next event */
	a = b;
    }
}

void reap_child(void)
{
    int status;
    pid_t pid;
    struct centry *c;
    struct service *s;

    while ((pid = waitpid((pid_t) -1, &status, WNOHANG)) > 0) {
	if (WIFEXITED(status)) {
	    syslog(LOG_DEBUG, "process %d exited, status %d", pid, 
		   WEXITSTATUS(status));
	}

	if (WIFSIGNALED(status)) {
	    syslog(LOG_ERR, "process %d exited, signaled to death by %d",
		   pid, WTERMSIG(status));
	}

	/* account for the child */
	c = ctable[pid % child_table_size];
	while(c && c->pid != pid) c = c->next;
	
	if (c && c->pid == pid) {
	    s = ((c->si) != SERVICE_NONE) ? &Services[c->si] : NULL;

	    /* paranoia */
	    switch (c->service_state) {
	    case SERVICE_STATE_READY:
	    case SERVICE_STATE_BUSY:
	    case SERVICE_STATE_UNKNOWN:
	    case SERVICE_STATE_DEAD:
		break;
	    default:
		syslog(LOG_CRIT, 
		       "service %s pid %d in ILLEGAL STATE: exited. Serious software bug or memory corruption detected!",
		       SERVICENAME(s->name), pid);
		syslog(LOG_DEBUG,
		       "service %s pid %d in ILLEGAL state: forced to valid UNKNOWN state",
		       SERVICENAME(s->name), pid);
		c->service_state = SERVICE_STATE_UNKNOWN;
	    }
	    if (s) {
	        /* update counters for known services */
		switch (c->service_state) {
		case SERVICE_STATE_READY:
		    s->nactive--;
		    s->ready_workers--;
		    if (!in_shutdown && (WIFSIGNALED(status) ||
			(WIFEXITED(status) && WEXITSTATUS(status)))) {
			syslog(LOG_WARNING, 
			       "service %s pid %d in READY state: terminated abnormally",
			       SERVICENAME(s->name), pid);
		    }
		    break;
		    
		case SERVICE_STATE_DEAD:
		    /* uh? either we got duplicate signals, or we are now MT */
		    syslog(LOG_WARNING, 
			   "service %s pid %d in DEAD state: receiving duplicate signals", 
			   SERVICENAME(s->name), pid);
		    break;
		    
		case SERVICE_STATE_BUSY:
		    s->nactive--;
		    if (!in_shutdown && (WIFSIGNALED(status) ||
			(WIFEXITED(status) && WEXITSTATUS(status)))) {
			syslog(LOG_DEBUG,
			       "service %s pid %d in BUSY state: terminated abnormally",
			       SERVICENAME(s->name), pid);
		    }
		    break;
		    
		case SERVICE_STATE_UNKNOWN:
		    s->nactive--;
		    syslog(LOG_WARNING,
			   "service %s pid %d in UNKNOWN state: exited",
			   SERVICENAME(s->name), pid);
		    break;
		default:
		    /* Shouldn't get here */
		    break;
		} 
	    } else {
	    	/* children from spawn_schedule (events) or
		 * children that messaged us before being registered or
		 * children of services removed by reread_conf() */
		if (c->service_state != SERVICE_STATE_READY) {
		    syslog(LOG_WARNING,
			   "unknown service pid %d in state %d: exited (maybe using a service as an event,"
			   " or a service was removed by SIGHUP?)",
			   pid, c->service_state);
		}
	    }
	    c->service_state = SERVICE_STATE_DEAD;
	    c->janitor_deadline = time(NULL) + 2;
	} else {
	    /* weird. Are we multithreaded now? we don't know this child */
	    syslog(LOG_WARNING,
		   "receiving signals from unregistered child %d. Handling it anyway",
		   pid);
	    c = get_centry();
	    c->pid = pid;
	    c->service_state = SERVICE_STATE_DEAD;
	    c->janitor_deadline = time(NULL) + 2;
	    c->si = SERVICE_NONE;
	    c->next = ctable[pid % child_table_size];
	    ctable[pid % child_table_size] = c;
	}
	if (verbose && c && (c->si != SERVICE_NONE))
	    syslog(LOG_DEBUG, "service %s now has %d ready workers\n", 
		    SERVICENAME(Services[c->si].name),
		    Services[c->si].ready_workers);
    }
}

void init_janitor(void)
{
    struct event *evt = (struct event *) malloc(sizeof(struct event));
    
    if (!evt) fatal("out of memory", EX_UNAVAILABLE);
    memset(evt, 0, sizeof(struct event));
    
    gettimeofday(&janitor_mark, NULL);
    janitor_position = 0;
    
    evt->name = xstrdup("janitor periodic wakeup call");
    evt->period = 10;
    evt->periodic = 1;
    evt->mark = time(NULL) + 2;
    schedule_event(evt);
}

void child_janitor(time_t now)
{
    int i;
    struct centry **p;
    struct centry *c;
    struct timeval rightnow;
    
    /* Estimate the number of entries to clean up in this sweep */
    gettimeofday(&rightnow, NULL);
    if (rightnow.tv_sec > janitor_mark.tv_sec + 1) {
	/* overflow protection */
	i = child_table_size;
    } else {
	double n;
	
	n = child_table_size * janitor_frequency * 
	    (double) ((rightnow.tv_sec - janitor_mark.tv_sec) * 1000000 +
	              rightnow.tv_usec - janitor_mark.tv_usec ) / 1000000;
	if (n < child_table_size) {
	    i = n;
	} else {
	    i = child_table_size;
	}
    }
    
    while (i-- > 0) {
	p = &ctable[janitor_position++];
	janitor_position = janitor_position % child_table_size;
	while (*p) {
	    c = *p;
	    if (c->service_state == SERVICE_STATE_DEAD) {
		if (c->janitor_deadline < now) {
		    *p = c->next;
		    c->next = cfreelist;
		    cfreelist = c;
		} else {
		    p = &((*p)->next);
		}
	    } else {
		p = &((*p)->next);
	    }
	}
    }
}

/* Allow a clean shutdown on SIGQUIT */
void sigquit_handler(int sig __attribute__((unused)))
{
    struct sigaction action;

    /* Ignore SIGQUIT ourselves */
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;
    action.sa_handler = SIG_IGN;
    if (sigaction(SIGQUIT, &action, (struct sigaction *) 0) < 0) {
	syslog(LOG_ERR, "sigaction: %m");
    }

    /* send our process group a SIGQUIT */
    if (kill(0, SIGQUIT) < 0) {
	syslog(LOG_ERR, "sigquit_handler: kill(0, SIGQUIT): %m");
    }

    /* Set a flag so main loop knows to shut down when
       all children have exited */
    in_shutdown = 1;

    syslog(LOG_INFO, "attempting clean shutdown on SIGQUIT");
}

static volatile sig_atomic_t gotsigchld = 0;

void sigchld_handler(int sig __attribute__((unused)))
{
    gotsigchld = 1;
}

static volatile int gotsighup = 0;

void sighup_handler(int sig __attribute__((unused)))
{
    gotsighup = 1;
}

void sigterm_handler(int sig __attribute__((unused)))
{
    struct sigaction action;

    /* send all the other processes SIGTERM, then exit */
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;
    action.sa_handler = SIG_IGN;
    if (sigaction(SIGTERM, &action, (struct sigaction *) 0) < 0) {
	syslog(LOG_ERR, "sigaction: %m");
	exit(1);
    }
    /* kill my process group */
    if (kill(0, SIGTERM) < 0) {
	syslog(LOG_ERR, "sigterm_handler: kill(0, SIGTERM): %m");
    }

#if defined(HAVE_UCDSNMP) || defined(HAVE_NETSNMP)
    /* tell master agent we're exiting */
    snmp_shutdown("cyrusMaster");
#endif

    syslog(LOG_INFO, "exiting on SIGTERM/SIGINT");
    exit(0);
}

void sigalrm_handler(int sig __attribute__((unused)))
{
    return;
}

void sighandler_setup(void)
{
    struct sigaction action;
    
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;

    action.sa_handler = sighup_handler;
#ifdef SA_RESTART
    action.sa_flags |= SA_RESTART;
#endif
    if (sigaction(SIGHUP, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGHUP: %m", 1);
    }

    action.sa_handler = sigalrm_handler;
    if (sigaction(SIGALRM, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGALRM: %m", 1);
    }

    /* Allow a clean shutdown on SIGQUIT */
    action.sa_handler = sigquit_handler;
    if (sigaction(SIGQUIT, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGQUIT: %m", 1);
    }

    /* Handle SIGTERM and SIGINT the same way -- kill
     * off our children! */
    action.sa_handler = sigterm_handler;
    if (sigaction(SIGTERM, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGTERM: %m", 1);
    }
    if (sigaction(SIGINT, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGINT: %m", 1);
    }

    action.sa_flags |= SA_NOCLDSTOP;
    action.sa_handler = sigchld_handler;
    if (sigaction(SIGCHLD, &action, NULL) < 0) {
	fatal("unable to install signal handler for SIGCHLD: %m", 1);
    }
}

void process_msg(const int si, struct notify_message *msg) 
{
    struct centry *c;
    /* si must NOT point to an invalid service */
    struct service * const s = &Services[si];;

    /* Search hash table with linked list for pid */
    c = ctable[msg->service_pid % child_table_size];
    while (c && c->pid != msg->service_pid) c = c->next;
    
    /* Did we find it? */
    if (!c || c->pid != msg->service_pid) {
	syslog(LOG_WARNING, "service %s pid %d: while trying to process message 0x%x: not registered yet", 
	       SERVICENAME(s->name), msg->service_pid, msg->message);
	/* resilience paranoia. Causes small performance loss when used */
	c = get_centry();
	c->si = si;
	c->pid = msg->service_pid;
	c->service_state = SERVICE_STATE_UNKNOWN;
	c->next = ctable[c->pid % child_table_size];
	ctable[c->pid % child_table_size] = c;
    }
    
    /* paranoia */
    if (si != c->si) {
	syslog(LOG_ERR, 
	       "service %s pid %d: changing from service %s due to received message",
	       SERVICENAME(s->name), c->pid,
	       ((c->si != SERVICE_NONE && Services[c->si].name) ? Services[c->si].name : "unknown"));
	c->si = si;
    }
    switch (c->service_state) {
    case SERVICE_STATE_UNKNOWN:
	syslog(LOG_WARNING, 
	       "service %s pid %d in UNKNOWN state: processing message 0x%x",
	       SERVICENAME(s->name), c->pid, msg->message);
	break;
    case SERVICE_STATE_READY:
    case SERVICE_STATE_BUSY:
    case SERVICE_STATE_DEAD:
	break;
    default:
	syslog(LOG_CRIT,
	       "service %s pid %d in ILLEGAL state: detected. Serious software bug or memory corruption uncloaked while processing message 0x%x from child!",
	       SERVICENAME(s->name), c->pid, msg->message);
	syslog(LOG_DEBUG,
	       "service %s pid %d in ILLEGAL state: forced to valid UNKNOWN state",
	       SERVICENAME(s->name), c->pid);
	c->service_state = SERVICE_STATE_UNKNOWN;
	break;
    }
    
    /* process message, according to state machine */
    switch (msg->message) {
    case MASTER_SERVICE_AVAILABLE:
	switch (c->service_state) {
	case SERVICE_STATE_READY:
	    /* duplicate message? */
	    syslog(LOG_WARNING,
		   "service %s pid %d in READY state: sent available message but it is already ready",
		   SERVICENAME(s->name), c->pid);
	    break;
	    
	case SERVICE_STATE_UNKNOWN:
	    /* since state is unknwon, error in non-DoS way, i.e.
	     * we don't increment ready_workers */
	    syslog(LOG_DEBUG,
		   "service %s pid %d in UNKNOWN state: now available and in READY state",
		   SERVICENAME(s->name), c->pid);
	    c->service_state = SERVICE_STATE_READY;
	    break;
	    
	case SERVICE_STATE_BUSY:
	    if (verbose) 
		syslog(LOG_DEBUG,
		       "service %s pid %d in BUSY state: now available and in READY state",
		       SERVICENAME(s->name), c->pid);
	    c->service_state = SERVICE_STATE_READY;
	    s->ready_workers++;
	    break;
	default:
	    /* Shouldn't get here */
	    break;
	}
	break;

    case MASTER_SERVICE_UNAVAILABLE:
	switch (c->service_state) {
	case SERVICE_STATE_BUSY:
	    /* duplicate message? */
	    syslog(LOG_WARNING,
		   "service %s pid %d in BUSY state: sent unavailable message but it is already busy",
		   SERVICENAME(s->name), c->pid);
	    break;
	    
	case SERVICE_STATE_UNKNOWN:
	    syslog(LOG_DEBUG,
		   "service %s pid %d in UNKNOWN state: now unavailable and in BUSY state",
		   SERVICENAME(s->name), c->pid);
	    c->service_state = SERVICE_STATE_BUSY;
	    break;
	    
	case SERVICE_STATE_READY:
	    if (verbose)
		syslog(LOG_DEBUG,
		       "service %s pid %d in READY state: now unavailable and in BUSY state",
		       SERVICENAME(s->name), c->pid);
	    c->service_state = SERVICE_STATE_BUSY;
	    s->ready_workers--;
	    break;
	default:
	    /* Shouldn't get here */
	    break;
	}
	break;

    case MASTER_SERVICE_CONNECTION:
	switch (c->service_state) {
	case SERVICE_STATE_BUSY:
	    s->nconnections++;
	    if (verbose)
		syslog(LOG_DEBUG,
		       "service %s pid %d in BUSY state: now serving connection",
		       SERVICENAME(s->name), c->pid);
	    break;
	    
	case SERVICE_STATE_UNKNOWN:
	    s->nconnections++;
	    c->service_state = SERVICE_STATE_BUSY;
	    syslog(LOG_DEBUG,
		   "service %s pid %d in UNKNOWN state: now in BUSY state and serving connection",
		   SERVICENAME(s->name), c->pid);
	    break;
	    
	case SERVICE_STATE_READY:
	    syslog(LOG_ERR, 
		   "service %s pid %d in READY state: reported new connection, forced to BUSY state",
		   SERVICENAME(s->name), c->pid);
	    /* be resilient on face of a bogon source, so lets err to the side
	     * of non-denial-of-service */
	    c->service_state = SERVICE_STATE_BUSY;
	    s->nconnections++;
	    s->ready_workers--;
	default:
	    /* Shouldn't get here */
	    break;
	}
	break;
	
    case MASTER_SERVICE_CONNECTION_MULTI:
	switch (c->service_state) {
	case SERVICE_STATE_READY:
	    s->nconnections++;
	    if (verbose)
		syslog(LOG_DEBUG, 
		       "service %s pid %d in READY state: serving one more multi-threaded connection",
		       SERVICENAME(s->name), c->pid);
	    break;
	    
	case SERVICE_STATE_BUSY:
	    syslog(LOG_ERR, 
		   "service %s pid %d in BUSY state: serving one more multi-threaded connection, forced to READY state",
		   SERVICENAME(s->name), c->pid);
	    /* be resilient on face of a bogon source, so lets err to the side
	     * of non-denial-of-service */
	    c->service_state = SERVICE_STATE_READY;
	    s->nconnections++;
	    s->ready_workers++;
	    break;
	    
	case SERVICE_STATE_UNKNOWN:
	    s->nconnections++;
	    c->service_state = SERVICE_STATE_READY;
	    syslog(LOG_ERR,
		   "service %s pid %d in UNKNOWN state: serving one more multi-threaded connection, forced to READY state",
		   SERVICENAME(s->name), c->pid);
	    break;
	default:
	    /* Shouldn't get here */
	    break;
	}
	break;
	
    default:
	syslog(LOG_CRIT, "service %s pid %d: Software bug: unrecognized message 0x%x", 
	       SERVICENAME(s->name), c->pid, msg->message);
	break;
    }

    if (verbose)
	syslog(LOG_DEBUG, "service %s now has %d ready workers\n", 
	       SERVICENAME(s->name), s->ready_workers);
}

static char **tokenize(char *p)
{
    char **tokens = NULL; /* allocated in increments of 10 */
    int i = 0;

    if (!p || !*p) return NULL; /* sanity check */
    while (*p) {
	while (*p && Uisspace(*p)) p++; /* skip whitespace */

	if (!(i % 10)) tokens = xrealloc(tokens, (i+10) * sizeof(char *));

	/* got a token */
	tokens[i++] = p;
	while (*p && !Uisspace(*p)) p++;

	/* p is whitespace or end of cmd */
	if (*p) *p++ = '\0';
    }
    /* add a NULL on the end */
    if (!(i % 10)) tokens = xrealloc(tokens, (i+1) * sizeof(char *));
    if (!tokens) return NULL;
    tokens[i] = NULL;

    return tokens;
}

void add_start(const char *name, struct entry *e,
	       void *rock __attribute__((unused)))
{
    char *cmd = xstrdup(masterconf_getstring(e, "cmd", ""));
    char buf[256];
    char **tok;

    if (!strcmp(cmd,"")) {
	snprintf(buf, sizeof(buf), "unable to find command for %s", name);
	fatal(buf, EX_CONFIG);
    }

    tok = tokenize(cmd);
    if (!tok) fatal("out of memory", EX_UNAVAILABLE);
    run_startup(tok);
    free(tok);
    free(cmd);
}

void add_service(const char *name, struct entry *e, void *rock)
{
    int ignore_err = (int) rock;
    char *cmd = xstrdup(masterconf_getstring(e, "cmd", ""));
    int prefork = masterconf_getint(e, "prefork", 0);
    int babysit = masterconf_getswitch(e, "babysit", 0);
    int maxforkrate = masterconf_getint(e, "maxforkrate", 0);
    char *listen = xstrdup(masterconf_getstring(e, "listen", ""));
    char *proto = xstrdup(masterconf_getstring(e, "proto", "tcp"));
    char *max = xstrdup(masterconf_getstring(e, "maxchild", "-1"));
    rlim_t maxfds = (rlim_t) masterconf_getint(e, "maxfds", 256);
    int reconfig = 0;
    int i, j;

    if(babysit && prefork == 0) prefork = 1;
    if(babysit && maxforkrate == 0) maxforkrate = 10; /* reasonable safety */

    if (!strcmp(cmd,"") || !strcmp(listen,"")) {
	char buf[256];
	snprintf(buf, sizeof(buf),
		 "unable to find command or port for service '%s'", name);

	if (ignore_err) {
	    syslog(LOG_WARNING, "WARNING: %s -- ignored", buf);
	    return;
	}

	fatal(buf, EX_CONFIG);
    }

    /* see if we have an existing entry that can be reused */
    for (i = 0; i < nservices; i++) {
	/* skip non-primary instances */
	if (Services[i].associate > 0)
	    continue;
	/* must have empty/same service name, listen and proto */
	if ((!Services[i].name || !strcmp(Services[i].name, name)) &&
	    (!Services[i].listen || !strcmp(Services[i].listen, listen)) &&
	    (!Services[i].proto || !strcmp(Services[i].proto, proto)))
	    break;
    }

    /* we have duplicate service names in the config file */
    if ((i < nservices) && Services[i].exec) {
	char buf[256];
	snprintf(buf, sizeof(buf), "multiple entries for service '%s'", name);

	if (ignore_err) {
	    syslog(LOG_WARNING, "WARNING: %s -- ignored", buf);
	    return;
	}

	fatal(buf, EX_CONFIG);
    }
 
    if (i == nservices) {
	/* either we don't have an existing entry or we are changing
	 * the port parameters, so create a new service
	 */
	if (nservices == allocservices) {
	    if (allocservices > SERVICE_MAX - 5)
		fatal("out of service structures, please restart", EX_UNAVAILABLE);
	    Services = xrealloc(Services, 
			       (allocservices+=5) * sizeof(struct service));
	}
	memset(&Services[nservices++], 0, sizeof(struct service));

	Services[i].last_interval_start = time(NULL);
    }
    else if (Services[i].listen) reconfig = 1;

    if (!Services[i].name) Services[i].name = xstrdup(name);
    if (Services[i].listen) free(Services[i].listen);
    Services[i].listen = listen;
    if (Services[i].proto) free(Services[i].proto);
    Services[i].proto = proto;

    Services[i].exec = tokenize(cmd);
    if (!Services[i].exec) fatal("out of memory", EX_UNAVAILABLE);

    /* is this service actually there? */
    if (!verify_service_file(Services[i].exec)) {
	char buf[1024];
	snprintf(buf, sizeof(buf),
		 "cannot find executable for service '%s'", name);
	
	/* if it is not, we're misconfigured, die. */
	fatal(buf, EX_CONFIG);
    }

    Services[i].maxforkrate = maxforkrate;
    Services[i].maxfds = maxfds;

    if (!strcmp(Services[i].proto, "tcp") ||
	!strcmp(Services[i].proto, "tcp4") ||
	!strcmp(Services[i].proto, "tcp6")) {
	Services[i].desired_workers = prefork;
	Services[i].babysit = babysit;
	Services[i].max_workers = atoi(max);
	if (Services[i].max_workers == -1) {
	    Services[i].max_workers = INT_MAX;
	}
    } else {
	/* udp */
	if (prefork > 1) prefork = 1;
	Services[i].desired_workers = prefork;
	Services[i].max_workers = 1;
    }
    free(max);
 
    if (reconfig) {
	/* reconfiguring an existing service, update any other instances */
	for (j = 0; j < nservices; j++) {
	    if (Services[j].associate > 0 && Services[j].listen &&
		Services[j].name && !strcmp(Services[j].name, name)) {
		Services[j].maxforkrate = Services[i].maxforkrate;
		Services[j].exec = Services[i].exec;
		Services[j].desired_workers = Services[i].desired_workers;
		Services[j].babysit = Services[i].babysit;
		Services[j].max_workers = Services[i].max_workers;
	    }
	}
    }

    if (verbose > 2)
	syslog(LOG_DEBUG, "%s: service '%s' (%s, %s:%s, %d, %d, %d)",
	       reconfig ? "reconfig" : "add",
	       Services[i].name, cmd,
	       Services[i].proto, Services[i].listen,
	       Services[i].desired_workers,
	       Services[i].max_workers,
	       (int) Services[i].maxfds);
}

void add_event(const char *name, struct entry *e, void *rock)
{
    int ignore_err = (int) rock;
    char *cmd = xstrdup(masterconf_getstring(e, "cmd", ""));
    int period = 60 * masterconf_getint(e, "period", 0);
    int at = masterconf_getint(e, "at", -1), hour, min;
    time_t now = time(NULL);
    struct event *evt;

    if (!strcmp(cmd,"")) {
	char buf[256];
	snprintf(buf, sizeof(buf),
		 "unable to find command or port for event '%s'", name);

	if (ignore_err) {
	    syslog(LOG_WARNING, "WARNING: %s -- ignored", buf);
	    return;
	}

	fatal(buf, EX_CONFIG);
    }
    
    evt = (struct event *) xmalloc(sizeof(struct event));
    evt->name = xstrdup(name);

    if (at >= 0 && ((hour = at / 100) <= 23) && ((min = at % 100) <= 59)) {
	struct tm *tm = localtime(&now);

	period = 86400; /* 24 hours */
	evt->periodic = 0;
	evt->hour = hour;
	evt->min = min;
	tm->tm_hour = hour;
	tm->tm_min = min;
	tm->tm_sec = 0;
	if ((evt->mark = mktime(tm)) < now) {
	    /* already missed it, so schedule for next day */
	    evt->mark += period;
	}
    }
    else {
	evt->periodic = 1;
	evt->mark = now;
    }
    evt->period = period;

    evt->exec = tokenize(cmd);
    if (!evt->exec) fatal("out of memory", EX_UNAVAILABLE);

    schedule_event(evt);
}

#ifdef HAVE_SETRLIMIT

#ifdef RLIMIT_NOFILE
# define RLIMIT_NUMFDS RLIMIT_NOFILE
#else
# ifdef RLIMIT_OFILE
#  define RLIMIT_NUMFDS RLIMIT_OFILE
# endif
#endif
void limit_fds(rlim_t x)
{
    struct rlimit rl;
    int r;

    rl.rlim_cur = x;
    rl.rlim_max = x;
    if (setrlimit(RLIMIT_NUMFDS, &rl) < 0) {
	syslog(LOG_ERR, "setrlimit: Unable to set file descriptors limit to %ld: %m", x);

#ifdef HAVE_GETRLIMIT

	if (!getrlimit(RLIMIT_NUMFDS, &rl)) {
	    syslog(LOG_ERR, "retrying with %ld (current max)", rl.rlim_max);
	    rl.rlim_cur = rl.rlim_max;
	    if (setrlimit(RLIMIT_NUMFDS, &rl) < 0) {
		syslog(LOG_ERR, "setrlimit: Unable to set file descriptors limit to %ld: %m", x);
	    }
	}
    }


    if (verbose > 1) {
	r = getrlimit(RLIMIT_NUMFDS, &rl);
	syslog(LOG_DEBUG, "set maximum file descriptors to %ld/%ld", rl.rlim_cur,
	       rl.rlim_max);
    }
#else
    }
#endif /* HAVE_GETRLIMIT */
}
#else
void limit_fds(rlim_t x)
{
}
#endif /* HAVE_SETRLIMIT */

void reread_conf(void)
{
    int i,j;
    struct event *ptr;
    struct centry *c;

    /* disable all services -
       they will be re-enabled if they appear in config file */
    for (i = 0; i < nservices; i++) Services[i].exec = NULL;

    /* read services */
    masterconf_getsection("SERVICES", &add_service, (void*) 1);

    for (i = 0; i < nservices; i++) {
	if (!Services[i].exec && Services[i].socket) {
	    /* cleanup newly disabled services */

	    if (verbose > 2)
		syslog(LOG_DEBUG, "disable: service %s socket %d pipe %d %d",
		       Services[i].name, Services[i].socket,
		       Services[i].stat[0], Services[i].stat[1]);

	    /* Only free the service info on the primary */
	    if(Services[i].associate == 0) {
		free(Services[i].listen);
		free(Services[i].proto);
	    }
	    Services[i].listen = NULL;
	    Services[i].proto = NULL;
	    Services[i].desired_workers = 0;

	    /* send SIGHUP to all children */
	    for (j = 0 ; j < child_table_size ; j++ ) {
		c = ctable[j];
		while (c != NULL) {
		    if ((c->si == i) &&
			(c->service_state != SERVICE_STATE_DEAD)) {
			kill(c->pid, SIGHUP);
		    }
		    c = c->next;
		}
	    }

	    /* close all listeners */
	    if (Services[i].socket > 0) {
		shutdown(Services[i].socket, SHUT_RDWR);
		close(Services[i].socket);
	    }
	    Services[i].socket = 0;
	}
	else if (Services[i].exec && !Services[i].socket) {
	    /* initialize new services */

	    service_create(&Services[i]);
	    if (verbose > 2)
		syslog(LOG_DEBUG, "init: service %s socket %d pipe %d %d",
		       Services[i].name, Services[i].socket,
		       Services[i].stat[0], Services[i].stat[1]);
	}
    }

    /* remove existing events */
    while (schedule) {
	ptr = schedule;
	schedule = schedule->next;
	event_free(ptr);
    }
    schedule = NULL;

    /* read events */
    masterconf_getsection("EVENTS", &add_event, (void*) 1);

    /* reinit child janitor */
    init_janitor();

    /* send some feedback to admin */
    syslog(LOG_NOTICE,
	    "Services reconfigured. %d out of %d (max %d) services structures are now in use",
	    nservices, allocservices, SERVICE_MAX);
}

int main(int argc, char **argv)
{
    const char *default_pidfile = MASTER_PIDFILE;
    const char *lock_suffix = ".lock";

    const char *pidfile = default_pidfile;
    char *pidfile_lock = NULL;

    int startup_pipe[2] = { -1, -1 };
    int pidlock_fd = -1;

    int i, opt, close_std = 1, daemon_mode = 0;
    extern int optind;
    extern char *optarg;

    char *alt_config = NULL;
    
    int fd;
    fd_set rfds;
    char *p = NULL;

#ifdef HAVE_NETSNMP
    char *agentxsocket = NULL;
    int agentxpinginterval = -1;
#endif

    time_t now;

    p = getenv("CYRUS_VERBOSE");
    if (p) verbose = atoi(p) + 1;
#ifdef HAVE_NETSNMP
    while ((opt = getopt(argc, argv, "C:M:p:l:Ddj:P:x:")) != EOF) {
#else
    while ((opt = getopt(argc, argv, "C:M:p:l:Ddj:")) != EOF) {
#endif
	switch (opt) {
	case 'C': /* alt imapd.conf file */
	    alt_config = optarg;
	    break;
	case 'M': /* alt cyrus.conf file */
	    MASTER_CONFIG_FILENAME = optarg;
	    break;
	case 'l':
            /* user defined listen queue backlog */
	    listen_queue_backlog = atoi(optarg);
	    break;
	case 'p':
	    /* Set the pidfile name */
	    pidfile = optarg;
	    break;
	case 'd':
	    /* Daemon Mode */
	    if(!close_std)
		fatal("Unable to both be debug and daemon mode", EX_CONFIG);
	    daemon_mode = 1;
	    break;
	case 'D':
	    /* Debug Mode */
	    if(daemon_mode)
		fatal("Unable to be both debug and daemon mode", EX_CONFIG);
	    close_std = 0;
	    break;
	case 'j':
	    /* Janitor frequency */
	    janitor_frequency = atoi(optarg);
	    if(janitor_frequency < 1)
		fatal("The janitor period must be at least 1 second", EX_CONFIG);
	    break;   
#ifdef HAVE_NETSNMP
	case 'P': /* snmp AgentXPingInterval */
	    agentxpinginterval = atoi(optarg);
	    break;
	case 'x': /* snmp AgentXSocket */
	    agentxsocket = optarg;
	    break;
#endif
	default:
	    break;
	}
    }

    masterconf_init("master", alt_config);

    /* zero out the children table */
    memset(&ctable, 0, sizeof(struct centry *) * child_table_size);

    if (close_std) {
      /* close stdin/out/err */
      for (fd = 0; fd < 3; fd++) {
	close(fd);
	if (open("/dev/null", O_RDWR, 0) != fd)
	  fatal("couldn't open /dev/null: %m", 2);
      }
    }

    /* we reserve fds 3 and 4 for children to communicate with us, so they
       better be available. */
    for (fd = 3; fd < 5; fd++) {
	close(fd);
	if (dup(0) != fd) fatal("couldn't dup fd 0: %m", 2);
    }

    /* Pidfile Algorithm in Daemon Mode.  This is a little subtle because
     * we want to ensure that we can report an error to our parent if the
     * child fails to lock the pidfile.
     *
     * [A] Create/lock pidfile.lock.  If locked, exit(failure).
     * [A] Create a pipe
     * [A] Fork [B]
     * [A] Block on reading exit code from pipe
     * [B] Create/lock pidfile.  If locked, write failure code to pipe and
     *     exit(failure)
     * [B] write pid to pidfile
     * [B] write success code to pipe & finish starting up
     * [A] unlink pidfile.lock and exit(code read from pipe)
     *
     */
    if(daemon_mode) {
	/* Daemonize */
	pid_t pid = -1;

	pidfile_lock = xmalloc(strlen(pidfile) + strlen(lock_suffix) + 1);

	strcpy(pidfile_lock, pidfile);
	strcat(pidfile_lock, lock_suffix);
	
	pidlock_fd = open(pidfile_lock, O_CREAT|O_TRUNC|O_RDWR, 0644);
	if(pidlock_fd == -1) {
	    syslog(LOG_ERR, "can't open pidfile lock: %s (%m)", pidfile_lock);
	    exit(EX_OSERR);
	} else {
	    if(lock_nonblocking(pidlock_fd)) {
		syslog(LOG_ERR, "can't get exclusive lock on %s",
		       pidfile_lock);
		exit(EX_TEMPFAIL);
	    }
	}
	
	if(pipe(startup_pipe) == -1) {
	    syslog(LOG_ERR, "can't create startup pipe (%m)");
	    exit(EX_OSERR);
	}

	do {
	    pid = fork();
	    	    
	    if ((pid == -1) && (errno == EAGAIN)) {
		syslog(LOG_WARNING, "master fork failed (sleeping): %m");
		sleep(5);
	    }
	} while ((pid == -1) && (errno == EAGAIN));

	if (pid == -1) {
	    fatal("fork error", EX_OSERR);
	} else if (pid != 0) {
	    int exit_code;

	    /* Parent, wait for child */
	    if(read(startup_pipe[0], &exit_code, sizeof(exit_code)) == -1) {
		syslog(LOG_ERR, "could not read from startup_pipe (%m)");
		unlink(pidfile_lock);
		exit(EX_OSERR);
	    } else {
		unlink(pidfile_lock);
		exit(exit_code);
	    }
	}

	/* Child! */
	close(startup_pipe[0]);

	free(pidfile_lock);

	/*
	 * We're now running in the child. Lose our controlling terminal
	 * and obtain a new process group.
	 */
	if (setsid() == -1) {
	    int exit_result = EX_OSERR;
	    
	    /* Tell our parent that we failed. */
	    write(startup_pipe[1], &exit_result, sizeof(exit_result));
	
	    fatal("setsid failure", EX_OSERR);
	}
    }

    limit_fds(RLIM_INFINITY);

    /* Write out the pidfile */
    pidfd = open(pidfile, O_CREAT|O_RDWR, 0644);
    if(pidfd == -1) {
	int exit_result = EX_OSERR;

	/* Tell our parent that we failed. */
	write(startup_pipe[1], &exit_result, sizeof(exit_result));

	syslog(LOG_ERR, "can't open pidfile: %m");
	exit(EX_OSERR);
    } else {
	char buf[100];

	if(lock_nonblocking(pidfd)) {
	    int exit_result = EX_OSERR;

	    /* Tell our parent that we failed. */
	    write(startup_pipe[1], &exit_result, sizeof(exit_result));
	    
	    fatal("cannot get exclusive lock on pidfile (is another master still running?)", EX_OSERR);
	} else {
	    int pidfd_flags = fcntl(pidfd, F_GETFD, 0);
	    if (pidfd_flags != -1)
		pidfd_flags = fcntl(pidfd, F_SETFD, 
				    pidfd_flags | FD_CLOEXEC);
	    if (pidfd_flags == -1) {
		int exit_result = EX_OSERR;
		
		/* Tell our parent that we failed. */
		write(startup_pipe[1], &exit_result, sizeof(exit_result));

		fatal("unable to set close-on-exec for pidfile: %m", EX_OSERR);
	    }
	    
	    /* Write PID */
	    snprintf(buf, sizeof(buf), "%lu\n", (unsigned long int)getpid());
	    if(lseek(pidfd, 0, SEEK_SET) == -1 ||
	       ftruncate(pidfd, 0) == -1 ||
	       write(pidfd, buf, strlen(buf)) == -1) {
		int exit_result = EX_OSERR;

		/* Tell our parent that we failed. */
		write(startup_pipe[1], &exit_result, sizeof(exit_result));

		fatal("unable to write to pidfile: %m", EX_OSERR);
	    }
	    fsync(pidfd);
	}
    }

    if(daemon_mode) {
	int exit_result = 0;

	/* success! */
	if(write(startup_pipe[1], &exit_result, sizeof(exit_result)) == -1) {
	    syslog(LOG_ERR,
		   "could not write success result to startup pipe (%m)");
	    exit(EX_OSERR);
	}

	close(startup_pipe[1]);
	if(pidlock_fd != -1) close(pidlock_fd);
    }

    syslog(LOG_NOTICE, "process started");

#if defined(HAVE_UCDSNMP) || defined(HAVE_NETSNMP)
    /* initialize SNMP agent */
    
    /* make us a agentx client. */
#ifdef HAVE_NETSNMP
    netsnmp_enable_subagent();

    netsnmp_ds_set_boolean(NETSNMP_DS_LIBRARY_ID,
                           NETSNMP_DS_LIB_ALARM_DONT_USE_SIG, 1);
    if (agentxpinginterval >= 0)
        netsnmp_ds_set_int(NETSNMP_DS_APPLICATION_ID,
                           NETSNMP_DS_AGENT_AGENTX_PING_INTERVAL, agentxpinginterval);

    if (agentxsocket != NULL)
        netsnmp_ds_set_string(NETSNMP_DS_APPLICATION_ID, 
                              NETSNMP_DS_AGENT_X_SOCKET, agentxsocket);
#else
    ds_set_boolean(DS_APPLICATION_ID, DS_AGENT_ROLE, 1);
#endif

    /* initialize the agent library */
    init_agent("cyrusMaster");

    init_cyrusMasterMIB();

    init_snmp("cyrusMaster"); 
#endif

    masterconf_getsection("START", &add_start, NULL);
    masterconf_getsection("SERVICES", &add_service, NULL);
    masterconf_getsection("EVENTS", &add_event, NULL);

    /* set signal handlers */
    sighandler_setup();

    /* initialize services */
    for (i = 0; i < nservices; i++) {
	service_create(&Services[i]);
	if (verbose > 2)
	    syslog(LOG_DEBUG, "init: service %s socket %d pipe %d %d",
		   Services[i].name, Services[i].socket,
		   Services[i].stat[0], Services[i].stat[1]);
    }

    if (become_cyrus_early) {
	if (become_cyrus() != 0) {
	    syslog(LOG_ERR, "can't change to the cyrus user: %m");
	    exit(1);
	}
    }

    /* init ctable janitor */
    init_janitor();
    
    /* ok, we're going to start spawning like mad now */
    syslog(LOG_NOTICE, "ready for work");

    now = time(NULL);
    for (;;) {
	int r, i, maxfd, total_children = 0;
	struct timeval tv, *tvptr;
	struct notify_message msg;
#if defined(HAVE_UCDSNMP) || defined(HAVE_NETSNMP)
	int blockp = 0;
#endif

	/* run any scheduled processes */
	if (!in_shutdown)
	    spawn_schedule(now);

	/* reap first, that way if we need to babysit we will */
	if (gotsigchld) {
	    /* order matters here */
	    gotsigchld = 0;
	    reap_child();
	}
	
	/* do we have any services undermanned? */
	for (i = 0; i < nservices; i++) {
	    total_children += Services[i].nactive;
	    if (!in_shutdown) {
		if (Services[i].exec /* enabled */ &&
		    (Services[i].nactive < Services[i].max_workers) &&
		    (Services[i].ready_workers < Services[i].desired_workers)) {
		    spawn_service(i);
		} else if (Services[i].exec
			  && Services[i].babysit
			  && Services[i].nactive == 0) {
		    syslog(LOG_ERR,
			  "lost all children for service: %s.  " \
			  "Applying babysitter.",
			  Services[i].name);
		    spawn_service(i);
		} else if (!Services[i].exec /* disabled */ &&
			  Services[i].name /* not yet removed */ &&
			  Services[i].nactive == 0) {
		    if (verbose > 2)
			syslog(LOG_DEBUG, "remove: service %s pipe %d %d",
			      Services[i].name,
			      Services[i].stat[0], Services[i].stat[1]);
    
		    /* Only free the service info on the primary */
		    if (Services[i].associate == 0) {
			free(Services[i].name);
		    }
		    Services[i].name = NULL;
		    Services[i].nforks = 0;
		    Services[i].nactive = 0;
		    Services[i].nconnections = 0;
		    Services[i].associate = 0;
    
		    if (Services[i].stat[0] > 0) close(Services[i].stat[0]);
		    if (Services[i].stat[1] > 0) close(Services[i].stat[1]);
		    memset(Services[i].stat, 0, sizeof(Services[i].stat));
		}
	    }
	}
        
	if (in_shutdown && total_children == 0) {
	   syslog(LOG_NOTICE, "All children have exited, closing down");
	   exit(0);
	}

	if (gotsighup) {
	    syslog(LOG_NOTICE, "got SIGHUP");
	    gotsighup = 0;
	    reread_conf();
	}

	FD_ZERO(&rfds);
	maxfd = 0;
	for (i = 0; i < nservices; i++) {
	    int x = Services[i].stat[0];

	    int y = Services[i].socket;

	    /* messages */
	    if (x > 0) {
		if (verbose > 2)
		    syslog(LOG_DEBUG, "listening for messages from %s",
			   Services[i].name);
		FD_SET(x, &rfds);
	    }
	    if (x > maxfd) maxfd = x;

	    /* connections */
	    if (y > 0 && Services[i].ready_workers == 0 &&
		Services[i].nactive < Services[i].max_workers) {
		if (verbose > 2)
		    syslog(LOG_DEBUG, "listening for connections for %s", 
			   Services[i].name);
		FD_SET(y, &rfds);
		if (y > maxfd) maxfd = y;
	    }

	    /* paranoia */
	    if (Services[i].ready_workers < 0) {
		syslog(LOG_ERR, "%s has %d workers?!?", Services[i].name,
		       Services[i].ready_workers);
	    }
	}
	maxfd++;		/* need 1 greater than maxfd */

	/* how long to wait? - do now so that any scheduled wakeup
	 * calls get accounted for*/
	tvptr = NULL;
	if (schedule) {
	    if (now < schedule->mark) tv.tv_sec = schedule->mark - now;
	    else tv.tv_sec = 0;
	    tv.tv_usec = 0;
	    tvptr = &tv;
	}

#if defined(HAVE_UCDSNMP) || defined(HAVE_NETSNMP)
	if (tvptr == NULL) blockp = 1;
	snmp_select_info(&maxfd, &rfds, tvptr, &blockp);
#endif
	errno = 0;
	r = select(maxfd, &rfds, NULL, NULL, tvptr);
	if (r == -1 && errno == EAGAIN) continue;
	if (r == -1 && errno == EINTR) continue;
	if (r == -1) {
	    /* uh oh */
	    fatal("select failed: %m", 1);
	}

#if defined(HAVE_UCDSNMP) || defined(HAVE_NETSNMP)
	/* check for SNMP queries */
	snmp_read(&rfds);
	snmp_timeout();
#endif
	for (i = 0; i < nservices; i++) {
	    int x = Services[i].stat[0];
	    int y = Services[i].socket;
	    int j;

	    if (FD_ISSET(x, &rfds)) {
		r = read(x, &msg, sizeof(msg));
		if (r != sizeof(msg)) {
		    syslog(LOG_ERR, "got incorrectly sized response from child: %x", i);
		    continue;
		}
		
		process_msg(i, &msg);
	    }

	    if (!in_shutdown && Services[i].exec &&
		Services[i].nactive < Services[i].max_workers) {
		/* bring us up to desired_workers */
		for (j = Services[i].ready_workers;
		     j < Services[i].desired_workers; 
		     j++)
		{
		    spawn_service(i);
		}

		if (Services[i].ready_workers == 0 && 
		    FD_ISSET(y, &rfds)) {
		    /* huh, someone wants to talk to us */
		    spawn_service(i);
		}
	    }
	}
	now = time(NULL);
	child_janitor(now);

#ifdef HAVE_NETSNMP
	run_alarms();
#endif
    }
}
