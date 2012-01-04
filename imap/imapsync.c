/* imapsync.c - synchronise to an IMAP server
 *
 * Copyright (c) 2011 Carnegie Mellon University.  All rights reserved.
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
 * $Id: sync_client.c,v 1.51 2010/06/28 12:04:20 brong Exp $
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <syslog.h>
#include <string.h>
#include <sys/wait.h>
#include <errno.h>
#include <ctype.h>
#include <signal.h>
#include <utime.h>

#include <netinet/tcp.h>

#include "global.h"
#include "assert.h"
#include "append.h"
#include "mboxlist.h"
#include "exitcodes.h"
#include "imap_err.h"
#include "mailbox.h"
#include "quota.h"
#include "xmalloc.h"
#include "acl.h"
#include "seen.h"
#include "mboxname.h"
#include "map.h"
#include "imapd.h"
#include "imparse.h"
#include "util.h"
#include "prot.h"
#include "message_guid.h"
#include "sync_log.h"
#include "sync_support.h"
#include "cyr_lock.h"
#include "backend.h"
#include "xstrlcat.h"
#include "xstrlcpy.h"
#include "signals.h"
#include "cyrusdb.h"
#include "strarray.h"

/* signal to config.c */
const int config_need_data = CONFIG_NEED_PARTITION_DATA;

/* ====================================================================== */

/* Static global variables and support routines for sync_client */

extern char *optarg;
extern int optind;

static const char *servername = NULL;
static const char *username = NULL;
static const char *password = NULL;
static const char *mboxname = NULL;
static const char *port = "143";
static int do_compress = 0;
static struct backend *backend = NULL;
static struct protstream *sync_out = NULL;
static struct protstream *sync_in = NULL;

static struct namespace   sync_namespace;

static int verbose         = 0;
static int tagnum = 0;

enum {
    /* IMAP capabilities */
    CAPA_IDLE		= (1 << 3),
    CAPA_MULTIAPPEND	= (1 << 5),
    CAPA_LITERALPLUS    = (1 << 10)
};

static struct protocol_t imap_protocol =
{ "imap", "imap",
  { 1, NULL },
  { "C01 CAPABILITY", NULL, "C01 ", NULL,
    CAPAF_MANY_PER_LINE,
    { { "AUTH", CAPA_AUTH },
      { "STARTTLS", CAPA_STARTTLS },
      { "COMPRESS=DEFLATE", CAPA_COMPRESS },
      { "IDLE", CAPA_IDLE },
      { "LITERAL+", CAPA_LITERALPLUS },
      { "MULTIAPPEND", CAPA_MULTIAPPEND },
      { NULL, 0 } } },
  { "S01 STARTTLS", "S01 OK", "S01 NO", 0 },
  { "A01 AUTHENTICATE", 0, 0, "A01 OK", "A01 NO", "+ ", "*",
    NULL, AUTO_CAPA_AUTH_OK },
  { "Z01 COMPRESS DEFLATE", "* ", "Z01 OK" },
  { "N01 NOOP", "* ", "N01 OK" },
  { "Q01 LOGOUT", "* ", "Q01 " }
};

static void shut_down(int code) __attribute__((noreturn));
static void shut_down(int code)
{
    in_shutdown = 1;

    seen_done();
    annotatemore_close();
    annotatemore_done();
    quotadb_close();
    quotadb_done();
    mboxlist_close();
    mboxlist_done();
    cyrus_done();
    exit(code);
}

static int usage(const char *name)
{
    fprintf(stderr,
            "usage: %s -S <servername> [-C <alt_config>] [-r] [-v] mailbox...\n", name);
 
    exit(EC_USAGE);
}

void fatal(const char *s, int code)
{
    fprintf(stderr, "Fatal error: %s\n", s);
    syslog(LOG_ERR, "Fatal error: %s", s);
    abort();
    exit(code);
}

static int copy_local(struct mailbox *mailbox, unsigned long uid)
{
    uint32_t recno;
    struct index_record oldrecord;
    int r;

    for (recno = 1; recno <= mailbox->i.num_records; recno++) {
	r = mailbox_read_index_record(mailbox, recno, &oldrecord);
	if (r) return r;

	/* found the record, renumber it */
	if (oldrecord.uid == uid) {
	    char *oldfname, *newfname;
	    struct index_record newrecord;

	    /* create the new record as a clone of the old record */
	    newrecord = oldrecord;
	    newrecord.uid = mailbox->i.last_uid + 1;

	    /* copy the file in to place */
	    oldfname = xstrdup(mailbox_message_fname(mailbox, oldrecord.uid));
	    newfname = xstrdup(mailbox_message_fname(mailbox, newrecord.uid));
	    r = mailbox_copyfile(oldfname, newfname, 0);
	    free(oldfname);
	    free(newfname);
	    if (r) return r;

	    /* append the new record */
	    r = mailbox_append_index_record(mailbox, &newrecord);
	    if (r) return r;

	    /* Copy across any per-message annotations */
	    r = annotate_msg_copy(mailbox, oldrecord.uid,
				  mailbox, newrecord.uid,
				  NULL);
	    if (r) return r;

	    /* and expunge the old record */
	    oldrecord.system_flags |= FLAG_EXPUNGED;
	    r = mailbox_rewrite_index_record(mailbox, &oldrecord);

	    /* done - return */
	    return r;
	}
    }

    /* not finding the record is an error! (should never happen) */
    return IMAP_MAILBOX_NONEXISTENT;
}

static const char *make_flags(struct mailbox *mailbox, struct index_record *record)
{
    static char buf[4096];
    const char *sep = "";
    int flag;

    if (record->system_flags & FLAG_DELETED) {
	snprintf(buf, 4096, "%s\\Deleted", sep);
        sep = " ";
    }
    if (record->system_flags & FLAG_ANSWERED) {
	snprintf(buf, 4096, "%s\\Answered", sep);
        sep = " ";
    }
    if (record->system_flags & FLAG_FLAGGED) {
	snprintf(buf, 4096, "%s\\Flagged", sep);
        sep = " ";
    }
    if (record->system_flags & FLAG_DRAFT) {
	snprintf(buf, 4096, "%s\\Draft", sep);
        sep = " ";
    }
    if (record->system_flags & FLAG_EXPUNGED) {
	snprintf(buf, 4096, "%s\\Expunged", sep);
        sep = " ";
    }
    if (record->system_flags & FLAG_SEEN) {
	snprintf(buf, 4096, "%s\\Seen", sep);
        sep = " ";
    }
        
    /* print user flags in mailbox order */
    for (flag = 0; flag < MAX_USER_FLAGS; flag++) {
	if (!mailbox->flagname[flag])
	    continue;
	if (!(record->user_flags[flag/32] & (1<<(flag&31))))
	    continue;
	snprintf(buf, 4096, "%s%s", sep, mailbox->flagname[flag]);
        sep = " ";
    }

    return buf;
}

static void _connect()
{
    int wait;
    struct protoent *proto;
    sasl_callback_t *cb;

    cb = mysasl_callbacks(NULL,
			  username,
			  "",
			  password);

    /* get the right port */
    imap_protocol.service = port;

    for (wait = 15;; wait *= 2) {
	backend = backend_connect(backend, servername,
				  &imap_protocol, "", cb, NULL);

	if (backend || wait > 1000) break;

	fprintf(stderr,
		"Can not connect to server '%s', retrying in %d seconds\n",
		servername, wait);
	sleep(wait);
    }

    free_callbacks(cb);
    cb = NULL;

    if (!backend) {
	fprintf(stderr, "Can not connect to server '%s'\n",
		servername);
	syslog(LOG_ERR, "Can not connect to server '%s'", servername);
	_exit(1);
    }

    /* Disable Nagle's Algorithm => increase throughput
     *
     * http://en.wikipedia.org/wiki/Nagle's_algorithm
     */ 
    if (servername[0] != '/') {
	if (backend->sock >= 0 && (proto = getprotobyname("tcp")) != NULL) {
	    int on = 1;

	    if (setsockopt(backend->sock, proto->p_proto, TCP_NODELAY,
			   (void *) &on, sizeof(on)) != 0) {
		syslog(LOG_ERR, "unable to setsocketopt(TCP_NODELAY): %m");
	    }

	    /* turn on TCP keepalive if set */
	    if (config_getswitch(IMAPOPT_TCP_KEEPALIVE)) {
		int r;
		int optval = 1;
		socklen_t optlen = sizeof(optval);
		struct protoent *proto = getprotobyname("TCP");

		r = setsockopt(backend->sock, SOL_SOCKET, SO_KEEPALIVE, &optval, optlen);
		if (r < 0) {
		    syslog(LOG_ERR, "unable to setsocketopt(SO_KEEPALIVE): %m");
		}
#ifdef TCP_KEEPCNT
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_CNT);
		if (optval) {
		    r = setsockopt(backend->sock, proto->p_proto, TCP_KEEPCNT, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPCNT): %m");
		    }
		}
#endif
#ifdef TCP_KEEPIDLE
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_IDLE);
		if (optval) {
		    r = setsockopt(backend->sock, proto->p_proto, TCP_KEEPIDLE, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPIDLE): %m");
		    }
		}
#endif
#ifdef TCP_KEEPINTVL
		optval = config_getint(IMAPOPT_TCP_KEEPALIVE_INTVL);
		if (optval) {
		    r = setsockopt(backend->sock, proto->p_proto, TCP_KEEPINTVL, &optval, optlen);
		    if (r < 0) {
			syslog(LOG_ERR, "unable to setsocketopt(TCP_KEEPINTVL): %m");
		    }
		}
#endif
	    }
	} else {
	    syslog(LOG_ERR, "unable to getprotobyname(\"tcp\"): %m");
	}
    }

#ifdef HAVE_ZLIB
    /* Does the backend support compression? */
    if (CAPA(backend, CAPA_COMPRESS)) {
	prot_printf(backend->out, "COMPRESS DEFLATE\r\n");
	prot_flush(backend->out);

	if (sync_parse_response("COMPRESS", backend->in, NULL)) {
	    if (do_compress) fatal("Failed to enable compression, aborting", EC_SOFTWARE);
	    syslog(LOG_NOTICE, "Failed to enable compression, continuing uncompressed");
	}
	else {
	    prot_setcompress(backend->in);
	    prot_setcompress(backend->out);
	}
    }
    else if (do_compress) fatal("Backend does not support compression, aborting", EC_SOFTWARE);
#endif

    /* links to sockets */
    sync_in = backend->in;
    sync_out = backend->out;

    if (verbose > 1) {
	prot_setlog(sync_in, fileno(stderr));
	prot_setlog(sync_out, fileno(stderr));
    }

    /* Force use of LITERAL+ so we don't need two way communications */
    prot_setisclient(sync_in, 1);
    if (CAPA(backend, CAPA_LITERALPLUS))
        prot_setisclient(sync_out, 1);
}

static void _disconnect(void)
{
    backend_disconnect(backend);
}


/* ====================================================================== */

static struct sasl_callback mysasl_cb[] = {
    { SASL_CB_GETOPT, (mysasl_cb_ft *) &mysasl_config, NULL },
    { SASL_CB_CANON_USER, (mysasl_cb_ft *) &mysasl_canon_user, NULL },
    { SASL_CB_LIST_END, NULL, NULL }
};

strarray_t *getfolders()
{
    strarray_t *res = strarray_new();
    struct buf tag = BUF_INITIALIZER;
    struct buf item = BUF_INITIALIZER;
    char *namespace;
    char *sep;
    char c;

    prot_printf(sync_out, "N01 NAMESPACE\r\n");
    prot_flush(sync_out);
    while (1) {
	struct dlist *dl = NULL;
	strarray_t *arr = strarray_new();
	c = getword(sync_in, &tag);
	if (strcmp(tag.s, "*")) break;
	c = getastring(sync_in, NULL, &item);

	if (strcasecmp(item.s, "NAMESPACE")) abort();
	if (c != ' ') abort();
	c = dlist_parse(&dl, 0, sync_in);
	namespace = xstrdup(dlist_cstring(dl->head->head));
	sep = xstrdup(dlist_cstring(dl->head->head->next));
	eatline(sync_in, c);
	dlist_free(&dl);
	strarray_free(arr);
    }
    eatline(sync_in, c);

    strarray_add(res, "INBOX");

    prot_printf(sync_out, "L01 LIST ");
    prot_printastring(sync_out, namespace);
    prot_printf(sync_out, " *\r\n");
    prot_flush(sync_out);
    while (1) {
	strarray_t *arr;
	c = getword(sync_in, &tag);
	if (strcmp(tag.s, "*")) break;
	c = getastring(sync_in, NULL, &item); /* this should be a LIST */
	while (c != ')') c = prot_getc(sync_in);
	c = prot_getc(sync_in);
	c = getastring(sync_in, NULL, &item); /* this is the separator */
	c = getastring(sync_in, NULL, &item); /* this is the folder name */
	eatline(sync_in, c);
	arr = strarray_split(item.s, sep);
	strarray_add(res, strarray_join(arr, sep));
	strarray_free(arr);
    }
    eatline(sync_in, c);

    return res;
}

static void do_folder(const char *foldername)
{
    char outtag[20];
    uint32_t exists = 0;
    uint32_t uidvalidity = 0;
    uint32_t uidnext = 0;
    struct buf tag = BUF_INITIALIZER;
    struct buf item = BUF_INITIALIZER;
    struct buf item2 = BUF_INITIALIZER;
    struct buf item3 = BUF_INITIALIZER;
    char *namespace;
    char c;

    sprintf(outtag, "S%04d", tagnum++);

    prot_printf(sync_out, "%s SELECT ", outtag);
    prot_printastring(sync_out, foldername);
    prot_printf(sync_out, "\r\n");
    prot_flush(sync_out);
    while (1) {
	c = getword(sync_in, &tag);
	if (strcmp(tag.s, "*")) break;

	c = getastring(sync_in, NULL, &item); /* could be OK, NUM or FLAGS */
	if (cyrus_isdigit(item.s[0])) {
	    c = getastring(sync_in, NULL, &item2); /* which number? */
	    if (!strcasecmp(item2.s, "EXISTS"))
		exists = atoi(item.s);
	}

	else if (!strcasecmp(item.s, "OK")) {
	    c = getastring(sync_in, NULL, &item2); /* which OK item? */
	    c = getastring(sync_in, NULL, &item3); /* which value ? */
	    if (!strcasecmp(item2.s, "[UIDVALIDITY"))
		uidvalidity = atoi(item3.s);
	    else if (!strcasecmp(item2.s, "[UIDNEXT"))
		uidnext = atoi(item3.s);
	}

	/* regardless, clean up for the next line */
	eatline(sync_in, c);
    }
    /* eat up the tag line too */
    eatline(sync_in, c);

    printf("%s %s: %d %d %d\n", outtag, foldername, uidvalidity, uidnext, exists);
}

int main(int argc, char **argv)
{
    int   opt;
    char *alt_config     = NULL;
    int   r = 0;
    int   exit_rc = 0;
    int i;
    char c;
    strarray_t *res;

    if ((geteuid()) == 0 && (become_cyrus() != 0)) {
	fatal("must run as the Cyrus user", EC_USAGE);
    }

    setbuf(stdout, NULL);

    while ((opt = getopt(argc, argv, "C:vS:u:p:P:m:")) != EOF) {
        switch (opt) {
        case 'C': /* alt config file */
            alt_config = optarg;
            break;

        case 'v': /* verbose */
            verbose++;
            break;

	case 'S': /* Socket descriptor for server */
	    servername = optarg;
	    break;

        case 'P':
            port = optarg;
            break;

	case 'u':
	    username = optarg;
	    break;

	case 'p':
	    password = optarg;
	    break;

	case 'm':
	    mboxname = optarg;
	    break;

	case 'z':
#ifdef HAVE_ZLIB
	    do_compress = 1;
#else
	    fatal("Compress not available without zlib compiled in", EC_SOFTWARE);
#endif
	    break;

        default:
            usage("sync_client");
        }
    }

    cyrus_init(alt_config, "imapsync",
	       (verbose > 1 ? CYRUSINIT_PERROR : 0));

    /* get the server name if not specified */
    if (!servername)
        fatal("sync_host not defined", EC_SOFTWARE);

    if (!username)
        fatal("username not defined", EC_SOFTWARE);

    if (!mboxname)
        fatal("mailbox not defined", EC_SOFTWARE);

    /* Set namespace -- force standard (internal) */
    config_virtdomains = config_getenum(IMAPOPT_VIRTDOMAINS);
    if ((r = mboxname_init_namespace(&sync_namespace, 1)) != 0) {
        fatal(error_message(r), EC_CONFIG);
    }

    /* open the mboxlist, we'll need it for real work */
    mboxlist_init(0);
    mboxlist_open(NULL);

    /* open the quota db, we'll need it for real work */
    quotadb_init(0);
    quotadb_open(NULL);

    /* open the annotation db */
    annotatemore_init(NULL, NULL);
    annotatemore_open();

    signals_set_shutdown(&shut_down);
    signals_add_handlers(0);

    /* load the SASL plugins */
    global_sasl_init(1, 0, mysasl_cb);

    _connect();

    res = getfolders();
    for (i = 0; i < res->count; i++) {
	const char *f = strarray_nth(res, i);
	do_folder(f);
    }
    strarray_free(res);

    _disconnect();

    shut_down(exit_rc);
}
