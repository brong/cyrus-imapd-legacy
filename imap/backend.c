/* backend.c -- IMAP server proxy for Cyrus Murder
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
 * $Id: backend.c,v 1.63 2010/08/04 18:57:36 wescraig Exp $
 */

#include <config.h>

#include <stdio.h>
#include <string.h>
#include <signal.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <fcntl.h>
#include <sys/types.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <syslog.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>

#include <sasl/sasl.h>
#include <sasl/saslutil.h>

#include "assert.h"
#include "prot.h"
#include "backend.h"
#include "global.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "iptostring.h"
#include "util.h"

enum {
    AUTO_BANNER = -1,
    AUTO_NO = 0,
    AUTO_YES = 1
};

static char *ask_capability(struct protstream *pout, struct protstream *pin,
			    struct protocol_t *prot, unsigned long *capa,
			    int automatic)
{
    char str[4096];
    char *ret = NULL, *tmp;
    struct capa_t *c;
    const char *resp;

    resp = (automatic == AUTO_BANNER) ? prot->banner.resp : prot->capa_cmd.resp;

    if (!automatic) {
	/* no capability command */
	if (!prot->capa_cmd.cmd) return NULL;
	
	/* request capabilities of server */
	prot_printf(pout, "%s", prot->capa_cmd.cmd);
	if (prot->capa_cmd.arg) prot_printf(pout, " %s", prot->capa_cmd.arg);
	prot_printf(pout, "\r\n");
	prot_flush(pout);
    }

    *capa = 0;
    
    do {
	if (prot_fgets(str, sizeof(str), pin) == NULL) break;

	/* look for capabilities in the string */
	for (c = prot->capa_cmd.capa; c->str; c++) {
	    if ((tmp = strstr(str, c->str)) != NULL) {
		*capa = *capa | c->flag;

		if (c->flag == CAPA_AUTH) {
		    if (ret) {
			free(ret);
			ret = NULL;
		    }
		    if (prot->capa_cmd.parse_mechlist)
			ret = prot->capa_cmd.parse_mechlist(str, prot);
		    else
			ret = xstrdup(tmp+strlen(c->str));
		}
	    }
	}
	if (!resp) {
	    /* multiline response with no distinct end (IMAP banner) */
	    prot_NONBLOCK(pin);
	}

	/* look for the end of the capabilities */
    } while (!resp || strncasecmp(str, resp, strlen(resp)));
    
    prot_BLOCK(pin);
    return ret;
}

static int do_compress(struct backend *s, struct simple_cmd_t *compress_cmd)
{
#ifndef HAVE_ZLIB
    return -1;
#else
    char buf[1024];

    /* send compress command */
    prot_printf(s->out, "%s\r\n", compress_cmd->cmd);
    prot_flush(s->out);

    /* check response */
    if (!prot_fgets(buf, sizeof(buf), s->in) ||
	strncmp(buf, compress_cmd->ok, strlen(compress_cmd->ok)))
	return -1;

    prot_setcompress(s->in);
    prot_setcompress(s->out);

    return 0;
#endif /* HAVE_ZLIB */
}

static int do_starttls(struct backend *s, struct tls_cmd_t *tls_cmd)
{
#ifndef HAVE_SSL
    return -1;
#else
    char buf[2048];
    int r;
    int *layerp;
    char *auth_id;
    sasl_ssf_t ssf;

    /* send starttls command */
    prot_printf(s->out, "%s\r\n", tls_cmd->cmd);
    prot_flush(s->out);

    /* check response */
    if (!prot_fgets(buf, sizeof(buf), s->in) ||
	strncmp(buf, tls_cmd->ok, strlen(tls_cmd->ok)))
	return -1;

    r = tls_init_clientengine(5, "", "");
    if (r == -1) return -1;

    /* SASL and openssl have different ideas about whether ssf is signed */
    layerp = (int *) &ssf;
    r = tls_start_clienttls(s->in->fd, s->out->fd, layerp, &auth_id,
			    &s->tlsconn, &s->tlssess);
    if (r == -1) return -1;

    r = sasl_setprop(s->saslconn, SASL_SSF_EXTERNAL, &ssf);
    if (r == SASL_OK)
	r = sasl_setprop(s->saslconn, SASL_AUTH_EXTERNAL, auth_id);
    if (auth_id) free(auth_id);
    if (r != SASL_OK) return -1;

    prot_settls(s->in,  s->tlsconn);
    prot_settls(s->out, s->tlsconn);

    return 0;
#endif /* HAVE_SSL */
}

static char *intersect_mechlists( char *config, char *server )
{
    char *newmechlist = xzmalloc( strlen( config ) + 1 );
    char *cmech = NULL, *smech = NULL, *s;
    int count = 0;
    char csave, ssave;

    do {
	if ( isalnum( *config ) || *config == '_' || *config == '-' ) {
	    if ( cmech == NULL ) {
		cmech = config;
	    }
	} else {
	    if ( cmech != NULL ) {
		csave = *config;
		*config = '\0';

		s = server;
		do {
		    if ( isalnum( *s ) || *s == '_' || *s == '-' ) {
			if ( smech == NULL ) {
			    smech = s;
			}
		    } else {
			if ( smech != NULL ) {
			    ssave = *s;
			    *s = '\0';

			    if ( strcasecmp( cmech, smech ) == 0 ) {
				if ( count > 0 ) {
				    strcat( newmechlist, " " );
				}
				strcat( newmechlist, cmech );
				count++;

				*s = ssave;
				smech = NULL;
				break;
			    }

			    *s = ssave;
			    smech = NULL;
			}
		    }
		} while ( *s++ );

		*config = csave;
		cmech = NULL;
	    }
	}
    } while ( *config++ );

    if ( count == 0 ) {
	free( newmechlist );
	return( NULL );
    }
    return( newmechlist );
}

static int backend_authenticate(struct backend *s, struct protocol_t *prot,
				char **mechlist, const char *userid,
				sasl_callback_t *cb, const char **status)
{
    int r;
    sasl_security_properties_t secprops =
	{ 0, 0xFF, PROT_BUFSIZE, 0, NULL, NULL }; /* default secprops */
    struct sockaddr_storage saddr_l, saddr_r;
    char remoteip[60], localip[60];
    socklen_t addrsize;
    int local_cb = 0;
    char buf[2048], optstr[128], *p;
    const char *mech_conf, *pass;

    /* set the IP addresses */
    addrsize=sizeof(struct sockaddr_storage);
    if (getpeername(s->sock, (struct sockaddr *)&saddr_r, &addrsize) != 0)
	return SASL_FAIL;
    if(iptostring((struct sockaddr *)&saddr_r, addrsize, remoteip, 60) != 0)
	return SASL_FAIL;
  
    addrsize=sizeof(struct sockaddr_storage);
    if (getsockname(s->sock, (struct sockaddr *)&saddr_l, &addrsize)!=0)
	return SASL_FAIL;
    if(iptostring((struct sockaddr *)&saddr_l, addrsize, localip, 60) != 0)
	return SASL_FAIL;

    if (!cb) {
	local_cb = 1;
	strlcpy(optstr, s->hostname, sizeof(optstr));
	p = strchr(optstr, '.');
	if (p) *p = '\0';
	strlcat(optstr, "_password", sizeof(optstr));
	pass = config_getoverflowstring(optstr, NULL);
	if(!pass) pass = config_getstring(IMAPOPT_PROXY_PASSWORD);
	cb = mysasl_callbacks(userid, 
			      config_getstring(IMAPOPT_PROXY_AUTHNAME),
			      config_getstring(IMAPOPT_PROXY_REALM),
			      pass);
    }

    /* Require proxying if we have an "interesting" userid (authzid) */
    r = sasl_client_new(prot->sasl_service, s->hostname, localip, remoteip, cb,
			(userid  && *userid ? SASL_NEED_PROXY : 0) |
			(prot->sasl_cmd.parse_success ? SASL_SUCCESS_DATA : 0),
			&s->saslconn);
    if (r != SASL_OK) {
	if (local_cb) free_callbacks(cb);
	return r;
    }

    r = sasl_setprop(s->saslconn, SASL_SEC_PROPS, &secprops);
    if (r != SASL_OK) {
	if (local_cb) free_callbacks(cb);
	return r;
    }

    /* Get SASL mechanism list.  We can force a particular
       mechanism using a <shorthost>_mechs option */
    strcpy(buf, s->hostname);
    p = strchr(buf, '.');
    if (p) *p = '\0';
    strcat(buf, "_mechs");
    mech_conf = config_getoverflowstring(buf, NULL);

    if(!mech_conf) {
	mech_conf = config_getstring(IMAPOPT_FORCE_SASL_CLIENT_MECH);
    }

    do {
	/* If we have a mech_conf, use it */
	if (mech_conf && *mechlist) {
	    char *conf = xstrdup(mech_conf);
	    char *newmechlist = intersect_mechlists( conf, *mechlist );

	    if ( newmechlist == NULL ) {
		syslog( LOG_INFO, "%s did not offer %s", s->hostname,
			mech_conf );
	    }

	    free(conf);
	    free(*mechlist);
	    *mechlist = newmechlist;
	}

	if (*mechlist) {
	    /* we now do the actual SASL exchange */
	    saslclient(s->saslconn, &prot->sasl_cmd, *mechlist,
		       s->in, s->out, &r, status);

	    /* garbage collect */
	    free(*mechlist);
	    *mechlist = NULL;
	}
	else r = SASL_NOMECH;

	/* If we don't have a usable mech, do TLS and try again */
    } while (r == SASL_NOMECH && CAPA(s, CAPA_STARTTLS) &&
	     do_starttls(s, &prot->tls_cmd) != -1 &&
	     (*mechlist = ask_capability(s->out, s->in, prot,
					 &s->capability,
					 prot->tls_cmd.auto_capa)));

    /* xxx unclear that this is correct */
    if (local_cb) free_callbacks(cb);

    if (r == SASL_OK) {
	prot_setsasl(s->in, s->saslconn);
	prot_setsasl(s->out, s->saslconn);
    }

    /* r == SASL_OK on success */
    return r;
}

static volatile sig_atomic_t timedout = 0;

static void timed_out(int sig) 
{
    if (sig == SIGALRM) {
	timedout = 1;
    } else {
	fatal("Bad signal in timed_out", EC_SOFTWARE);
    }
}

struct backend *backend_connect(struct backend *ret_backend, const char *server,
				struct protocol_t *prot, const char *userid,
				sasl_callback_t *cb, const char **auth_status)
{
    /* need to (re)establish connection to server or create one */
    int sock = -1;
    int r;
    int err = -1;
    int ask = 1; /* should we explicitly ask for capabilities? */
    struct addrinfo hints, *res0 = NULL, *res;
    struct sockaddr_un sunsock;
    char buf[2048], *mechlist = NULL;
    struct sigaction action;
    struct backend *ret;

    if (!ret_backend) {
	ret = xzmalloc(sizeof(struct backend));
	strlcpy(ret->hostname, server, sizeof(ret->hostname));
	ret->timeout = NULL;
    }
    else
	ret = ret_backend;

    if (server[0] == '/') { /* unix socket */
	res0 = &hints;
	memset(res0, 0, sizeof(struct addrinfo));
	res0->ai_family = PF_UNIX;
	res0->ai_socktype = SOCK_STREAM;

 	res0->ai_addr = (struct sockaddr *) &sunsock;
 	res0->ai_addrlen = sizeof(sunsock.sun_family) + strlen(server) + 1;
#ifdef SIN6_LEN
 	res0->ai_addrlen += sizeof(sunsock.sun_len);
 	sunsock.sun_len = res0->ai_addrlen;
#endif
	sunsock.sun_family = AF_UNIX;
	strlcpy(sunsock.sun_path, server, sizeof(sunsock.sun_path));

	/* XXX set that we are preauthed */

	/* change hostname to 'config_servername' */
	strlcpy(ret->hostname, config_servername, sizeof(ret->hostname));
    }
    else { /* inet socket */
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = PF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;
	err = getaddrinfo(server, prot->service, &hints, &res0);
	if (err) {
	    syslog(LOG_ERR, "getaddrinfo(%s) failed: %s",
		   server, gai_strerror(err));
	    if (!ret_backend) free(ret);
	    return NULL;
	}
    }

    /* Setup timeout */
    timedout = 0;
    action.sa_flags = 0;
    action.sa_handler = timed_out;
    sigemptyset(&action.sa_mask);
    if(sigaction(SIGALRM, &action, NULL) < 0) 
    {
	syslog(LOG_ERR, "Setting timeout in backend_connect failed: sigaction: %m");
	/* continue anyway */
    }
    
    for (res = res0; res; res = res->ai_next) {
	sock = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
	if (sock < 0)
	    continue;
	alarm(config_getint(IMAPOPT_CLIENT_TIMEOUT));
	if (connect(sock, res->ai_addr, res->ai_addrlen) >= 0)
	    break;
	if(errno == EINTR && timedout == 1)
	    errno = ETIMEDOUT;
	close(sock);
	sock = -1;
    }

    /* Remove timeout code */
    alarm(0);
    signal(SIGALRM, SIG_IGN);
    
    if (sock < 0) {
	if (res0 != &hints)
	    freeaddrinfo(res0);
	syslog(LOG_ERR, "connect(%s) failed: %m", server);
	if (!ret_backend) free(ret);
	return NULL;
    }
    memcpy(&ret->addr, res->ai_addr, res->ai_addrlen);
    if (res0 != &hints)
	freeaddrinfo(res0);

    ret->in = prot_new(sock, 0);
    ret->out = prot_new(sock, 1);
    ret->sock = sock;
    prot_setflushonread(ret->in, ret->out);
    ret->prot = prot;
    
    if (prot->banner.is_capa) {
	/* try to get the capabilities from the banner */
	mechlist = ask_capability(ret->out, ret->in, prot,
				  &ret->capability, AUTO_BANNER);
	if (mechlist || ret->capability) {
	    /* found capabilities in banner -> don't ask */
	    ask = 0;
	}
    }
    else {
	do { /* read the initial greeting */
	    if (!prot_fgets(buf, sizeof(buf), ret->in)) {
		syslog(LOG_ERR,
		       "backend_connect(): couldn't read initial greeting: %s",
		       ret->in->error ? ret->in->error : "(null)");
		if (!ret_backend) free(ret);
		close(sock);
		return NULL;
	    }
	} while (strncasecmp(buf, prot->banner.resp,
			     strlen(prot->banner.resp)));
    }

    if (ask) {
	/* get the capabilities */
	mechlist = ask_capability(ret->out, ret->in, prot,
				  &ret->capability, AUTO_NO);
    }

    /* now need to authenticate to backend server,
       unless we're doing LMTP/CSYNC on a UNIX socket (deliver/sync_client) */
    if ((server[0] != '/') ||
	(strcmp(prot->sasl_service, "lmtp") &&
	 strcmp(prot->sasl_service, "csync"))) {
	char *mlist = xstrdup(mechlist); /* backend_auth is destructive */

	if ((r = backend_authenticate(ret, prot, &mlist, userid,
				      cb, auth_status))) {
	    syslog(LOG_ERR, "couldn't authenticate to backend server: %s",
		   sasl_errstring(r, NULL, NULL));
	    if (!ret_backend) free(ret);
	    close(sock);
	    ret = NULL;
	}
	else {
	    const void *ssf;

	    sasl_getprop(ret->saslconn, SASL_SSF, &ssf);
	    if (*((sasl_ssf_t *) ssf)) {
		/* if we have a SASL security layer, compare SASL mech lists
		   to check for a MITM attack */
		char *new_mechlist;
		int auto_capa = prot->sasl_cmd.auto_capa;

		if (!strcmp(prot->service, "sieve")) {
		    /* XXX  Hack to handle ManageSieve servers.
		     * No way to tell from protocol if server will
		     * automatically send capabilities, so we treat it
		     * as optional.
		     */
		    char ch;

		    /* wait and probe for possible auto-capability response */
		    usleep(250000);
		    prot_NONBLOCK(ret->in);
		    if ((ch = prot_getc(ret->in)) != EOF) {
			prot_ungetc(ch, ret->in);
		    } else {
			auto_capa = AUTO_NO;
		    }
		    prot_BLOCK(ret->in);
		}

		new_mechlist = ask_capability(ret->out, ret->in, prot,
					      &ret->capability, auto_capa);
		if (new_mechlist && strcmp(new_mechlist, mechlist)) {
		    syslog(LOG_ERR, "possible MITM attack:"
			   "list of available SASL mechanisms changed");
		    if (!ret_backend) free(ret);
		    close(sock);
		    ret = NULL;
		}

		free(new_mechlist);
	    }
	}

	if (mlist) free(mlist);
    }

    if (mechlist) free(mechlist);

    /* start compression if requested and both client/server support it */
    if (config_getswitch(IMAPOPT_PROXY_COMPRESS) && ret &&
	CAPA(ret, CAPA_COMPRESS) &&
	prot->compress_cmd.cmd &&
	do_compress(ret, &prot->compress_cmd)) {

	syslog(LOG_ERR, "couldn't enable compression on backend server");
	if (!ret_backend) free(ret);
	close(sock);
	ret = NULL;
    }

    if (!ret_backend) ret_backend = ret;
	    
    return ret;
}

int backend_ping(struct backend *s)
{
    char buf[1024];

    if (!s || !s->prot->ping_cmd.cmd) return 0;
    if (s->sock == -1) return -1; /* Disconnected Socket */
    
    prot_printf(s->out, "%s\r\n", s->prot->ping_cmd.cmd);
    prot_flush(s->out);

    for (;;) {
	if (!prot_fgets(buf, sizeof(buf), s->in)) {
	    /* connection closed? */
	    return -1;
	} else if (s->prot->ping_cmd.unsol &&
		   !strncmp(s->prot->ping_cmd.unsol, buf,
			    strlen(s->prot->ping_cmd.unsol))) {
	    /* unsolicited response */
	    continue;
	} else {
	    /* success/fail response */
	    return strncmp(s->prot->ping_cmd.ok, buf,
			   strlen(s->prot->ping_cmd.ok));
	}
    }
}

void backend_disconnect(struct backend *s)
{
    char buf[1024];

    if (!s || s->sock == -1) return;
    
    if (!prot_error(s->in)) {
	if (s->prot->logout_cmd.cmd) {
	    prot_printf(s->out, "%s\r\n", s->prot->logout_cmd.cmd);
	    prot_flush(s->out);

	    for (;;) {
		if (!prot_fgets(buf, sizeof(buf), s->in)) {
		    /* connection closed? */
		    break;
		} else if (s->prot->logout_cmd.unsol &&
			   !strncmp(s->prot->logout_cmd.unsol, buf,
				    strlen(s->prot->logout_cmd.unsol))) {
		    /* unsolicited response */
		    continue;
		} else {
		    /* success/fail response -- don't care either way */
		    break;
		}
	    }
	}
    }

    /* Flush the incoming buffer */
    prot_NONBLOCK(s->in);
    prot_fill(s->in);

#ifdef HAVE_SSL
    /* Free tlsconn */
    if (s->tlsconn) {
	tls_reset_servertls(&s->tlsconn);
	s->tlsconn = NULL;
    }
#endif /* HAVE_SSL */

    /* close/free socket & prot layer */
    cyrus_close_sock(s->sock);
    s->sock = -1;
    
    prot_free(s->in);
    prot_free(s->out);
    s->in = s->out = NULL;

    /* Free saslconn */
    if(s->saslconn) {
	sasl_dispose(&(s->saslconn));
	s->saslconn = NULL;
    }

    /* free last_result buffer */
    buf_free(&s->last_result);
}
