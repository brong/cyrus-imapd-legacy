/* tls.c - STARTTLS helper functions for imapd
 * Tim Martin
 * 9/21/99
 *
 * Based upon Lutz Jaenicke's TLS patches for postfix
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
 * $Id: tls.c,v 1.67 2010/01/06 17:01:42 murch Exp $
 */

/*
* NAME
*	tls
* SUMMARY
*	interface to openssl routines
* SYNOPSIS
*	#include <tls.h>
*
* DESCRIPTION
*	This module is the interface between Cyrus Imapd and the OpenSSL library.
*	As of now only one filedescriptor can be handled, so only one
*	TLS channel can be open at a time.
*
*	tls_init_serverengine() is called once when the server is started
*	in order to initialize as much of the TLS stuff as possible.
*	The certificate handling is also decided during the setup phase,
*	so that a peer specific handling is not possible.
*
*	tls_start_servertls() activates the TLS feature for the
*	filedescriptor selected with tls_setfd() before. We expect
*	that all buffers are flushed and the TLS handshake can begin
*	immediately.
*
*	tls_stop_servertls() sends the "close notify" alert via
*	SSL_shutdown() to the peer and resets all connection specific
*	TLS data. As RFC2487 does not specify a separate shutdown, it
*	is supposed that the underlying TCP connection is shut down
*	immediately afterwards, so we don't care about additional data
*	coming through the channel.
*
*	Once the TLS connection is initiated, information about the TLS
*	state is available:
*	tls_protocol holds the protocol name (SSLv2, SSLv3, TLSv1),
*	tls_cipher_name the cipher name (e.g. RC4/MD5),
*	tls_cipher_usebits the number of bits actually used (e.g. 40),
*	tls_cipher_algbits the number of bits the algorithm is based on
*	(e.g. 128).
*	The last two values may be different when talking to a crippled
*	- ahem - export controled peer (e.g. 40/128).
*
* xxx we need to offer a callback to do peer issuer certification.
*     data that should be available for inspection:
*	If the peer offered a certifcate _and_ the certificate could be
*	verified successfully, part of the certificate data are available as:
*	tls_peer_subject X509v3-oneline with the DN of the peer
*	pfixlts_peer_CN extracted CommonName of the peer
*	tls_peer_issuer  X509v3-oneline with the DN of the issuer
*	pfixlts_peer_CN extracted CommonName of the issuer
*	tls_peer_fingerprint fingerprint of the certificate
*
*/

#include <config.h>

#ifdef HAVE_SSL

/* System library. */

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <syslog.h>

/* OpenSSL library. */

#include <openssl/lhash.h>
#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/ssl.h>

/* Application-specific. */
#include "assert.h"
#include "nonblock.h"
#include "xmalloc.h"
#include "xstrlcat.h"
#include "xstrlcpy.h"
#include "tls.h"

/* Session caching/reuse stuff */
#include "global.h"
#include "cyrusdb.h"

#define DB (config_tlscache_db) /* sessions are binary -> MUST use DB3 */

static struct db *sessdb = NULL;
static int sess_dbopen = 0;

/* We must keep some of the info available */
static const char hexcodes[] = "0123456789ABCDEF";

enum {
    var_imapd_tls_loglevel = 0,
    var_proxy_tls_loglevel = 0,
    CCERT_BUFSIZ = 256
};

static int verify_depth = 5;
static int verify_error = X509_V_OK;

static SSL_CTX *s_ctx = NULL, *c_ctx = NULL;

static int tls_serverengine = 0; /* server engine initialized? */
static int tls_clientengine = 0; /* client engine initialized? */
static int do_dump = 0;		/* actively dumping protocol? */


int tls_enabled(void)
{
    const char *val;

    val = config_getstring(IMAPOPT_TLS_CERT_FILE);
    if (!val || !strcasecmp(val, "disabled")) return 0;

    val = config_getstring(IMAPOPT_TLS_KEY_FILE);
    if (!val || !strcasecmp(val, "disabled")) return 0;

    return 1;
}

/* taken from OpenSSL apps/s_cb.c 
 * tim - this seems to just be giving logging messages
 */

static void apps_ssl_info_callback(SSL * s, int where, int ret)
{
    char   *str;
    int     w;

    if (var_imapd_tls_loglevel==0) return;

    w = where & ~SSL_ST_MASK;

    if (w & SSL_ST_CONNECT)
	str = "SSL_connect";
    else if (w & SSL_ST_ACCEPT)
	str = "SSL_accept";
    else
	str = "undefined";

    if (where & SSL_CB_LOOP) {
	if (tls_serverengine && (var_imapd_tls_loglevel >= 2))
	    syslog(LOG_DEBUG, "%s:%s", str, SSL_state_string_long(s));
    } else if (where & SSL_CB_ALERT) {
	str = (where & SSL_CB_READ) ? "read" : "write";
	if ((tls_serverengine && (var_imapd_tls_loglevel >= 2)) ||
	    ((ret & 0xff) != SSL3_AD_CLOSE_NOTIFY))
	    syslog(LOG_DEBUG, "SSL3 alert %s:%s:%s", str,
		   SSL_alert_type_string_long(ret),
		   SSL_alert_desc_string_long(ret));
    } else if (where & SSL_CB_EXIT) {
	if (ret == 0)
	    syslog(LOG_DEBUG, "%s:failed in %s",
		   str, SSL_state_string_long(s));
	else if (ret < 0) {
	    syslog(LOG_DEBUG, "%s:error in %s",
		   str, SSL_state_string_long(s));
	}
    }
}

/* taken from OpenSSL apps/s_cb.c
   not thread safe! */
static RSA *tmp_rsa_cb(SSL * s __attribute__((unused)),
		       int export __attribute__((unused)),
		       int keylength)
{
    static RSA *rsa_tmp = NULL;

    if (rsa_tmp == NULL) {
	rsa_tmp = RSA_generate_key(keylength, RSA_F4, NULL, NULL);
    }
    return (rsa_tmp);
}

#if (OPENSSL_VERSION_NUMBER >= 0x0090800fL)
/* Logic copied from OpenSSL apps/s_server.c: give the TLS context
 * DH params to work with DHE-* cipher suites. Hardcoded fallback
 * in case no DH params in tls_key_file or tls_cert_file.
 */
static DH *get_dh1024(void)
{
    /* Second Oakley group 1024-bits MODP group from RFC2409 */
    DH *dh=NULL;

    if ((dh=DH_new()) == NULL) return(NULL);
    dh->p=get_rfc2409_prime_1024(NULL);
    dh->g=NULL;
    BN_dec2bn(&(dh->g), "2");
    if ((dh->p == NULL) || (dh->g == NULL)) return(NULL);

    return(dh);
	
}
static DH *load_dh_param(const char *keyfile, const char *certfile)
{
    DH *ret=NULL;
    BIO *bio = NULL;

    if (keyfile) bio = BIO_new_file(keyfile, "r");

    if ((bio == NULL) && certfile) bio = BIO_new_file(certfile,"r");

    if (bio) ret=PEM_read_bio_DHparams(bio,NULL,NULL,NULL);

    if (ret == NULL) {
	ret = get_dh1024();
	syslog(LOG_NOTICE, "imapd:Loading hard-coded DH parameters");
    } else {
	syslog(LOG_NOTICE, "imapd:Loading DH parameters from file");
    }

    if (bio != NULL) BIO_free(bio);

    return(ret);
}
#endif /* OPENSSL_VERSION_NUMBER >= 0x009080fL */

/* taken from OpenSSL apps/s_cb.c */

static int verify_callback(int ok, X509_STORE_CTX * ctx)
{
    char    buf[256];
    X509   *err_cert;
    int     err;
    int     depth;

    syslog(LOG_DEBUG, "Doing a peer verify");

    err_cert = X509_STORE_CTX_get_current_cert(ctx);
    err = X509_STORE_CTX_get_error(ctx);
    depth = X509_STORE_CTX_get_error_depth(ctx);

    X509_NAME_oneline(X509_get_subject_name(err_cert), buf, sizeof(buf));
    if (ok==0)
    {
      syslog(LOG_ERR, "verify error:num=%d:%s", err,
	     X509_verify_cert_error_string(err));
      
	if (verify_depth >= depth) {
	    ok = 0;
	    verify_error = X509_V_OK;
	} else {
	    ok = 0;
	    verify_error = X509_V_ERR_CERT_CHAIN_TOO_LONG;
	}
    }
    switch (ctx->error) {
    case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT:
	X509_NAME_oneline(X509_get_issuer_name(ctx->current_cert), buf, sizeof(buf));
	syslog(LOG_NOTICE, "issuer= %s", buf);
	break;
    case X509_V_ERR_CERT_NOT_YET_VALID:
    case X509_V_ERR_ERROR_IN_CERT_NOT_BEFORE_FIELD:
	syslog(LOG_NOTICE, "cert not yet valid");
	break;
    case X509_V_ERR_CERT_HAS_EXPIRED:
    case X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD:
	syslog(LOG_NOTICE, "cert has expired");
	break;
    }

    return (ok);
}


/*
 * taken from OpenSSL crypto/bio/b_dump.c, modified to save a lot of strcpy
 * and strcat by Matti Aarnio.
 */

#define TRUNCATE
#define DUMP_WIDTH	16

static int tls_dump(const char *s, int len)
{
    int     ret = 0;
    char    buf[160 + 1];
    char    *ss;
    int     i;
    int     j;
    int     rows;
    int     trunc;
    unsigned char ch;

    trunc = 0;

#ifdef TRUNCATE
    for (; (len > 0) && ((s[len - 1] == ' ') || (s[len - 1] == '\0')); len--)
	trunc++;
#endif

    rows = (len / DUMP_WIDTH);
    if ((rows * DUMP_WIDTH) < len)
	rows++;

    for (i = 0; i < rows; i++) {
	unsigned int val;
	buf[0] = '\0';				/* start with empty string */
	ss = buf;

	val = i * DUMP_WIDTH;
	assert(val <= 0xFFFF);
	sprintf(ss, "%04x ", i * DUMP_WIDTH);
	ss += strlen(ss);

	for (j = 0; j < DUMP_WIDTH; j++) {
	    if (((i * DUMP_WIDTH) + j) >= len) {
		strcpy(ss, "   ");
	    } else {
		ch = ((unsigned char) *((char *) (s) + i * DUMP_WIDTH + j))
		    & 0xFF;

		sprintf(ss, "%02x%c", ch, j == 7 ? '|' : ' ');
		ss += 3;
	    }
	}
	ss += strlen(ss);
	*ss+= ' ';
	for (j = 0; j < DUMP_WIDTH; j++) {
	    if (((i * DUMP_WIDTH) + j) >= len)
		break;
	    ch = ((unsigned char) *((char *) (s) + i * DUMP_WIDTH + j)) & 0xff;
	    *ss+= (((ch >= ' ') && (ch <= '~')) ? ch : '.');
	    if (j == 7) *ss+= ' ';
	}
	*ss = 0;
	/* 
	 * if this is the last call then update the ddt_dump thing so that
         * we will move the selection point in the debug window
         */	
	if (var_imapd_tls_loglevel>0)
	  syslog(LOG_DEBUG, "%s", buf);
	ret += strlen(buf);
    }
#ifdef TRUNCATE
    if (trunc > 0) {
	snprintf(buf, sizeof(buf), "%04x - <SPACES/NULS>\n", len+ trunc);
	if (var_imapd_tls_loglevel>0)
	  syslog(LOG_DEBUG, "%s", buf);
	ret += strlen(buf);
    }
#endif
    return (ret);
}

 /*
  * Set up the cert things on the server side. We do need both the
  * private key (in key_file) and the cert (in cert_file).
  * Both files may be identical.
  *
  * This function is taken from OpenSSL apps/s_cb.c
  */

static int set_cert_stuff(SSL_CTX * ctx,
			  const char *cert_file, const char *key_file)
{
    if (cert_file != NULL) {
	/* SSL_CTX_use_certificate_chain_file() requires an empty error stack.
	 * To make sure there is no error from previous op, we clear it here...
	 */
	ERR_clear_error();
	if (SSL_CTX_use_certificate_chain_file(ctx, cert_file) <= 0) {
	    syslog(LOG_ERR, "unable to get certificate from '%s'", cert_file);
	    return (0);
	}
	if (key_file == NULL)
	    key_file = cert_file;
	if (SSL_CTX_use_PrivateKey_file(ctx, key_file,
					SSL_FILETYPE_PEM) <= 0) {
	    syslog(LOG_ERR, "unable to get private key from '%s'", key_file);
	    return (0);
	}
	/* Now we know that a key and cert have been set against
         * the SSL context */
	if (!SSL_CTX_check_private_key(ctx)) {
	    syslog(LOG_ERR,
		   "Private key does not match the certificate public key");
	    return (0);
	}
    }
    return (1);
}

/*
 * The new_session_cb() is called, whenever a new session has been
 * negotiated and session caching is enabled.  We save the session in
 * a database so that we can share sessions between processes. 
 */ 
static int new_session_cb(SSL *ssl __attribute__((unused)),
			  SSL_SESSION *sess)
{
    int len;
    unsigned char *data = NULL;
    time_t expire;
    int ret = -1;
    unsigned char *asn;

    assert(sess);

    if (!sess_dbopen) return 0;

    /* find the size of the ASN1 representation of the session */
    len = i2d_SSL_SESSION(sess, NULL);

    /*
     * create the data buffer.  the data is stored as:
     * <expire time><ASN1 data>
     */
    data = (unsigned char *) xmalloc(sizeof(time_t)+len*sizeof(unsigned char));

    /* transform the session into its ASN1 representation */
    asn = data + sizeof(time_t);
    len = i2d_SSL_SESSION(sess, &asn);
    if (!len) syslog(LOG_ERR, "i2d_SSL_SESSION failed");

    /* set the expire time for the external cache, and prepend it to data */
    expire = SSL_SESSION_get_time(sess) + SSL_SESSION_get_timeout(sess);
    memcpy(data, &expire, sizeof(time_t));

    if (len) {
	/* store the session in our database */
	do {
	    ret = DB->store(sessdb, (const char *) sess->session_id,
			    sess->session_id_length,
			    (const char *) data, len + sizeof(time_t), NULL);
	} while (ret == CYRUSDB_AGAIN);
    }

    free(data);

    /* log this transaction */
    if (var_imapd_tls_loglevel > 0) {
	unsigned int i;
	char idstr[SSL_MAX_SSL_SESSION_ID_LENGTH*2 + 1];
	for (i = 0; i < sess->session_id_length; i++) {
	    sprintf(idstr+i*2, "%02X", sess->session_id[i]);
	}
	syslog(LOG_DEBUG, "new TLS session: id=%s, expire=%s, status=%s",
	       idstr, ctime(&expire), ret ? "failed" : "ok");
    }

    return (ret == 0);
}

/*
 * Function for removing a session from our database.
 */
static void remove_session(unsigned char *id, int idlen)
{
    int ret;

    assert(id);
    assert(idlen <= SSL_MAX_SSL_SESSION_ID_LENGTH);
    
    if (!sess_dbopen) return;

    do {
	ret = DB->delete(sessdb, (const char *) id, idlen, NULL, 1);
    } while (ret == CYRUSDB_AGAIN);

    /* log this transaction */
    if (var_imapd_tls_loglevel > 0) {
	int i;
	char idstr[SSL_MAX_SSL_SESSION_ID_LENGTH*2 + 1];

	for (i = 0; i < idlen; i++) {
	    sprintf(idstr+i*2, "%02X", id[i]);
	}
	    
	syslog(LOG_DEBUG, "remove TLS session: id=%s", idstr);
    }
}

/*
 * The remove_session_cb() is called, whenever the SSL engine removes
 * a session from the internal cache. This happens if the session is
 * removed because it is expired or when a connection was not shutdown
 * cleanly.
 */
static void remove_session_cb(SSL_CTX *ctx __attribute__((unused)),
			      SSL_SESSION *sess)
{
    assert(sess);

    remove_session(sess->session_id, sess->session_id_length);
}

/*
 * The get_session_cb() is only called on SSL/TLS servers with the
 * session id proposed by the client. The get_session_cb() is always
 * called, also when session caching was disabled.  We lookup the
 * session in our database in case it was stored by another process.
 */
static SSL_SESSION *get_session_cb(SSL *ssl __attribute__((unused)),
				   unsigned char *id, int idlen, int *copy)
{
    int ret;
    const char *data = NULL;
    int len = 0;
    time_t expire = 0, now = time(0);
    SSL_SESSION *sess = NULL;

    assert(id);
    assert(idlen <= SSL_MAX_SSL_SESSION_ID_LENGTH);

    if (!sess_dbopen) return NULL;

    do {
	ret = DB->fetch(sessdb, (const char *) id, idlen, &data, &len, NULL);
    } while (ret == CYRUSDB_AGAIN);

    if (!ret && data) {
	assert(len >= (int) sizeof(time_t));

	/* grab the expire time */
	memcpy(&expire, data, sizeof(time_t));

	/* check if the session has expired */
	if (expire < now) {
	    remove_session(id, idlen);
	}
	else {
	    /* transform the ASN1 representation of the session
	       into an SSL_SESSION object */
	    const unsigned char *asn = (unsigned char *) data + sizeof(time_t);
	    sess = d2i_SSL_SESSION(NULL, &asn, len - sizeof(time_t));
	    if (!sess) syslog(LOG_ERR, "d2i_SSL_SESSION failed: %m");
	}
    }

    /* log this transaction */
    if (var_imapd_tls_loglevel > 0) {
	int i;
	char idstr[SSL_MAX_SSL_SESSION_ID_LENGTH*2 + 1];
	for (i = 0; i < idlen; i++)
	    sprintf(idstr+i*2, "%02X", id[i]);

	syslog(LOG_DEBUG, "get TLS session: id=%s, expire=%s, status=%s",
	       idstr, ctime(&expire),
	       !data ? "not found" : expire < now ? "expired" : "ok");
    }

    *copy = 0;
    return sess;
}

/*
 * Seed the random number generator.
 */
static int tls_rand_init(void)
{
#ifdef EGD_SOCKET
    return (RAND_egd(EGD_SOCKET));
#else
    /* otherwise let OpenSSL do it internally */
    return 0;
#endif
}

 /*
  * This is the setup routine for the SSL server. As smtpd might be called
  * more than once, we only want to do the initialization one time.
  *
  * The skeleton of this function is taken from OpenSSL apps/s_server.c.

  * returns -1 on error
  */

/* must be called after cyrus_init */
int     tls_init_serverengine(const char *ident,
			      int verifydepth,
			      int askcert,
			      int tlsonly)
{
    int     off = 0;
    int     verify_flags = SSL_VERIFY_NONE;
    const char   *cipher_list;
    const char   *CApath;
    const char   *CAfile;
    const char   *s_cert_file;
    const char   *s_key_file;
    int    requirecert;
    int    timeout;

    if (tls_serverengine)
	return (0);				/* already running */

    if (var_imapd_tls_loglevel >= 2)
	syslog(LOG_DEBUG, "starting TLS server engine");

    SSL_library_init();
    SSL_load_error_strings();
    if (tls_rand_init() == -1) {
	syslog(LOG_ERR,"TLS server engine: cannot seed PRNG");
	return -1;
    }

#if 0
    if (tlsonly) {
	s_ctx = SSL_CTX_new(TLSv1_server_method());
    } else {
	s_ctx = SSL_CTX_new(SSLv23_server_method());
    }
#endif
    /* even if we want TLS only, we use SSLv23 server method so we can
       deal with a client sending an SSLv2 greeting message */

    s_ctx = SSL_CTX_new(SSLv23_server_method());
    if (s_ctx == NULL) {
	return (-1);
    };

    off |= SSL_OP_ALL;		/* Work around all known bugs */
    if (tlsonly) {
	off |= SSL_OP_NO_SSLv2;
	off |= SSL_OP_NO_SSLv3;
    }
    SSL_CTX_set_options(s_ctx, off);
    SSL_CTX_set_info_callback(s_ctx, (void (*)()) apps_ssl_info_callback);

    /* Don't use an internal session cache */
    SSL_CTX_sess_set_cache_size(s_ctx, 1);  /* 0 is unlimited, so use 1 */
    SSL_CTX_set_session_cache_mode(s_ctx, SSL_SESS_CACHE_SERVER |
				   SSL_SESS_CACHE_NO_AUTO_CLEAR |
				   SSL_SESS_CACHE_NO_INTERNAL_LOOKUP);

    /* Get the session timeout from the config file (in minutes) */
    timeout = config_getint(IMAPOPT_TLS_SESSION_TIMEOUT);
    if (timeout < 0) timeout = 0;
    if (timeout > 1440) timeout = 1440; /* 24 hours max */

    /* A timeout of zero disables session caching */
    if (timeout) {
	char dbdir[1024];
	int r;

	/* Set the context for session reuse -- use the service ident */
	SSL_CTX_set_session_id_context(s_ctx, (void*) ident, strlen(ident));

	/* Set the timeout for the internal/external cache (in seconds) */
	SSL_CTX_set_timeout(s_ctx, timeout*60);

	/* Set the callback functions for the external session cache */
	SSL_CTX_sess_set_new_cb(s_ctx, new_session_cb);
	SSL_CTX_sess_set_remove_cb(s_ctx, remove_session_cb);
	SSL_CTX_sess_set_get_cb(s_ctx, get_session_cb);

	/* create the name of the db file */
	strlcpy(dbdir, config_dir, sizeof(dbdir));
	strlcat(dbdir, FNAME_TLSSESSIONS, sizeof(dbdir));

	r = (DB->open)(dbdir, CYRUSDB_CREATE, &sessdb);
	if (r != 0) {
	    syslog(LOG_ERR, "DBERROR: opening %s: %s",
		   dbdir, cyrusdb_strerror(ret));
	}
	else
	    sess_dbopen = 1;
    }

    cipher_list = config_getstring(IMAPOPT_TLS_CIPHER_LIST);
    if (!SSL_CTX_set_cipher_list(s_ctx, cipher_list)) {
	syslog(LOG_ERR,"TLS server engine: cannot load cipher list '%s'",
	       cipher_list);
	return (-1);
    }

    CAfile = config_getstring(IMAPOPT_TLS_CA_FILE);
    CApath = config_getstring(IMAPOPT_TLS_CA_PATH);

    if ((!SSL_CTX_load_verify_locations(s_ctx, CAfile, CApath)) ||
	(!SSL_CTX_set_default_verify_paths(s_ctx))) {
	/* just a warning since this is only necessary for client auth */
	syslog(LOG_NOTICE,"TLS server engine: cannot load CA data");	
    }

    s_cert_file = config_getstring(IMAPOPT_TLS_CERT_FILE);
    s_key_file = config_getstring(IMAPOPT_TLS_KEY_FILE);

    if (!set_cert_stuff(s_ctx, s_cert_file, s_key_file)) {
	syslog(LOG_ERR,"TLS server engine: cannot load cert/key data");
	return (-1);
    }
    SSL_CTX_set_tmp_rsa_callback(s_ctx, tmp_rsa_cb);

#if (OPENSSL_VERSION_NUMBER >= 0x0090800fL)
    /* Load DH params for DHE-* key exchanges */
    SSL_CTX_set_tmp_dh(s_ctx, load_dh_param(s_key_file, s_cert_file));
    /* FIXME: Load ECDH params for ECDHE suites when 0.9.9 is released */
#endif

    verify_depth = verifydepth;
    if (askcert!=0)
	verify_flags |= SSL_VERIFY_PEER | SSL_VERIFY_CLIENT_ONCE;

    requirecert = config_getswitch(IMAPOPT_TLS_REQUIRE_CERT);
    if (requirecert)
	verify_flags |= SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT
	    | SSL_VERIFY_CLIENT_ONCE;
    SSL_CTX_set_verify(s_ctx, verify_flags, verify_callback);

    if (askcert || requirecert) {
      if (CAfile == NULL) {
	  syslog(LOG_ERR, 
		 "TLS server engine: No CA file specified. "
		 "Client side certs may not work");
      } else {
	  SSL_CTX_set_client_CA_list(s_ctx, SSL_load_client_CA_file(CAfile));
      }
    }

    tls_serverengine = 1;
    return (0);
}


/* taken from OpenSSL apps/s_cb.c */

static long bio_dump_cb(BIO * bio, int cmd, const char *argp, int argi,
			long argl __attribute__((unused)), long ret)
{
    if (!do_dump)
	return (ret);

    if (cmd == (BIO_CB_READ | BIO_CB_RETURN)) {
	printf("read from %08lX [%08lX] (%d bytes => %ld (0x%lX))",
	       (unsigned long)bio, (unsigned long)argp,
	       argi, ret, ret);
	tls_dump(argp, (int) ret);
	return (ret);
    } else if (cmd == (BIO_CB_WRITE | BIO_CB_RETURN)) {
	printf("write to %08lX [%08lX] (%d bytes => %ld (0x%lX))",
	       (unsigned long) bio, (unsigned long)argp,
	       argi, ret, ret);
	tls_dump(argp, (int) ret);
    }
    return (ret);
}




 /*
  * This is the actual startup routine for the connection. We expect
  * that the buffers are flushed and the "Ready to start TLS" was
  * send to the client, so that we can immediately can start the TLS
  * handshake process.
  *
  * 'layerbits' and 'authid' are filled in on success. authid is only
  * filled in if the client authenticated. 'ret' is the SSL connection
  * on success.
  */
int tls_start_servertls(int readfd, int writefd, int timeout,
			int *layerbits, char **authid, SSL **ret)
{
    int     sts;
    int     j;
    unsigned int n;
    SSL_CIPHER *cipher;
    X509   *peer;
    const char *tls_protocol = NULL;
    const char *tls_cipher_name = NULL;
    int tls_cipher_usebits = 0;
    int tls_cipher_algbits = 0;
    SSL *tls_conn;
    int r = 0;

    assert(tls_serverengine);
    assert(ret);
    if (var_imapd_tls_loglevel >= 1)
	syslog(LOG_DEBUG, "setting up TLS connection");

    if (authid) *authid = NULL;

    tls_conn = (SSL *) SSL_new(s_ctx);
    if (tls_conn == NULL) {
	*ret = NULL;
	r = -1;
	goto done;
    }
    SSL_clear(tls_conn);
    
    /* set the file descriptors for SSL to use */
    if ((SSL_set_rfd(tls_conn, readfd) == 0) || 
	(SSL_set_wfd(tls_conn, writefd) == 0)) {
	r = -1;
	goto done;
    }

    /*
     * This is the actual handshake routine. It will do all the negotiations
     * and will check the client cert etc.
     */
    SSL_set_accept_state(tls_conn);

    /*
     * We do have an SSL_set_fd() and now suddenly a BIO_ routine is called?
     * Well there is a BIO below the SSL routines that is automatically
     * created for us, so we can use it for debugging purposes.
     */
    if (var_imapd_tls_loglevel >= 3)
	BIO_set_callback(SSL_get_rbio(tls_conn), bio_dump_cb);

    /* Dump the negotiation for loglevels 3 and 4*/
    if (var_imapd_tls_loglevel >= 3)
	do_dump = 1;

    nonblock(readfd, 1);
    while (1) {
	fd_set rfds;
	struct timeval tv;
	int err;

	FD_ZERO(&rfds);
	FD_SET(readfd, &rfds);
	tv.tv_sec = timeout;
	tv.tv_usec = 0;

	sts = select(1, &rfds, NULL, NULL, &tv);
	if (sts <= 0) {
	    if (sts == 0) {
		syslog(LOG_DEBUG, "SSL_accept() timed out -> fail");
	    } else {
		syslog(LOG_DEBUG,
		       "tls_start_servertls() failed in select() -> fail: %m");
	    }
	    r = -1;
	    goto done;
	}

	sts = SSL_accept(tls_conn);
	if (sts > 0) {
	    syslog(LOG_DEBUG, "SSL_accept() succeeded -> done");
	    break;
	}

	/* Check the error code */
	err = SSL_get_error(tls_conn, sts);
	switch (err) {
	case SSL_ERROR_WANT_READ:
	case SSL_ERROR_WANT_WRITE:
	    syslog(LOG_DEBUG, "SSL_accept() incomplete -> wait");
	    continue;
	case SSL_ERROR_SYSCALL:
	    if (sts == 0) {
		syslog(LOG_DEBUG, "EOF in SSL_accept() -> fail");
	    } else if (errno == EINTR || errno == EAGAIN) {
		syslog(LOG_DEBUG,
		       "SSL_accept() interrupted by signal %m -> retry");
		continue;
	    } else {
		syslog(LOG_DEBUG,
		       "SSL_accept() interrupted by signal %m -> fail");
	    }
	    break;
	case SSL_ERROR_SSL:
	    err = ERR_get_error();
	    if (err == 0) {
		syslog(LOG_DEBUG, "protocol error in SSL_accept() -> fail");
	    } else {
		syslog(LOG_DEBUG, "%s in SSL_accept() -> fail",
		       ERR_reason_error_string(err));
	    }
	    break;
	case SSL_ERROR_ZERO_RETURN:
	    syslog(LOG_DEBUG,
		   "TLS/SSL connection closed in SSL_accept() -> fail");
	    break;
	default:
	    syslog(LOG_DEBUG,
		   "SSL_accept() failed with unknown error %d -> fail",
		   err);
	    break;
	}
	r = -1;
	goto done;

	/* Should never get here */
    }

    /* Only loglevel==4 dumps everything */
    if (var_imapd_tls_loglevel < 4)
	do_dump = 0;

    /*
     * Lets see, whether a peer certificate is available and what is
     * the actual information. We want to save it for later use.
     */
    peer = SSL_get_peer_certificate(tls_conn);
    if (peer != NULL) {
	char fingerprint[EVP_MAX_MD_SIZE * 3];
	char issuer_CN[CCERT_BUFSIZ];
	char peer_issuer[CCERT_BUFSIZ];
	char peer_CN[CCERT_BUFSIZ];
	char peer_subject[CCERT_BUFSIZ];
	unsigned char md[EVP_MAX_MD_SIZE];

	syslog(LOG_DEBUG, "received client certificate");

	X509_NAME_oneline(X509_get_subject_name(peer),
			  peer_subject, CCERT_BUFSIZ);
	syslog(LOG_DEBUG, "subject=%s", peer_subject);
	X509_NAME_oneline(X509_get_issuer_name(peer),
			  peer_issuer, CCERT_BUFSIZ);
	if (var_imapd_tls_loglevel >= 2)
	    syslog(LOG_DEBUG, "issuer=%s", peer_issuer);

	if (X509_digest(peer, EVP_md5(), md, &n)) {
	    for (j = 0; j < (int) n; j++)
	    {
		fingerprint[j * 3] = hexcodes[(md[j] & 0xf0) >> 4];
		fingerprint[(j * 3) + 1] = hexcodes[(md[j] & 0x0f)];
		if (j + 1 != (int) n) {
		    fingerprint[(j * 3) + 2] = '_';
		} else {
		    fingerprint[(j * 3) + 2] = '\0';
		}
	    }
	    if (var_imapd_tls_loglevel >= 2)
		syslog(LOG_DEBUG, "fingerprint=%s", fingerprint);
	}
	X509_NAME_get_text_by_NID(X509_get_subject_name(peer),
			  NID_commonName, peer_CN, CCERT_BUFSIZ);
	X509_NAME_get_text_by_NID(X509_get_issuer_name(peer),
			  NID_commonName, issuer_CN, CCERT_BUFSIZ);
	if (var_imapd_tls_loglevel >= 3)
	    syslog(LOG_DEBUG, "subject_CN=%s, issuer_CN=%s", 
		   peer_CN, issuer_CN);

	/* xxx verify that we like the peer_issuer/issuer_CN */

	if (authid != NULL) {
	    /* save the peer id for our caller */
	    *authid = peer_CN[0] ? xstrdup(peer_CN) : NULL;
	}
	X509_free(peer);
    }
    tls_protocol = SSL_get_version(tls_conn);
    cipher = SSL_get_current_cipher(tls_conn);
    tls_cipher_name = SSL_CIPHER_get_name(cipher);
    tls_cipher_usebits = SSL_CIPHER_get_bits(cipher, &tls_cipher_algbits);

    if (layerbits != NULL) {
	*layerbits = tls_cipher_usebits;
    }

    if (authid && *authid) {
	syslog(LOG_NOTICE, "starttls: %s with cipher %s (%d/%d bits %s)"
	                   " authenticated as %s", 
	       tls_protocol, tls_cipher_name,
	       tls_cipher_usebits, tls_cipher_algbits, 
	       SSL_session_reused(tls_conn) ? "reused" : "new",
	       *authid);
    } else {
	syslog(LOG_NOTICE, "starttls: %s with cipher %s (%d/%d bits %s)"
	                   " no authentication", 
	       tls_protocol, tls_cipher_name,
	       tls_cipher_usebits, tls_cipher_algbits,
	       SSL_session_reused(tls_conn) ? "reused" : "new");
    }

 done:
    nonblock(readfd, 0);
    if (r && tls_conn) {
	/* error; clean up */
	SSL_SESSION *session = SSL_get_session(tls_conn);
	if (session) {
	    SSL_CTX_remove_session(s_ctx, session);
	}
	SSL_free(tls_conn);
	tls_conn = NULL;
    }
    *ret = tls_conn;
    return r;
}

int tls_reset_servertls(SSL **conn)
{
    int r = 0;

    if (*conn) {
	if (TLS_FAST_SHUTDOWN) {
	    /*
	     * Don't bother spending time closing the TLS session,
	     * but make sure its available for reuse.
	     */
	    SSL_set_shutdown(*conn,SSL_SENT_SHUTDOWN|SSL_RECEIVED_SHUTDOWN);
	}
	else {
	    /* Follow the TLS protocol and do a shutdown handshake */
	    r = SSL_shutdown(*conn);
	    if (r == 0) {
		/* Just sent, now wait for peer to ack */
		r = SSL_shutdown(*conn);
	    }
	    if (r == 0) r = -1;
	}
	SSL_free(*conn);
    }
    
    return r;
}

int tls_shutdown_serverengine(void)
{
    int r;

    if (tls_serverengine && sess_dbopen) {
	r = (DB->close)(sessdb);
	if (r) {
	    syslog(LOG_ERR, "DBERROR: error closing tlsdb: %s",
		   cyrusdb_strerror(r));
	}
	sessdb = NULL;
	sess_dbopen = 0;
    }

    return 0;

}

/*
 * Delete expired sessions.
 */
struct prunerock {
    int count;
    int deletions;
};

static int prune_p(void *rock, const char *id, int idlen,
		   const char *data, int datalen)
{
    struct prunerock *prock = (struct prunerock *) rock;
    time_t expire;

    prock->count++;

    assert(datalen >= (int) sizeof(time_t));

    /* grab the expire time */
    memcpy(&expire, data, sizeof(time_t));

    /* log this transaction */
    if (var_imapd_tls_loglevel > 0) {
	int i;
	char idstr[SSL_MAX_SSL_SESSION_ID_LENGTH*2 + 1];

	assert(idlen <= SSL_MAX_SSL_SESSION_ID_LENGTH);

	for (i = 0; i < idlen; i++) {
	    sprintf(idstr+i*2, "%02X", (unsigned char) id[i]);
	}
	
	syslog(LOG_DEBUG, "found TLS session: id=%s, expire=%s",
	       idstr, ctime(&expire));
    }

    /* check if the session has expired */
    return (expire < time(0));
}

static int prune_cb(void *rock, const char *id, int idlen,
		    const char *data __attribute__((unused)), 
                    int datalen __attribute__((unused)))
{
    struct prunerock *prock = (struct prunerock *) rock;

    prock->deletions++;

    remove_session((unsigned char*) id, idlen);

    return 0;
}

/* must be called after cyrus_init */
int tls_prune_sessions(void)
{
    char dbdir[1024];
    int ret;
    struct prunerock prock;

   /* create the name of the db file */
    strlcpy(dbdir, config_dir, sizeof(dbdir));
    strlcat(dbdir, FNAME_TLSSESSIONS, sizeof(dbdir));

    ret = (DB->open)(dbdir, 0, &sessdb);
    if (ret != CYRUSDB_OK) {
	syslog(LOG_ERR, "DBERROR: opening %s: %s",
	       dbdir, cyrusdb_strerror(ret));
	return 1;
    }
    else {
	/* check each session in our database */
	sess_dbopen = 1;
	prock.count = prock.deletions = 0;
	DB->foreach(sessdb, "", 0, &prune_p, &prune_cb, &prock, NULL);
	(DB->close)(sessdb);
	sessdb = NULL;
	sess_dbopen = 0;

	syslog(LOG_NOTICE, "tls_prune: purged %d out of %d entries",
	       prock.deletions, prock.count);
    }

    return 0;
}

/* fill string buffer with info about tls connection */
int tls_get_info(SSL *conn, char *buf, size_t len)
{
    int usebits = 0;
    int algbits = 0;

    usebits = SSL_get_cipher_bits(conn, &algbits);
    snprintf(buf, len, "version=%s cipher=%s bits=%d/%d verify=%s",
	     SSL_get_cipher_version(conn), SSL_get_cipher_name(conn),
	     usebits, algbits,
	     SSL_get_verify_result(conn) == X509_V_OK ? "YES" : "NO");

    return (strlen(buf));
}

int tls_init_clientengine(int verifydepth,
			  char *var_tls_cert_file,
			  char *var_tls_key_file)
{
    int     off = 0;
    int     verify_flags = SSL_VERIFY_NONE;
    const char   *CApath;
    const char   *CAfile;
    char   *c_cert_file;
    char   *c_key_file;
    
    if (tls_clientengine)
	return (0);				/* already running */

    if (var_proxy_tls_loglevel >= 2)
	syslog(LOG_DEBUG, "starting TLS client engine");

    SSL_library_init();
    SSL_load_error_strings();
    if (tls_rand_init() == -1) {
	printf("TLS client engine: cannot seed PRNG\n");
	return -1;
    }
    
    c_ctx = SSL_CTX_new(TLSv1_client_method());
    if (c_ctx == NULL) {
	return (-1);
    };
    
    off |= SSL_OP_ALL;		/* Work around all known bugs */
    SSL_CTX_set_options(c_ctx, off);
    SSL_CTX_set_info_callback(c_ctx, (void (*)()) apps_ssl_info_callback);
    
    CAfile = config_getstring(IMAPOPT_TLS_CA_FILE);
    CApath = config_getstring(IMAPOPT_TLS_CA_PATH);

    if ((!SSL_CTX_load_verify_locations(c_ctx, CAfile, CApath)) ||
	(!SSL_CTX_set_default_verify_paths(c_ctx))) {
	/* just a warning since this is only necessary for client auth */
	syslog(LOG_NOTICE,"TLS client engine: cannot load CA data");	
    }

    if (strlen(var_tls_cert_file) == 0)
	c_cert_file = NULL;
    else
	c_cert_file = var_tls_cert_file;
    if (strlen(var_tls_key_file) == 0)
	c_key_file = NULL;
    else
	c_key_file = var_tls_key_file;
    
    if (c_cert_file || c_key_file) {
	if (!set_cert_stuff(c_ctx, c_cert_file, c_key_file)) {
	    syslog(LOG_ERR,"TLS client engine: cannot load cert/key data");
	    return (-1);
	}
    }
    SSL_CTX_set_tmp_rsa_callback(c_ctx, tmp_rsa_cb);
    
    verify_depth = verifydepth;
    SSL_CTX_set_verify(c_ctx, verify_flags, verify_callback);
    
    tls_clientengine = 1;
    return (0);
}

int tls_start_clienttls(int readfd, int writefd,
			int *layerbits, char **authid, SSL **ret,
			SSL_SESSION **sess)
{
    int     sts;
    SSL_CIPHER *cipher;
    X509   *peer;
    const char *tls_protocol = NULL;
    const char *tls_cipher_name = NULL;
    int tls_cipher_usebits = 0;
    int tls_cipher_algbits = 0;
    SSL *tls_conn;
    int r = 0;
    
    assert(tls_clientengine);
    assert(ret);
    if (var_proxy_tls_loglevel >= 1)
	syslog(LOG_DEBUG, "setting up TLS connection");

    if (authid) *authid = NULL;

    tls_conn = (SSL *) SSL_new(c_ctx);
    if (tls_conn == NULL) {
	*ret = NULL;
	r = -1;
	goto done;
    }
    SSL_clear(tls_conn);
    
    /* set the file descriptors for SSL to use */
    if ((SSL_set_rfd(tls_conn, readfd) == 0) || 
	(SSL_set_wfd(tls_conn, writefd) == 0)) {
	r = -1;
	goto done;
    }

    /*
     * This is the actual handshake routine. It will do all the negotiations
     * and will check the client cert etc.
     */
    SSL_set_connect_state(tls_conn);
    
    /*
     * We do have an SSL_set_fd() and now suddenly a BIO_ routine is called?
     * Well there is a BIO below the SSL routines that is automatically
     * created for us, so we can use it for debugging purposes.
     */
    if (var_proxy_tls_loglevel >= 3)
	BIO_set_callback(SSL_get_rbio(tls_conn), bio_dump_cb);

    /* Dump the negotiation for loglevels 3 and 4*/
    if (var_proxy_tls_loglevel >= 3)
	do_dump = 1;

    if (sess && *sess)  /* Reuse a session if we have one */
	SSL_set_session(tls_conn, *sess);

    if ((sts = SSL_connect(tls_conn)) <= 0) {
	SSL_SESSION *session = SSL_get_session(tls_conn);
	if (session) {
	    SSL_CTX_remove_session(c_ctx, session);
	}
	if (sess) *sess = NULL;
	r = -1;
	goto done;
    }
    if (sess) *sess = SSL_get_session(tls_conn);

    /* Only loglevel==4 dumps everything */
    if (var_proxy_tls_loglevel < 4)
	do_dump = 0;
    
    /*
     * Lets see, whether a peer certificate is available and what is
     * the actual information. We want to save it for later use.
     */
    peer = SSL_get_peer_certificate(tls_conn);
    if (peer != NULL) {
	char issuer_CN[CCERT_BUFSIZ];
	char peer_CN[CCERT_BUFSIZ];

	syslog(LOG_DEBUG, "received server certificate");

	X509_NAME_get_text_by_NID(X509_get_subject_name(peer),
				  NID_commonName, peer_CN, CCERT_BUFSIZ);
	X509_NAME_get_text_by_NID(X509_get_issuer_name(peer),
				  NID_commonName, issuer_CN, CCERT_BUFSIZ);
	if (var_proxy_tls_loglevel >= 3)
	    syslog(LOG_DEBUG, "subject_CN=%s, issuer_CN=%s", 
		   peer_CN, issuer_CN);

	/* xxx verify that we like the peer_issuer/issuer_CN */

	if (authid != NULL) {
	    /* save the peer id for our caller */
	    *authid = peer_CN[0] ? xstrdup(peer_CN) : NULL;
	}
	X509_free(peer);
    }
    tls_protocol = SSL_get_version(tls_conn);
    cipher = SSL_get_current_cipher(tls_conn);
    tls_cipher_name = SSL_CIPHER_get_name(cipher);
    tls_cipher_usebits = SSL_CIPHER_get_bits(cipher, &tls_cipher_algbits);
    
    if (layerbits != NULL)
	*layerbits = tls_cipher_usebits;
    
    syslog(LOG_DEBUG, "starttls: %s with cipher %s (%d/%d bits %s client)"
	   " no authentication", 
	   tls_protocol, tls_cipher_name,
	   tls_cipher_usebits, tls_cipher_algbits,
	   SSL_session_reused(tls_conn) ? "reused" : "new");

  done:
    if (r && tls_conn) {
	/* error; clean up */
	SSL_free(tls_conn);
	tls_conn = NULL;
    }
    *ret = tls_conn;
    return r;

}

#else

int tls_enabled(void)
{
    return 0;
}

#endif /* HAVE_SSL */
