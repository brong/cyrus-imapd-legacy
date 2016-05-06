/* httpd.h -- Common state for HTTP/RSS/WebDAV/CalDAV/iSchedule daemon
 *
 * Copyright (c) 1994-2011 Carnegie Mellon University.  All rights reserved.
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
 */

#ifndef HTTPD_H
#define HTTPD_H

#include <sasl/sasl.h>
#include <libxml/tree.h>
#include <libxml/uri.h>
#include <libical/ical.h>

#ifdef HAVE_ZLIB
#include <zlib.h>
#endif /* HAVE_ZLIB */

#include "annotate.h" /* for strlist */
#include "hash.h"
#include "http_client.h"
#include "mailbox.h"
#include "spool.h"

#define MAX_REQ_LINE    8000  /* minimum size per RFC 7230 */
#define MARKUP_INDENT   2     /* # spaces to indent each line of markup */
#define GZIP_MIN_LEN    300   /* minimum length of data to gzip */

#define DFLAG_UNBIND    "DAV:unbind"
#define DFLAG_UNCHANGED "DAV:unchanged"

/* XML namespace URIs */
#define XML_NS_CYRUS    "http://cyrusimap.org/ns/"

/* Supported TLS version for Upgrade */
#define TLS_VERSION      "TLS/1.0"

/* Supported HTML DOCTYPE */
#define HTML_DOCTYPE \
    "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" " \
    "\"http://www.w3.org/TR/html4/loose.dtd\">"

#define XML_DECLARATION \
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>"

/* Macro to return proper response code when user privileges are insufficient */
#define HTTP_NO_PRIVS \
    (httpd_userid && !is_userid_anonymous(httpd_userid) ? \
     HTTP_FORBIDDEN : HTTP_UNAUTHORIZED)

/* Macro to access query part of URI */
#if LIBXML_VERSION >= 20700
#define URI_QUERY(uri) uri->query_raw
#else
#define URI_QUERY(uri) uri->query
#endif

/* SASL usage based on availability */
#if defined(SASL_NEED_HTTP) && defined(SASL_HTTP_REQUEST)
  #define HTTP_DIGEST_MECH "DIGEST-MD5"
  #define SASL_USAGE_FLAGS (SASL_NEED_HTTP | SASL_SUCCESS_DATA)
#else
  #define HTTP_DIGEST_MECH NULL  /* not supported by our SASL version */
  #define SASL_USAGE_FLAGS SASL_SUCCESS_DATA
#endif /* SASL_NEED_HTTP */

/* Array of HTTP methods known by our server. */
struct known_meth_t {
    const char *name;
    unsigned flags;
};
extern const struct known_meth_t http_methods[];

/* Flags for known methods*/
enum {
    METH_NOBODY =       (1<<0), /* Method does not expect a body */
};


/* Path namespaces */
enum {
    URL_NS_DEFAULT = 0,
    URL_NS_PRINCIPAL,
    URL_NS_NOTIFY,
    URL_NS_CALENDAR,
    URL_NS_FREEBUSY,
    URL_NS_ADDRESSBOOK,
    URL_NS_DRIVE,
    URL_NS_ISCHEDULE,
    URL_NS_DOMAINKEY,
    URL_NS_TZDIST,
    URL_NS_RSS,
    URL_NS_DBLOOKUP,
    URL_NS_JMAP,
    URL_NS_ADMIN,
#ifdef ENABLE_APPLEPUSHSERVICE
    URL_NS_APPLEPUSH
#endif
};

/* Bitmask of features/methods to allow, based on URL */
enum {
    ALLOW_READ =        (1<<0), /* Read resources/properties */
    ALLOW_POST =        (1<<1), /* Post to a URL */
    ALLOW_WRITE =       (1<<2), /* Create/modify/lock resources */
    ALLOW_PATCH =       (1<<3), /* Patch resources */
    ALLOW_DELETE =      (1<<4), /* Delete resources/collections */
    ALLOW_TRACE =       (1<<5), /* TRACE a request */

    ALLOW_DAV =         (1<<8), /* WebDAV specific methods/features */
    ALLOW_PROPPATCH  =  (1<<9), /* Modify properties */
    ALLOW_MKCOL =       (1<<10),/* Create collections */
    ALLOW_ACL =         (1<<11),/* Modify access control list */

    ALLOW_CAL =         (1<<16),/* CalDAV specific methods/features */
    ALLOW_CAL_SCHED =   (1<<17),/* CalDAV Scheduling specific features */
    ALLOW_CAL_AVAIL =   (1<<18),/* CalDAV Availability specific features */
    ALLOW_CAL_NOTZ =    (1<<19),/* CalDAV TZ by Ref specific features */
    ALLOW_CAL_ATTACH =  (1<<20),/* CalDAV Managed Attachments features */

    ALLOW_CARD =        (1<<24),/* CardDAV specific methods/features */

    ALLOW_ISCHEDULE =   (1<<31) /* iSchedule specific methods/features */
};

#define ALLOW_READ_MASK ~(ALLOW_POST|ALLOW_WRITE|ALLOW_DELETE|ALLOW_PATCH\
                          |ALLOW_PROPPATCH|ALLOW_MKCOL|ALLOW_ACL)


struct auth_scheme_t {
    unsigned idx;               /* Index value of the scheme */
    const char *name;           /* HTTP auth scheme name */
    const char *saslmech;       /* Corresponding SASL mech name */
    unsigned flags;             /* Bitmask of requirements/features */
                                /* Optional function to send success data */
    void (*send_success)(const char *name, const char *data);
                                /* Optional function to recv success data */
    const char *(*recv_success)(hdrcache_t hdrs);
};

/* Index into available schemes */
enum {
    AUTH_BASIC = 0,
    AUTH_DIGEST,
    AUTH_SPNEGO,
    AUTH_NTLM
};

/* Auth scheme flags */
enum {
    AUTH_NEED_PERSIST = (1<<0), /* Persistent connection required */
    AUTH_NEED_REQUEST = (1<<1), /* Request-line required */
    AUTH_SERVER_FIRST = (1<<2), /* SASL mech is server-first */
    AUTH_BASE64 =       (1<<3)  /* Base64 encode/decode auth data */
};

/* List of HTTP auth schemes that we support */
extern struct auth_scheme_t auth_schemes[];

extern const char *digest_recv_success(hdrcache_t hdrs);


/* Request-line context */
struct request_line_t {
    char buf[MAX_REQ_LINE+1];   /* working copy of request-line */
    char *meth;                 /* method */
    char *uri;                  /* request-target */
    char *ver;                  /* HTTP-version */
};


/* Request target context */
struct request_target_t {
    char path[MAX_MAILBOX_PATH+1]; /* working copy of URL path */
    char *tail;                 /* tail of original request path */
    unsigned namespace;         /* namespace of path */
    char *userid;               /* owner of collection (needs freeing) */
    char *collection;           /* ptr to collection name */
    size_t collen;
    char *resource;             /* ptr to resource name */
    size_t reslen;
    unsigned flags;             /* target-specific flags/meta-data */
    unsigned long allow;        /* bitmask of allowed features/methods */
    int mboxtype;               /* mailbox types to match on findall */
    mbentry_t *mbentry;         /* mboxlist entry of target collection */
    const char *urlprefix;      /* namespace prefix */
    const char *mboxprefix;     /* mailbox prefix */
};

/* Request target flags */
enum {
    TGT_SERVER_INFO = 1,
    TGT_DAV_SHARED,
    TGT_SCHED_INBOX,
    TGT_SCHED_OUTBOX,
    TGT_MANAGED_ATTACH,
    TGT_DRIVE_ROOT,
    TGT_DRIVE_USER
};

/* Function to parse URI path and generate a mailbox name */
typedef int (*parse_path_t)(const char *path,
                            struct request_target_t *tgt, const char **errstr);

/* Auth challenge context */
struct auth_challenge_t {
    struct auth_scheme_t *scheme;       /* Selected AUTH scheme */
    const char *param;                  /* Server challenge */
};

/* Meta-data for error response */
struct error_t {
    const char *desc;                   /* Error description */
    unsigned precond;                   /* [Cal]DAV precondition */
    xmlNodePtr node;                    /* XML node to be added to error */
    const char *resource;               /* Resource href to be added to error */
    int rights;                         /* Privileges needed by resource */
};

struct range {
    unsigned long first;
    unsigned long last;
    struct range *next;
};

struct patch_doc_t {
    const char *format;                 /* MIME format of patch document */
    int (*proc)();                      /* Function to parse and apply doc */
};


/* Meta-data for response body (payload & representation headers) */
struct resp_body_t {
    ulong len;                          /* Content-Length   */
    struct range *range;                /* Content-Range    */
    const char *fname;                  /* Content-Dispo    */
    unsigned char enc;                  /* Content-Encoding */
    const char *lang;                   /* Content-Language */
    const char *loc;                    /* Content-Location */
    const u_char *md5;                  /* Content-MD5      */
    const char *type;                   /* Content-Type     */
    const struct patch_doc_t *patch;    /* Accept-Patch     */
    unsigned prefs;                     /* Prefer           */
    const char *link;                   /* Link             */
    const char *lock;                   /* Lock-Token       */
    const char *etag;                   /* ETag             */
    time_t lastmod;                     /* Last-Modified    */
    time_t maxage;                      /* Expires          */
    const char *stag;                   /* Schedule-Tag     */
    const char *cmid;                   /* Cal-Managed-ID   */
    time_t iserial;                     /* iSched serial#   */
    struct buf payload;                 /* Payload          */
};

/* Transaction flags */
struct txn_flags_t {
    unsigned long ver1_0   : 1;         /* Request from HTTP/1.0 client */
    unsigned long conn     : 3;         /* Connection opts on req/resp */
    unsigned long override : 1;         /* HTTP method override */
    unsigned long cors     : 3;         /* Cross-Origin Resource Sharing */
    unsigned long mime     : 1;         /* MIME-conformant response */
    unsigned long te       : 3;         /* Transfer-Encoding for resp */
    unsigned long cc       : 7;         /* Cache-Control directives for resp */
    unsigned long ranges   : 1;         /* Accept range requests for resource */
    unsigned long vary     : 4;         /* Headers on which response varied */
    unsigned long trailer  : 1;         /* Headers which will be in trailer */
};

/* Transaction context */
struct transaction_t {
    unsigned meth;                      /* Index of Method to be performed */
    struct txn_flags_t flags;           /* Flags for this txn */
    struct request_line_t req_line;     /* Parsed request-line */
    xmlURIPtr req_uri;                  /* Parsed request-target URI */
    struct request_target_t req_tgt;    /* Parsed request-target path */
    hash_table req_qparams;             /* Parsed query params */
    hdrcache_t req_hdrs;                /* Cached HTTP headers */
    struct body_t req_body;             /* Buffered request body */
    struct auth_challenge_t auth_chal;  /* Authentication challenge */
    const char *location;               /* Location of resource */
    struct error_t error;               /* Error response meta-data */
    struct resp_body_t resp_body;       /* Response body meta-data */
#ifdef HAVE_ZLIB
    z_stream zstrm;                     /* Compression context */
    struct buf zbuf;                    /* Compression buffer */
#endif
    struct buf buf;                     /* Working buffer - currently used for:
                                           httpd:
                                             - telemetry of auth'd request
                                             - error desc string
                                             - Location hdr on redirects
                                             - Etag for static docs
                                           http_rss:
                                             - Content-Type for MIME parts
                                             - URL for feed & items
                                           http_caldav:
                                             - precond error resource URL
                                           http_ischedule:
                                             - error desc string
                                        */
};

/* Connection token flags */
enum {
    CONN_CLOSE =        (1<<0),
    CONN_UPGRADE =      (1<<1),
    CONN_KEEPALIVE =    (1<<2)
};

/* Cross-Origin Resource Sharing flags */
enum {
    CORS_NONE =         0,
    CORS_SIMPLE =       1,
    CORS_PREFLIGHT =    2
};

/* Content-Encoding flags (coding of representation) */
enum {
    CE_IDENTITY =       0,
    CE_DEFLATE =        (1<<0),
    CE_GZIP =           (1<<1)
};

/* Cache-Control directive flags */
enum {
    CC_REVALIDATE =     (1<<0),
    CC_NOCACHE =        (1<<1),
    CC_NOSTORE =        (1<<2),
    CC_NOTRANSFORM =    (1<<3),
    CC_PUBLIC =         (1<<4),
    CC_PRIVATE =        (1<<5),
    CC_MAXAGE =         (1<<6)
};

/* Vary header flags (headers used in selecting/producing representation) */
enum {
    VARY_ACCEPT =       (1<<0),
    VARY_AE =           (1<<1), /* Accept-Encoding */
    VARY_BRIEF =        (1<<2),
    VARY_PREFER =       (1<<3)
};

/* Trailer header flags */
enum {
    TRAILER_CMD5 =      (1<<0)  /* Content-MD5 */
};

typedef int (*premethod_proc_t)(struct transaction_t *txn);
typedef int (*method_proc_t)(struct transaction_t *txn, void *params);

struct method_t {
    method_proc_t proc;         /* Function to perform the method */
    void *params;               /* Parameters to pass to the method */
};

struct namespace_t {
    unsigned id;                /* Namespace identifier */
    unsigned enabled;           /* Is this namespace enabled? */
    const char *prefix;         /* Prefix of URL path denoting namespace */
    const char *well_known;     /* Any /.well-known/ URI */
    unsigned need_auth;         /* Do we need to auth for this namespace? */
    int mboxtype;               /* What mbtype can be seen in this namespace? */
    unsigned long allow;        /* Bitmask of allowed features/methods */
    void (*init)(struct buf *); /* Function run during service startup */
    void (*auth)(const char *); /* Function run after authentication */
    void (*reset)(void);        /* Function run before change in auth */
    void (*shutdown)(void);     /* Function run during service shutdown */
    int (*premethod)(struct transaction_t *); /* Func run prior to any method */
    struct method_t methods[];  /* Array of functions to perform HTTP methods.
                                 * MUST be an entry for EACH method listed,
                                 * and in the SAME ORDER in which they appear
                                 * in the http_methods[] array.
                                 * If the method is not supported,
                                 * the function pointer MUST be NULL.
                                 */
};

struct accept {
    char *token;
    float qual;
    struct accept *next;
};

extern struct namespace_t namespace_default;
extern struct namespace_t namespace_principal;
extern struct namespace_t namespace_notify;
extern struct namespace_t namespace_calendar;
extern struct namespace_t namespace_freebusy;
extern struct namespace_t namespace_addressbook;
extern struct namespace_t namespace_drive;
extern struct namespace_t namespace_ischedule;
extern struct namespace_t namespace_domainkey;
extern struct namespace_t namespace_tzdist;
extern struct namespace_t namespace_jmap;
extern struct namespace_t namespace_rss;
extern struct namespace_t namespace_dblookup;
extern struct namespace_t namespace_admin;
#ifdef ENABLE_APPLEPUSHSERVICE
extern struct namespace_t namespace_applepush;
#endif


/* XXX  These should be included in struct transaction_t */
extern struct buf serverinfo;
extern struct backend **backend_cached;
extern struct protstream *httpd_in;
extern struct protstream *httpd_out;
extern int https;
extern int httpd_tls_done;
extern int httpd_timeout;
extern int httpd_userisadmin;
extern int httpd_userisproxyadmin;
extern int httpd_userisanonymous;
extern char *httpd_userid;
extern char *httpd_extrafolder;
extern char *httpd_extradomain;
extern struct auth_state *httpd_authstate;
extern struct namespace httpd_namespace;
extern const char *httpd_localip, *httpd_remoteip;
extern unsigned long config_httpmodules;
extern int config_httpprettytelemetry;

extern int ignorequota;

extern xmlURIPtr parse_uri(unsigned meth, const char *uri, unsigned path_reqd,
                           const char **errstr);
extern struct accept *parse_accept(const char **hdr);
extern time_t calc_compile_time(const char *time, const char *date);
extern const char *http_statusline(long code);
extern char *rfc3339date_gen(char *buf, size_t len, time_t t);
extern char *httpdate_gen(char *buf, size_t len, time_t t);
extern void comma_list_hdr(const char *hdr, const char *vals[],
                           unsigned flags, ...);
extern void response_header(long code, struct transaction_t *txn);
extern void buf_printf_markup(struct buf *buf, unsigned level,
                              const char *fmt, ...);
extern void keepalive_response(void);
extern void error_response(long code, struct transaction_t *txn);
extern void html_response(long code, struct transaction_t *txn, xmlDocPtr html);
extern void xml_response(long code, struct transaction_t *txn, xmlDocPtr xml);
extern void write_body(long code, struct transaction_t *txn,
                       const char *buf, unsigned len);
extern void write_multipart_body(long code, struct transaction_t *txn,
                                 const char *buf, unsigned len);
extern int meth_options(struct transaction_t *txn, void *params);
extern int meth_trace(struct transaction_t *txn, void *params);
extern int etagcmp(const char *hdr, const char *etag);
extern int check_precond(struct transaction_t *txn,
                         const char *etag, time_t lastmod);

extern int httpd_myrights(struct auth_state *authstate, const char *acl);

extern void tzdist_truncate_vtimezone(icalcomponent *vtz,
                                      icaltimetype *startp, icaltimetype *endp);

#endif /* HTTPD_H */
