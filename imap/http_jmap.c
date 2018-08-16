/* http_jmap.c -- Routines for handling JMAP requests in httpd
 *
 * Copyright (c) 1994-2014 Carnegie Mellon University.  All rights reserved.
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

#include <config.h>

#include <sys/time.h>
#include <sys/resource.h>

#include <sasl/sasl.h>
#include <sasl/saslutil.h>

#ifdef HAVE_SSL
#include <openssl/hmac.h>
#include <openssl/rand.h>
#endif /* HAVE_SSL */

#include <errno.h>

#include "append.h"
#include "cyrusdb.h"
#include "hash.h"
#include "httpd.h"
#include "http_dav.h"
#include "http_proxy.h"
#include "http_ws.h"
#include "mboxname.h"
#include "msgrecord.h"
#include "proxy.h"
#include "times.h"
#include "syslog.h"
#include "xstrlcpy.h"
#include "vparse.h"
#include "vcard_support.h"

/* generated headers are not necessarily in current directory */
#include "imap/http_err.h"
#include "imap/imap_err.h"
#include "imap/jmap_err.h"

#include "http_jmap.h"

#define JMAP_ROOT          "/jmap"
#define JMAP_BASE_URL      JMAP_ROOT "/"
#define JMAP_UPLOAD_COL    "upload/"
#define JMAP_UPLOAD_TPL    "{accountId}/"
#define JMAP_DOWNLOAD_COL  "download/"
#define JMAP_DOWNLOAD_TPL  "{accountId}/{blobId}/{name}?accept={type}"

struct namespace jmap_namespace;

static time_t compile_time;

static json_t *jmap_capabilities = NULL;

/* HTTP method handlers */
static int jmap_get(struct transaction_t *txn, void *params);
static int jmap_post(struct transaction_t *txn, void *params);

/* Namespace callbacks */
static void jmap_init(struct buf *serverinfo);
static int  jmap_need_auth(struct transaction_t *txn);
static int  jmap_auth(const char *userid);

static int  jmap_settings(struct transaction_t *txn);
static int  jmap_initreq(jmap_req_t *req);
static void jmap_finireq(jmap_req_t *req);

static int jmap_core_echo(jmap_req_t *req);
static int jmap_blob_copy(jmap_req_t *req);

static int myrights(struct auth_state *authstate,
                    const mbentry_t *mbentry,
                    hash_table *mboxrights);

/* WebSocket handler */
#define JMAP_WS_PROTOCOL   "jmap"

static int jmap_ws(struct buf *inbuf, struct buf *outbuf,
                   struct buf *logbuf, void **rock);

static struct connect_params ws_params = {
    JMAP_BASE_URL, JMAP_WS_PROTOCOL, &jmap_ws
};

/* Namespace for JMAP */
struct namespace_t namespace_jmap = {
    URL_NS_JMAP, 0, "jmap", JMAP_ROOT, "/.well-known/jmap",
    jmap_need_auth, /*authschemes*/0,
    /*mbtype*/0, 
    (ALLOW_READ | ALLOW_POST),
    &jmap_init, &jmap_auth, NULL, NULL, NULL, /*bearer*/NULL,
    {
        { NULL,                 NULL },                 /* ACL          */
        { NULL,                 NULL },                 /* BIND         */
        { &meth_connect,        &ws_params },           /* CONNECT      */
        { NULL,                 NULL },                 /* COPY         */
        { NULL,                 NULL },                 /* DELETE       */
        { &jmap_get,            NULL },                 /* GET          */
        { &jmap_get,            NULL },                 /* HEAD         */
        { NULL,                 NULL },                 /* LOCK         */
        { NULL,                 NULL },                 /* MKCALENDAR   */
        { NULL,                 NULL },                 /* MKCOL        */
        { NULL,                 NULL },                 /* MOVE         */
        { &meth_options,        NULL },                 /* OPTIONS      */
        { NULL,                 NULL },                 /* PATCH        */
        { &jmap_post,           NULL },                 /* POST         */
        { NULL,                 NULL },                 /* PROPFIND     */
        { NULL,                 NULL },                 /* PROPPATCH    */
        { NULL,                 NULL },                 /* PUT          */
        { NULL,                 NULL },                 /* REPORT       */
        { &meth_trace,          NULL },                 /* TRACE        */
        { NULL,                 NULL },                 /* UNBIND       */
        { NULL,                 NULL }                  /* UNLOCK       */
    }
};


static int json_response(int code, struct transaction_t *txn, json_t *root)
{
    size_t flags = JSON_PRESERVE_ORDER;
    char *buf;

    /* Dump JSON object into a text buffer */
    flags |= (config_httpprettytelemetry ? JSON_INDENT(2) : JSON_COMPACT);
    buf = json_dumps(root, flags);
    json_decref(root);

    if (!buf) {
        txn->error.desc = "Error dumping JSON object";
        return HTTP_SERVER_ERROR;
    }

    /* Output the JSON object */
    switch (code) {
    case HTTP_OK:
    case HTTP_CREATED:
        txn->resp_body.type = "application/json; charset=utf-8";
        break;
    default:
        txn->resp_body.type = "application/problem+json; charset=utf-8";
        break;
    }

    write_body(code, txn, buf, strlen(buf));
    free(buf);

    return 0;
}

static int json_error_response(struct transaction_t *txn,
                               long code, json_t **res)
{
    long http_code = HTTP_BAD_REQUEST;
    const char *type, *title, *limit = NULL;

    /* Error string is encoded as type NUL title [ NUL limit ] */
    type = error_message(code);
    title = type + strlen(type) + 1;

    switch (code) {
    case JMAP_NOT_JSON:
    case JMAP_NOT_REQUEST:
    case JMAP_UNKNOWN_CAPABILITY:
        break;

    case JMAP_LIMIT_SIZE:
        http_code = HTTP_PAYLOAD_TOO_LARGE;

        GCC_FALLTHROUGH

    case JMAP_LIMIT_CALLS:
    case JMAP_LIMIT_OBJS_GET:
    case JMAP_LIMIT_OBJS_SET:
        limit = title + strlen(title) + 1;
        break;

    default:
        /* Actually an HTTP code, not a JMAP error code */
        return code;
    }

    *res = json_pack("{s:s s:s s:i}", "type", type, "title", title,
                     "status", atoi(error_message(http_code)));
    if (!*res) {
        txn->error.desc = "Unable to create JSON response";
        return HTTP_SERVER_ERROR;
    }

    if (limit) {
        json_object_set_new(*res, "limit", json_string(limit));
    }

    if (txn->error.desc) {
        json_object_set_new(*res, "detail", json_string(txn->error.desc));
    }

    return 0;
}


enum {
    JMAP_ENDPOINT_API,
    JMAP_ENDPOINT_UPLOAD,
    JMAP_ENDPOINT_DOWNLOAD
};

static int jmap_parse_path(struct transaction_t *txn)
{
    struct request_target_t *tgt = &txn->req_tgt;
    size_t len;
    char *p;

    if (*tgt->path) return 0;  /* Already parsed */

    /* Make a working copy of target path */
    strlcpy(tgt->path, txn->req_uri->path, sizeof(tgt->path));
    p = tgt->path;

    /* Sanity check namespace */
    len = strlen(namespace_jmap.prefix);
    if (strlen(p) < len ||
        strncmp(namespace_jmap.prefix, p, len) ||
        (tgt->path[len] && tgt->path[len] != '/')) {
        txn->error.desc = "Namespace mismatch request target path";
        return HTTP_FORBIDDEN;
    }

    /* Skip namespace */
    p += len;
    if (!*p) {
        /* Canonicalize URL */
        txn->location = JMAP_BASE_URL;
        return HTTP_MOVED;
    }

    /* Check for path after prefix */
    if (*++p) {
        /* Get "collection" */
        tgt->collection = p;

        if (!strncmp(tgt->collection, JMAP_UPLOAD_COL,
                          strlen(JMAP_UPLOAD_COL))) {
            tgt->flags = JMAP_ENDPOINT_UPLOAD;
            tgt->allow = ALLOW_POST;

            /* Get "resource" which must be the accountId */
            tgt->resource = tgt->collection + strlen(JMAP_UPLOAD_COL);
        }
        else if (!strncmp(tgt->collection,
                          JMAP_DOWNLOAD_COL, strlen(JMAP_DOWNLOAD_COL))) {
            tgt->flags = JMAP_ENDPOINT_DOWNLOAD;
            tgt->allow = ALLOW_READ;

            /* Get "resource" */
            tgt->resource = tgt->collection + strlen(JMAP_DOWNLOAD_COL);
        }
        else {
            return HTTP_NOT_ALLOWED;
        }
    }
    else {
        tgt->flags = JMAP_ENDPOINT_API;
        tgt->allow = ALLOW_POST|ALLOW_READ;
    }

    return 0;
}

static hash_table jmap_methods = HASH_TABLE_INITIALIZER;

static jmap_method_t *find_methodproc(const char *name)
{
    return hash_lookup(name, &jmap_methods);
}

struct mymblist_rock {
    mboxlist_cb *proc;
    void *rock;
    struct auth_state *authstate;
    hash_table *mboxrights;
    int all;
};

static int mymblist_cb(const mbentry_t *mbentry, void *rock)
{
    struct mymblist_rock *myrock = rock;

    if (!myrock->all) {
        if (mbentry->mbtype & MBTYPE_DELETED)
            return 0;

        int rights = myrights(myrock->authstate, mbentry, myrock->mboxrights);
        if (!(rights & ACL_LOOKUP))
            return 0;
    }
    return myrock->proc(mbentry, myrock->rock);
}

static int mymblist(const char *userid,
                    const char *accountid,
                    struct auth_state *authstate,
                    hash_table *mboxrights,
                    mboxlist_cb *proc,
                    void *rock,
                    int all)
{
    int flags = all ? (MBOXTREE_TOMBSTONES|MBOXTREE_DELETED) : 0;

    /* skip ACL checks if account owner */
    if (!strcmp(userid, accountid))
        return mboxlist_usermboxtree(userid, authstate, proc, rock, flags);

    /* Open the INBOX first */
    struct mymblist_rock myrock = { proc, rock, authstate, mboxrights, all };
    return mboxlist_usermboxtree(accountid, authstate, mymblist_cb, &myrock, flags);
}

EXPORTED int jmap_mboxlist(jmap_req_t *req, mboxlist_cb *proc, void *rock)
{
    return mymblist(req->userid, req->accountid, req->authstate,
                    req->mboxrights, proc, rock, 0/*all*/);
}

static long jmap_max_size_upload = 0;
static long jmap_max_concurrent_upload = 0;
static long jmap_max_size_request = 0;
static long jmap_max_concurrent_requests = 0;
static long jmap_max_calls_in_request = 0;
static long jmap_max_objects_in_get = 0;
static long jmap_max_objects_in_set = 0;

static void jmap_init(struct buf *serverinfo __attribute__((unused)))
{
    namespace_jmap.enabled =
        config_httpmodules & IMAP_ENUM_HTTPMODULES_JMAP;

    if (!namespace_jmap.enabled) return;

    compile_time = calc_compile_time(__TIME__, __DATE__);

    initialize_JMAP_error_table();

#define _read_opt(val, optkey) \
    val = config_getint(optkey); \
    if (val <= 0) { \
        syslog(LOG_ERR, "jmap: invalid property value: %s", \
                imapopts[optkey].optname); \
        val = 0; \
    }
    _read_opt(jmap_max_size_upload, IMAPOPT_JMAP_MAX_SIZE_UPLOAD);
    jmap_max_size_upload *= 1024;
    _read_opt(jmap_max_concurrent_upload, IMAPOPT_JMAP_MAX_CONCURRENT_UPLOAD);
    _read_opt(jmap_max_size_request, IMAPOPT_JMAP_MAX_SIZE_REQUEST);
    jmap_max_size_request *= 1024;
    _read_opt(jmap_max_concurrent_requests, IMAPOPT_JMAP_MAX_CONCURRENT_REQUESTS);
    _read_opt(jmap_max_calls_in_request, IMAPOPT_JMAP_MAX_CALLS_IN_REQUEST);
    _read_opt(jmap_max_objects_in_get, IMAPOPT_JMAP_MAX_OBJECTS_IN_GET);
    _read_opt(jmap_max_objects_in_set, IMAPOPT_JMAP_MAX_OBJECTS_IN_SET);
#undef _read_opt

    jmap_capabilities = json_pack("{s:{s:i s:i s:i s:i s:i s:i s:i s:o}}",
        JMAP_URN_CORE,
        "maxSizeUpload", jmap_max_size_upload,
        "maxConcurrentUpload", jmap_max_concurrent_upload,
        "maxSizeRequest", jmap_max_size_request,
        "maxConcurrentRequests", jmap_max_concurrent_requests,
        "maxCallsInRequest",jmap_max_calls_in_request,
        "maxObjectsInGet", jmap_max_objects_in_get,
        "maxObjectsInSet", jmap_max_objects_in_set,
        "collationAlgorithms", json_array()
    );

    if (ws_enabled()) {
        json_object_set_new(jmap_capabilities, JMAP_URN_WEBSOCKET,
                            json_pack("{s:s}", "wsUrl", JMAP_BASE_URL));
    }

    construct_hash_table(&jmap_methods, 128, 0);

    jmap_mail_init(&jmap_methods, jmap_capabilities);
    jmap_contact_init(&jmap_methods, jmap_capabilities);
    jmap_calendar_init(&jmap_methods, jmap_capabilities);

    json_object_set_new(jmap_capabilities,
                        XML_NS_CYRUS "performance", json_object());

    static jmap_method_t coreecho = { "Core/echo", &jmap_core_echo };
    hash_insert(coreecho.name, &coreecho, &jmap_methods);

    static jmap_method_t blobcopy = { "Blob/copy", &jmap_blob_copy };
    hash_insert(blobcopy.name, &blobcopy, &jmap_methods);
}


static int jmap_auth(const char *userid __attribute__((unused)))
{
    /* Set namespace */
    mboxname_init_namespace(&jmap_namespace,
                            httpd_userisadmin || httpd_userisproxyadmin);
    return 0;
}

/* Perform a GET/HEAD request */
static int jmap_get(struct transaction_t *txn,
                    void *params __attribute__((unused)))
{
    int r = jmap_parse_path(txn);

    if (r || !(txn->req_tgt.allow & ALLOW_READ)) {
        return HTTP_NOT_FOUND;
    }

    if (txn->req_tgt.flags == JMAP_ENDPOINT_API) {
        /* Upgrade to WebSockets over HTTP/1.1 on API endpoint, if requested */
        if (txn->flags.upgrade & UPGRADE_WS) {
            return ws_start_channel(txn, JMAP_WS_PROTOCOL, &jmap_ws);
        }

        return jmap_settings(txn);
    }

    return jmap_download(txn);
}

static int is_accessible(const mbentry_t *mbentry,
                         void *rock __attribute__((unused)))
{
    if ((mbentry->mbtype & MBTYPE_DELETED) ||
        (mbentry->mbtype & MBTYPE_MOVING) ||
        (mbentry->mbtype & MBTYPE_REMOTE) ||
        (mbentry->mbtype & MBTYPE_RESERVE)) {
        return 0;
    }
    return IMAP_OK_COMPLETED;
}

static json_t *extract_value(json_t *from, const char *path, ptrarray_t *refs);

static json_t *extract_array_value(json_t *val, const char *idx,
                                   const char *path, ptrarray_t *pool)
{
    if (!strcmp(idx, "*")) {
        /* Build value from array traversal */
        json_t *newval = json_pack("[]");
        size_t i;
        json_t *v;
        json_array_foreach(val, i, v) {
            json_t *x = extract_value(v, path, pool);
            if (json_is_array(x)) {
                /* JMAP spec: "If the result of applying the rest
                 * of the pointer tokens to a value was itself an
                 * array, its items should be included individually
                 * in the output rather than including the array
                 * itself." */
                json_array_extend(newval, x);
            } else if (x) {
                json_array_append(newval, x);
            } else {
                json_decref(newval);
                newval = NULL;
            }
        }
        if (newval) {
            ptrarray_add(pool, newval);
        }
        return newval;
    }

    /* Lookup array value by index */
    const char *eot = NULL;
    bit64 num;
    if (parsenum(idx, &eot, 0, &num) || *eot) {
        return NULL;
    }
    val = json_array_get(val, num);
    if (!val) {
        return NULL;
    }
    return extract_value(val, path, pool);
}

/* Extract the JSON value at position path from val.
 *
 * Return NULL, if the the value does not exist or if
 * path is erroneous.
 */
static json_t *extract_value(json_t *val, const char *path, ptrarray_t *pool)
{
    /* Return value for empty path */
    if (*path == '\0') {
        return val;
    }

    /* Be lenient: root path '/' is optional */
    if (*path == '/') {
        path++;
    }

    /* Walk over path segments */
    while (val && *path) {
        const char *top = NULL;
        char *p = NULL;

        /* Extract next path segment */
        if (!(top = strchr(path, '/'))) {
            top = strchr(path, '\0');
        }
        p = json_pointer_decode(path, top - path);
        if (*p == '\0') {
            return NULL;
        }

        /* Extract array value */
        if (json_is_array(val)) {
            val = extract_array_value(val, p, top, pool);
            free(p);
            return val;
        }

        /* Value MUST be an object now */
        if (!json_is_object(val)) {
            free(p);
            return NULL;
        }
        /* Step down into object tree */
        val = json_object_get(val, p);
        free(p);
        path = *top ? top + 1 : top;
    }

    return val;
}

static int process_resultrefs(json_t *args, json_t *resp)
{
    json_t *ref;
    const char *arg;
    int ret = -1;

    void *tmp;
    json_object_foreach_safe(args, tmp, arg, ref) {
        if (*arg != '#' || *(arg+1) == '\0') {
            continue;
        }

        const char *of, *path, *name;
        json_t *res = NULL;

        /* Parse result reference object */
        of = json_string_value(json_object_get(ref, "resultOf"));
        if (!of || *of == '\0') {
            goto fail;
        }
        path = json_string_value(json_object_get(ref, "path"));
        if (!path || *path == '\0') {
            goto fail;
        }
        name = json_string_value(json_object_get(ref, "name"));
        if (!name || *name == '\0') {
            goto fail;
        }

        /* Lookup referenced response */
        json_t *v;
        size_t i;
        json_array_foreach(resp, i, v) {
            const char *tag = json_string_value(json_array_get(v, 2));
            if (!tag || strcmp(tag, of)) {
                continue;
            }
            const char *mname = json_string_value(json_array_get(v, 0));
            if (!mname || strcmp(name, mname)) {
                goto fail;
            }
            res = v;
            break;
        }
        if (!res) goto fail;

        /* Extract the reference argument value. */
        /* We maintain our own pool of newly created JSON objects, since
         * tracking reference counts across newly created JSON arrays is
         * a pain. Rule: If you incref an existing JSON value or create
         * an entirely new one, put it into the pool for cleanup. */
        ptrarray_t pool = PTRARRAY_INITIALIZER;
        json_t *val = extract_value(json_array_get(res, 1), path, &pool);
        if (!val) goto fail;

        /* Replace both key and value of the reference entry */
        json_object_set(args, arg + 1, val);
        json_object_del(args, arg);

        /* Clean up reference counts of pooled JSON objects */
        json_t *ref;
        while ((ref = ptrarray_pop(&pool))) {
            json_decref(ref);
        }
        ptrarray_fini(&pool);
    }

    return 0;

fail:
    return ret;
}

static int parse_json_body(struct transaction_t *txn, json_t **req)
{
    const char **hdr;
    json_error_t jerr;
    int ret;

    /* Check Content-Type */
    if (!(hdr = spool_getheader(txn->req_hdrs, "Content-Type")) ||
        !is_mediatype("application/json", hdr[0])) {
        txn->error.desc = "This method requires a JSON request body";
        return HTTP_BAD_MEDIATYPE;
    }

    /* Read body */
    txn->req_body.flags |= BODY_DECODE;
    ret = http_read_req_body(txn);
    if (ret) {
        txn->flags.conn = CONN_CLOSE;
        return ret;
    }

    /* Parse the JSON request */
    *req = json_loads(buf_cstring(&txn->req_body.payload), 0, &jerr);
    if (!*req) {
        buf_reset(&txn->buf);
        buf_printf(&txn->buf,
                   "Unable to parse JSON request body: %s", jerr.text);
        txn->error.desc = buf_cstring(&txn->buf);
        return JMAP_NOT_JSON;
    }

    return 0;
}

static int validate_request(struct transaction_t *txn, json_t *req, int *do_perf)
{
    json_t *using = json_object_get(req, "using");
    json_t *calls = json_object_get(req, "methodCalls");

    if (!json_is_array(using) || !json_is_array(calls)) {
        return JMAP_NOT_REQUEST;
    }

    /*
     * XXX the following maximums are not enforced:
     * maxConcurrentUpload
     * maxConcurrentRequests
     */

    if (buf_len(&txn->req_body.payload) > (size_t) jmap_max_size_request) {
        return JMAP_LIMIT_SIZE;
    }

    size_t i;
    json_t *val;
    json_array_foreach(calls, i, val) {
        if (json_array_size(val) != 3 ||
                !json_is_string(json_array_get(val, 0)) ||
                !json_is_object(json_array_get(val, 1)) ||
                !json_is_string(json_array_get(val, 2))) {
            return JMAP_NOT_REQUEST;
        }
        if (i >= (size_t) jmap_max_calls_in_request) {
            return JMAP_LIMIT_CALLS;
        }
        const char *mname = json_string_value(json_array_get(val, 0));
        mname = strchr(mname, '/');
        if (!mname) continue;

        if (!strcmp(mname, "get")) {
            json_t *ids = json_object_get(json_array_get(val, 1), "ids");
            if (json_array_size(ids) > (size_t) jmap_max_objects_in_get) {
                return JMAP_LIMIT_OBJS_GET;
            }
        }
        else if (!strcmp(mname, "set")) {
            json_t *args = json_array_get(val, 1);
            size_t size = json_object_size(json_object_get(args, "create"));
            size += json_object_size(json_object_get(args, "update"));
            size += json_array_size(json_object_get(args, "destroy"));
            if (size > (size_t) jmap_max_objects_in_set) {
                return JMAP_LIMIT_OBJS_SET;
            }
        }
    }

    json_array_foreach(using, i, val) {
        const char *s = json_string_value(val);
        if (!s) {
            return JMAP_NOT_REQUEST;
        }
        if (!strcmp(s, XML_NS_CYRUS "performance")) {
            *do_perf = 1;
        }
        else if (!strcmp(s, "ietf:jmap")) {
            syslog(LOG_DEBUG, "old capability %s used", s);
        }
        else if (!strcmp(s, "ietf:jmapmail")) {
            syslog(LOG_DEBUG, "old capability %s used", s);
        }
        else if (!json_object_get(jmap_capabilities, s)) {
            return JMAP_UNKNOWN_CAPABILITY;
        }
    }

    return 0;
}

EXPORTED int jmap_is_valid_id(const char *id)
{
    if (!id || *id == '\0') return 0;
    const char *p;
    for (p = id; *p; p++) {
        if (('0' <= *p && *p <= '9'))
            continue;
        if (('a' <= *p && *p <= 'z') || ('A' <= *p && *p <= 'Z'))
            continue;
        if ((*p == '-') || (*p == '_'))
            continue;
        return 0;
    }
    return 1;
}

static void _make_created_ids(const char *creation_id, void *val, void *rock)
{
    json_t *jcreatedIds = rock;
    const char *id = val;
    json_object_set_new(jcreatedIds, creation_id, json_string(id));
}

/* Perform an API request */
static int jmap_api(struct transaction_t *txn, json_t **res)
{
    json_t *jreq = NULL, *resp = NULL;
    size_t i;
    int ret, do_perf = 0;
    char *inboxname = NULL;
    hash_table *client_creation_ids = NULL;
    hash_table *new_creation_ids = NULL;
    hash_table accounts = HASH_TABLE_INITIALIZER;
    hash_table mboxrights = HASH_TABLE_INITIALIZER;
    strarray_t methods = STRARRAY_INITIALIZER;

    ret = parse_json_body(txn, &jreq);
    if (ret) return json_error_response(txn, ret, res);

    /* Validate Request object */
    if ((ret = validate_request(txn, jreq, &do_perf))) {
        return json_error_response(txn, ret, res);
    }

    /* Start JSON response */
    resp = json_array();
    if (!resp) {
        txn->error.desc = "Unable to create JSON response body";
        ret = HTTP_SERVER_ERROR;
        goto done;
    }

    /* Set up request-internal state */
    construct_hash_table(&accounts, 8, 0);
    construct_hash_table(&mboxrights, 64, 0);

    /* Set up creation ids */
    long max_creation_ids =
        (jmap_max_calls_in_request + 1) * jmap_max_objects_in_set;
    new_creation_ids = xzmalloc(sizeof(hash_table));
    construct_hash_table(new_creation_ids, max_creation_ids, 0);

    /* Parse client-supplied creation ids */
    json_t *jcreatedIds = json_object_get(jreq, "createdIds");
    if (json_is_object(jcreatedIds)) {
        client_creation_ids = xzmalloc(sizeof(hash_table));
        construct_hash_table(client_creation_ids, json_object_size(jcreatedIds)+1, 0);
        const char *creation_id;
        json_t *jval;
        json_object_foreach(jcreatedIds, creation_id, jval) {
            if (!json_is_string(jval)) {
                txn->error.desc = "Invalid createdIds argument";
                ret = HTTP_BAD_REQUEST;
                goto done;
            }
            const char *id = json_string_value(jval);
            if (!jmap_is_valid_id(creation_id) || !jmap_is_valid_id(id)) {
                txn->error.desc = "Invalid createdIds argument";
                ret = HTTP_BAD_REQUEST;
                goto done;
            }
            hash_insert(creation_id, xstrdup(id), client_creation_ids);
        }
    }
    else if (jcreatedIds && jcreatedIds != json_null()) {
        txn->error.desc = "Invalid createdIds argument";
        ret = HTTP_BAD_REQUEST;
        goto done;
    }

    /* Process each method call in the request */
    json_t *mc;
    json_array_foreach(json_object_get(jreq, "methodCalls"), i, mc) {
        const jmap_method_t *mp;
        const char *mname = json_string_value(json_array_get(mc, 0));
        json_t *args = json_array_get(mc, 1), *arg;
        const char *tag = json_string_value(json_array_get(mc, 2));
        int r = 0;

        strarray_append(&methods, mname);

        /* Find the message processor */
        if (!(mp = find_methodproc(mname))) {
            json_array_append(resp, json_pack("[s {s:s} s]",
                        "error", "type", "unknownMethod", tag));
            continue;
        }

        /* Determine account */
        const char *accountid = httpd_userid;
        arg = json_object_get(args, "accountId");
        if (arg && arg != json_null()) {
            if ((accountid = json_string_value(arg)) == NULL) {
                json_t *err = json_pack("{s:s, s:[s]}",
                        "type", "invalidArguments", "arguments", "accountId");
                json_array_append(resp, json_pack("[s,o,s]", "error", err, tag));
                continue;
            }
            /* Check if any shared mailbox is accessible */
            if (!hash_lookup(accountid, &accounts)) {
                r = mymblist(httpd_userid, accountid, httpd_authstate,
                             &mboxrights, is_accessible, NULL, 0/*all*/);
                if (r != IMAP_OK_COMPLETED) {
                    json_t *err = json_pack("{s:s}", "type", "accountNotFound");
                    json_array_append_new(resp,
                                          json_pack("[s,o,s]", "error", err, tag));
                    continue;
                }
                hash_insert(accountid, (void*)1, &accounts);
            }
        }
        free(inboxname);
        inboxname = mboxname_user_mbox(accountid, NULL);

        /* Pre-process result references */
        if (process_resultrefs(args, resp)) {
            json_array_append_new(resp, json_pack("[s,{s:s},s]",
                        "error", "type", "resultReference", tag));
            continue;
        }

        struct conversations_state *cstate = NULL;
        r = conversations_open_user(accountid, &cstate);
        if (r) {
            txn->error.desc = error_message(r);
            ret = HTTP_SERVER_ERROR;
            goto done;
        }

        struct jmap_req req;
        memset(&req, 0, sizeof(struct jmap_req));
        req.method = mname;
        req.userid = httpd_userid;
        req.accountid = accountid;
        req.inboxname = inboxname;
        req.cstate = cstate;
        req.authstate = httpd_authstate;
        req.args = args;
        req.response = resp;
        req.tag = tag;
        req.client_creation_ids = client_creation_ids;
        req.new_creation_ids = new_creation_ids;
        req.txn = txn;
        req.mboxrights = &mboxrights;
        req.force_openmbox_rw = 0;

        if (do_perf) {
            struct rusage usage;

            getrusage(RUSAGE_SELF, &usage);
            req.user_start = timeval_get_double(&usage.ru_utime);
            req.sys_start = timeval_get_double(&usage.ru_stime);
            req.real_start = now_ms() / 1000.0;
            req.do_perf = 1;
        }

        /* Initialize request context */
        jmap_initreq(&req);

        /* Read the current state data in */
        r = mboxname_read_counters(inboxname, &req.counters);
        if (r) goto done;

        /* Call the message processor. */
        r = mp->proc(&req);

        /* Finalize request context */
        jmap_finireq(&req);

        if (r) {
            conversations_abort(&req.cstate);
            txn->error.desc = error_message(r);
            ret = HTTP_SERVER_ERROR;
            goto done;
        }
        conversations_commit(&req.cstate);
    }

    /* tell syslog which methods were called */
    spool_replace_header(xstrdup(":jmap"),
                         strarray_join(&methods, ","), txn->req_hdrs);


    /* Build responses */
    *res = json_pack("{s:O}", "methodResponses", resp);
    if (client_creation_ids) {
        json_t *jcreatedIds = json_object();
        hash_enumerate(new_creation_ids, _make_created_ids, jcreatedIds);
        json_object_set_new(*res, "createdIds", jcreatedIds);
    }

  done:
    free_hash_table(client_creation_ids, free);
    free(client_creation_ids);
    free_hash_table(new_creation_ids, free);
    free(new_creation_ids);
    free_hash_table(&accounts, NULL);
    free_hash_table(&mboxrights, free);
    free(inboxname);
    json_decref(jreq);
    json_decref(resp);
    strarray_fini(&methods);

    return ret;
}

/* Perform a POST request */
static int jmap_post(struct transaction_t *txn,
                     void *params __attribute__((unused)))
{
    int ret;
    json_t *res = NULL;

    ret = jmap_parse_path(txn);

    if (ret) return ret;
    if (!(txn->req_tgt.allow & ALLOW_POST)) {
        return HTTP_NOT_ALLOWED;
    }

    /* Handle uploads */
    if (txn->req_tgt.flags == JMAP_ENDPOINT_UPLOAD) {
        return jmap_upload(txn);
    }

    /* Regular JMAP API request */
    ret = jmap_api(txn, &res);

    if (!ret) {
        /* Output the JSON object */
        ret = json_response(HTTP_OK, txn, res);
    }

    syslog(LOG_DEBUG, ">>>> jmap_post: Exit\n");
    return ret;
}

const char *jmap_lookup_id(jmap_req_t *req, const char *creation_id)
{
    if (req->client_creation_ids) {
        const char *id = hash_lookup(creation_id, req->client_creation_ids);
        if (id) return id;
    }
    if (!req->new_creation_ids)
        return NULL;
    return hash_lookup(creation_id, req->new_creation_ids);
}

void jmap_add_id(jmap_req_t *req, const char *creation_id, const char *id)
{
    /* It's OK to overwrite existing ids, as per Foo/set:
     * "A client SHOULD NOT reuse a creation id anywhere in the same API
     * request. If a creation id is reused, the server MUST map the creation
     * id to the most recently created item with that id."
     */
    if (!req->new_creation_ids) {
        req->new_creation_ids = xzmalloc(sizeof(hash_table));
        construct_hash_table(req->new_creation_ids, 128, 0);
    }
    hash_insert(creation_id, xstrdup(id), req->new_creation_ids);
}

/*
 * WebSockets data callback ('jmap' sub-protocol): Process JMAP API request.
 *
 * Can be tested with:
 *   https://github.com/websockets/wscat
 *   https://chrome.google.com/webstore/detail/web-socket-client/lifhekgaodigcpmnakfhaaaboididbdn
 *
 * WebSockets over HTTP/2 currently only available in:
 *   https://www.google.com/chrome/browser/canary.html
 */
static int jmap_ws(struct buf *inbuf, struct buf *outbuf,
                   struct buf *logbuf, void **rock)
{
    struct transaction_t **txnp = (struct transaction_t **) rock;
    struct transaction_t *txn = *txnp;
    json_t *res = NULL;
    int ret;

    if (!txn) {
        /* Create a transaction rock to use for API requests */
        txn = *txnp = xzmalloc(sizeof(struct transaction_t));
        txn->req_body.flags = BODY_DONE;

        /* Create header cache */
        txn->req_hdrs = spool_new_hdrcache();
        if (!txn->req_hdrs) {
            free(txn);
            return HTTP_SERVER_ERROR;
        }

        /* Set Content-Type of request payload */
        spool_cache_header(xstrdup("Content-Type"),
                           xstrdup("application/json"), txn->req_hdrs);
    }
    else if (!inbuf) {
        /* Free transaction rock */
        transaction_free(txn);
        free(txn);
        return 0;
    }

    /* Set request payload */
    buf_init_ro(&txn->req_body.payload, buf_base(inbuf), buf_len(inbuf));

    /* Process the API request */
    ret = jmap_api(txn, &res);

    /* Free request payload */
    buf_free(&txn->req_body.payload);

    if (logbuf) {
        /* Log JMAP methods */
        const char **hdr = spool_getheader(txn->req_hdrs, ":jmap");

        if (hdr) buf_printf(logbuf, "; jmap=%s", hdr[0]);
    }

    if (!ret) {
        /* Return the JSON object */
        size_t flags = JSON_PRESERVE_ORDER;
        char *buf;

        /* Dump JSON object into a text buffer */
        flags |= (config_httpprettytelemetry ? JSON_INDENT(2) : JSON_COMPACT);
        buf = json_dumps(res, flags);
        json_decref(res);

        buf_initm(outbuf, buf, strlen(buf));
    }

    return ret;
}

struct _mboxcache_rec {
    struct mailbox *mbox;
    int refcount;
    int rw;
};

static int jmap_initreq(jmap_req_t *req)
{
    req->mboxes = ptrarray_new();
    return 0;
}

static void jmap_finireq(jmap_req_t *req)
{
    int i;

    for (i = 0; i < req->mboxes->count; i++) {
        struct _mboxcache_rec *rec = ptrarray_nth(req->mboxes, i);
        if (rec->refcount)
            syslog(LOG_ERR, "DBERROR jmap: force-closing mailbox %s (refcount=%d)",
                            rec->mbox->name, rec->refcount);
        mailbox_close(&rec->mbox);
        free(rec);
    }
    ptrarray_free(req->mboxes);
    req->mboxes = NULL;
}

EXPORTED int jmap_openmbox(jmap_req_t *req, const char *name,
                           struct mailbox **mboxp, int rw)
{
    int i, r;
    struct _mboxcache_rec *rec;

    for (i = 0; i < req->mboxes->count; i++) {
        rec = (struct _mboxcache_rec*) ptrarray_nth(req->mboxes, i);
        if (!strcmp(name, rec->mbox->name)) {
            if (rw && !rec->rw) {
                /* Lock promotions are not supported */
                syslog(LOG_ERR, "jmapmbox: failed to grab write-lock on cached read-only mailbox %s", name);
                return IMAP_INTERNAL;
            }
            /* Found a cached mailbox. Increment refcount. */
            rec->refcount++;
            *mboxp = rec->mbox;

            return 0;
        }
    }

    /* Add mailbox to cache */
    if (req->force_openmbox_rw)
        rw = 1;
    r = rw ? mailbox_open_iwl(name, mboxp) : mailbox_open_irl(name, mboxp);
    if (r) {
        syslog(LOG_ERR, "jmap_openmbox(%s): %s", name, error_message(r));
        return r;
    }
    rec = xzmalloc(sizeof(struct _mboxcache_rec));
    rec->mbox = *mboxp;
    rec->refcount = 1;
    rec->rw = rw;
    ptrarray_add(req->mboxes, rec);

    return 0;
}

EXPORTED int jmap_isopenmbox(jmap_req_t *req, const char *name)
{

    int i;
    struct _mboxcache_rec *rec;

    for (i = 0; i < req->mboxes->count; i++) {
        rec = (struct _mboxcache_rec*) ptrarray_nth(req->mboxes, i);
        if (!strcmp(name, rec->mbox->name))
            return 1;
    }

    return 0;
}

EXPORTED void jmap_closembox(jmap_req_t *req, struct mailbox **mboxp)
{
    struct _mboxcache_rec *rec = NULL;
    int i;

    if (mboxp == NULL || *mboxp == NULL) return;

    for (i = 0; i < req->mboxes->count; i++) {
        rec = (struct _mboxcache_rec*) ptrarray_nth(req->mboxes, i);
        if (rec->mbox == *mboxp) {
            --rec->refcount;
            assert(rec->refcount >= 0);
            *mboxp = NULL;
            return;
        }
    }
    syslog(LOG_INFO, "jmap: ignoring non-cached mailbox %s", (*mboxp)->name);
    // XXX - assert and die here?
}

EXPORTED char *jmap_blobid(const struct message_guid *guid)
{
    char *blobid = xzmalloc(42);
    blobid[0] = 'G';
    memcpy(blobid+1, message_guid_encode(guid), 40);
    return blobid;
}


struct findblob_data {
    jmap_req_t *req;
    const char *accountid;
    int is_shared_account;
    struct mailbox *mbox;
    msgrecord_t *mr;
    char *part_id;
};

static int findblob_cb(const conv_guidrec_t *rec, void *rock)
{
    struct findblob_data *d = (struct findblob_data*) rock;
    jmap_req_t *req = d->req;
    int r = 0;

    /* Ignore blobs that don't belong to the current accountId */
    mbname_t *mbname = mbname_from_intname(rec->mboxname);
    int is_accountid_mbox =
        (mbname && !strcmp(mbname_userid(mbname), d->accountid));
    mbname_free(&mbname);
    if (!is_accountid_mbox)
        return 0;

    /* Check ACL */
    if (d->is_shared_account) {
        mbentry_t *mbentry = NULL;
        r = mboxlist_lookup(rec->mboxname, &mbentry, NULL);
        if (r) {
            syslog(LOG_ERR, "jmap_findblob: no mbentry for %s", rec->mboxname);
            return r;
        }
        int rights = jmap_myrights(req, mbentry);
        mboxlist_entry_free(&mbentry);
        if ((rights & (ACL_LOOKUP|ACL_READ)) != (ACL_LOOKUP|ACL_READ)) {
            return 0;
        }
    }

    r = jmap_openmbox(req, rec->mboxname, &d->mbox, 0);
    if (r) return r;

    r = msgrecord_find(d->mbox, rec->uid, &d->mr);
    if (r) {
        jmap_closembox(req, &d->mbox);
        d->mr = NULL;
        return r;
    }

    d->part_id = rec->part ? xstrdup(rec->part) : NULL;
    return IMAP_OK_COMPLETED;
}

static int _findblob(jmap_req_t *req, const char *blobid,
                     const char *accountid,
                     struct mailbox **mbox, msgrecord_t **mr,
                     struct body **body, const struct body **part,
                     struct buf *blob)
{

    struct findblob_data data = {
        req, /* req */
        accountid, /* accountid */
        strcmp(req->userid, accountid), /* is_shared_account */
        NULL, /* mbox */
        NULL, /* mr */
        NULL  /* part_id */
    };
    struct body *mybody = NULL;
    const struct body *mypart = NULL;
    int i, r;

    if (blobid[0] != 'G')
        return IMAP_NOTFOUND;

    r = conversations_guid_foreach(req->cstate, blobid+1, findblob_cb, &data);
    if (r != IMAP_OK_COMPLETED) {
        if (!r) r = IMAP_NOTFOUND;
        goto done;
    }

    r = msgrecord_get_bodystructure(data.mr, &mybody);
    if (r) goto done;

    /* Find part containing the data */
    if (data.part_id) {
        ptrarray_t parts = PTRARRAY_INITIALIZER;
        struct message_guid content_guid;

        message_guid_decode(&content_guid, blobid+1);

        ptrarray_push(&parts, mybody);
        while ((mypart = ptrarray_shift(&parts))) {
            if (!message_guid_cmp(&content_guid, &mypart->content_guid)) {
                break;
            }
            if (!mypart->subpart) {
                if (data.mbox->mbtype == MBTYPE_ADDRESSBOOK &&
                    (mypart = jmap_contact_findblob(&content_guid, data.part_id,
                                                    data.mbox, data.mr, blob))) {
                    break;
                }
                continue;
            }
            ptrarray_push(&parts, mypart->subpart);
            for (i = 1; i < mypart->numparts; i++)
                ptrarray_push(&parts, mypart->subpart + i);
        }
        ptrarray_fini(&parts);

        if (!mypart) {
            r = IMAP_NOTFOUND;
            goto done;
        }
    }

    *mbox = data.mbox;
    *mr = data.mr;
    *part = mypart;
    *body = mybody;
    r = 0;

done:
    if (r) {
        if (data.mbox) jmap_closembox(req, &data.mbox);
        if (mybody) message_free_body(mybody);
    }
    if (data.part_id) free(data.part_id);
    return r;
}


EXPORTED int jmap_findblob(jmap_req_t *req, const char *blobid,
                           struct mailbox **mbox, msgrecord_t **mr,
                           struct body **body, const struct body **part,
                           struct buf *blob)
{
    return _findblob(req, blobid, req->accountid, mbox, mr, body, part, blob);
}

static char *parse_accept_header(const char **hdr)
{
    char *val = NULL;
    struct accept *accept = parse_accept(hdr);
    if (accept) {
        char *type = NULL;
        char *subtype = NULL;
        struct param *params = NULL;
        message_parse_type(accept->token, &type, &subtype, &params);
        if (type && subtype && !strchr(type, '*') && !strchr(subtype, '*'))
            val = xstrdup(accept->token);
        free(type);
        free(subtype);
        param_free(&params);
        struct accept *tmp;
        for (tmp = accept; tmp && tmp->token; tmp++) {
            free(tmp->token);
        }
        free(accept);
    }
    return val;
}


EXPORTED int jmap_download(struct transaction_t *txn)
{
    const char *userid = txn->req_tgt.resource;
    const char *slash = strchr(userid, '/');
    if (!slash) {
        /* XXX - error, needs AccountId */
        return HTTP_NOT_FOUND;
    }

#if 0
    size_t userlen = slash - userid;

    /* invalid user? */
    if (!strncmp(userid, httpd_userid, userlen)) {
        txn->error.desc = "failed to match userid";
        return HTTP_BAD_REQUEST;
    }
#endif

    const char *blobbase = slash + 1;
    slash = strchr(blobbase, '/');
    if (!slash) {
        /* XXX - error, needs blobid */
        txn->error.desc = "failed to find blobid";
        return HTTP_BAD_REQUEST;
    }
    size_t bloblen = slash - blobbase;

    if (*blobbase != 'G') {
        txn->error.desc = "invalid blobid (doesn't start with G)";
        return HTTP_BAD_REQUEST;
    }

    if (bloblen != 41) {
        /* incomplete or incorrect blobid */
        txn->error.desc = "invalid blobid (not 41 chars)";
        return HTTP_BAD_REQUEST;
    }

    const char *name = slash + 1;

    char *accountid = xstrndup(userid, strchr(userid, '/') - userid);
    int res = 0;

    struct conversations_state *cstate = NULL;
    int r = conversations_open_user(accountid, &cstate);
    if (r) {
        txn->error.desc = error_message(r);
        res = (r == IMAP_MAILBOX_BADNAME) ? HTTP_NOT_FOUND : HTTP_SERVER_ERROR;
        free(accountid);
        return res;
    }

    /* now we're allocating memory, so don't return from here! */

    char *inboxname = mboxname_user_mbox(httpd_userid, NULL);
    char *blobid = NULL;
    char *ctype = NULL;

    struct jmap_req req;
    req.userid = httpd_userid;
    req.accountid = accountid;
    req.inboxname = inboxname;
    req.cstate = cstate;
    req.authstate = httpd_authstate;
    req.args = NULL;
    req.response = NULL;
    req.tag = NULL;
    req.client_creation_ids = NULL;
    req.new_creation_ids = NULL;
    req.txn = txn;
    req.force_openmbox_rw = 0;


    /* Initialize ACL mailbox cache for findblob */
    hash_table mboxrights = HASH_TABLE_INITIALIZER;
    construct_hash_table(&mboxrights, 64, 0);
    req.mboxrights = &mboxrights;

    jmap_initreq(&req);

    blobid = xstrndup(blobbase, bloblen);

    struct mailbox *mbox = NULL;
    msgrecord_t *mr = NULL;
    struct body *body = NULL;
    const struct body *part = NULL;
    struct buf msg_buf = BUF_INITIALIZER;
    char *decbuf = NULL;
    strarray_t headers = STRARRAY_INITIALIZER;
    char *accept_mime = NULL;

    /* Find part containing blob */
    r = _findblob(&req, blobid, accountid, &mbox, &mr, &body, &part, &msg_buf);
    if (r) {
        res = HTTP_NOT_FOUND; // XXX errors?
        txn->error.desc = "failed to find blob by id";
        goto done;
    }

    if (!buf_base(&msg_buf)) {
        /* Map the message into memory */
        r = msgrecord_get_body(mr, &msg_buf);
        if (r) {
            res = HTTP_NOT_FOUND; // XXX errors?
            txn->error.desc = "failed to map record";
            goto done;
        }
    }

    struct strlist *param;
    if ((param = hash_lookup("accept", &txn->req_qparams))) {
        accept_mime = xstrdup(param->s);
    }

    const char **hdr;
    if (!accept_mime && (hdr = spool_getheader(txn->req_hdrs, "Accept"))) {
        accept_mime = parse_accept_header(hdr);
    }
    if (!accept_mime) accept_mime = xstrdup("application/octet-stream");

    // default with no part is the whole message
    const char *base = msg_buf.s;
    size_t len = msg_buf.len;
    txn->resp_body.type = accept_mime;

    if (part) {
        // map into just this part
        base += part->content_offset;
        len = part->content_size;

        // binary decode if needed
        int encoding = part->charset_enc & 0xff;
        base = charset_decode_mimebody(base, len, encoding, &decbuf, &len);
    }

    txn->resp_body.len = len;
    txn->resp_body.dispo.fname = name;

    write_body(HTTP_OK, txn, base, len);

 done:
    free(accept_mime);
    free_hash_table(&mboxrights, free);
    free(accountid);
    free(decbuf);
    free(ctype);
    strarray_fini(&headers);
    if (mbox) jmap_closembox(&req, &mbox);
    conversations_commit(&cstate);
    if (body) {
        message_free_body(body);
        free(body);
    }
    if (mr) {
        msgrecord_unref(&mr);
    }
    buf_free(&msg_buf);
    free(blobid);
    jmap_finireq(&req);
    free(inboxname);
    return res;
}

static int lookup_upload_collection(const char *accountid, mbentry_t **mbentry)
{
    mbname_t *mbname;
    const char *uploadname;
    int r;

    /* Create notification mailbox name from the parsed path */
    mbname = mbname_from_userid(accountid);
    mbname_push_boxes(mbname, config_getstring(IMAPOPT_JMAPUPLOADFOLDER));

    /* XXX - hack to allow @domain parts for non-domain-split users */
    if (httpd_extradomain) {
        /* not allowed to be cross domain */
        if (mbname_localpart(mbname) &&
            strcmpsafe(mbname_domain(mbname), httpd_extradomain)) {
            r = HTTP_NOT_FOUND;
            goto done;
        }
        mbname_set_domain(mbname, NULL);
    }

    /* Locate the mailbox */
    uploadname = mbname_intname(mbname);
    r = http_mlookup(uploadname, mbentry, NULL);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* Find location of INBOX */
        char *inboxname = mboxname_user_mbox(accountid, NULL);

        int r1 = http_mlookup(inboxname, mbentry, NULL);
        free(inboxname);
        if (r1 == IMAP_MAILBOX_NONEXISTENT) {
            r = IMAP_INVALID_USER;
            goto done;
        }

        int rights = httpd_myrights(httpd_authstate, *mbentry);
        if (!(rights & ACL_CREATE)) {
            r = IMAP_PERMISSION_DENIED;
            goto done;
        }

        if (*mbentry) free((*mbentry)->name);
        else *mbentry = mboxlist_entry_create();
        (*mbentry)->name = xstrdup(uploadname);
    }
    else if (!r) {
        int rights = httpd_myrights(httpd_authstate, *mbentry);
        if (!(rights & ACL_INSERT)) {
            r = IMAP_PERMISSION_DENIED;
            goto done;
        }
    }

  done:
    mbname_free(&mbname);
    return r;
}


static int create_upload_collection(const char *accountid,
                                    struct mailbox **mailbox)
{
    /* notifications collection */
    mbentry_t *mbentry = NULL;
    int r = lookup_upload_collection(accountid, &mbentry);

    if (r == IMAP_INVALID_USER) {
        goto done;
    }
    else if (r == IMAP_PERMISSION_DENIED) {
        goto done;
    }
    else if (r == IMAP_MAILBOX_NONEXISTENT) {
        if (!mbentry) goto done;
        else if (mbentry->server) {
            proxy_findserver(mbentry->server, &http_protocol, httpd_userid,
                             &backend_cached, NULL, NULL, httpd_in);
            goto done;
        }

        r = mboxlist_createmailbox(mbentry->name, MBTYPE_COLLECTION,
                                   NULL, 1 /* admin */, accountid,
                                   httpd_authstate, 0, 0, 0, 0, mailbox);
        /* we lost the race, that's OK */
        if (r == IMAP_MAILBOX_LOCKED) r = 0;
        if (r) syslog(LOG_ERR, "IOERROR: failed to create %s (%s)",
                      mbentry->name, error_message(r));
    }
    else if (mailbox) {
        /* Open mailbox for writing */
        r = mailbox_open_iwl(mbentry->name, mailbox);
        if (r) {
            syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s",
                   mbentry->name, error_message(r));
        }
    }

 done:
    mboxlist_entry_free(&mbentry);
    return r;
}

/* Helper function to determine domain of data */
enum {
    DOMAIN_7BIT = 0,
    DOMAIN_8BIT,
    DOMAIN_BINARY
};

static int data_domain(const char *p, size_t n)
{
    int r = DOMAIN_7BIT;

    while (n--) {
        if (!*p) return DOMAIN_BINARY;
        if (*p & 0x80) r = DOMAIN_8BIT;
        p++;
    }

    return r;
}

EXPORTED int jmap_upload(struct transaction_t *txn)
{
    strarray_t flags = STRARRAY_INITIALIZER;

    struct body *body = NULL;

    int ret = HTTP_CREATED;
    hdrcache_t hdrcache = txn->req_hdrs;
    struct stagemsg *stage = NULL;
    FILE *f = NULL;
    const char **hdr;
    time_t now = time(NULL);
    struct appendstate as;

    struct mailbox *mailbox = NULL;
    int r = 0;

    /* Read body */
    txn->req_body.flags |= BODY_DECODE;
    r = http_read_req_body(txn);
    if (r) {
        txn->flags.conn = CONN_CLOSE;
        return r;
    }

    const char *data = buf_base(&txn->req_body.payload);
    size_t datalen = buf_len(&txn->req_body.payload);

    if (datalen > (size_t) jmap_max_size_upload) {
        txn->error.desc = "JSON upload byte size exceeds maxSizeUpload";
        return HTTP_PAYLOAD_TOO_LARGE;
    }

    /* Resource must be {accountId}/ with no trailing path */
    char *accountid = xstrdup(txn->req_tgt.resource);
    char *slash = strchr(accountid, '/');
    if (!slash || *(slash + 1) != '\0') {
        ret = HTTP_NOT_FOUND;
        goto done;
    }
    *slash = '\0';

    r = create_upload_collection(accountid, &mailbox);
    if (r) {
        syslog(LOG_ERR, "jmap_upload: can't open upload collection for %s: %s",
               error_message(r), accountid);
        ret = HTTP_NOT_FOUND;
        goto done;
    }

    /* Prepare to stage the message */
    if (!(f = append_newstage(mailbox->name, now, 0, &stage))) {
        syslog(LOG_ERR, "append_newstage(%s) failed", mailbox->name);
        txn->error.desc = "append_newstage() failed";
        ret = HTTP_SERVER_ERROR;
        goto done;
    }

    /* Create RFC 5322 header for resource */
    if ((hdr = spool_getheader(hdrcache, "User-Agent"))) {
        fprintf(f, "User-Agent: %s\r\n", hdr[0]);
    }

    if ((hdr = spool_getheader(hdrcache, "From"))) {
        fprintf(f, "From: %s\r\n", hdr[0]);
    }
    else {
        char *mimehdr;

        assert(!buf_len(&txn->buf));
        if (strchr(httpd_userid, '@')) {
            /* XXX  This needs to be done via an LDAP/DB lookup */
            buf_printf(&txn->buf, "<%s>", httpd_userid);
        }
        else {
            buf_printf(&txn->buf, "<%s@%s>", httpd_userid, config_servername);
        }

        mimehdr = charset_encode_mimeheader(buf_cstring(&txn->buf),
                                            buf_len(&txn->buf), 0);
        fprintf(f, "From: %s\r\n", mimehdr);
        free(mimehdr);
        buf_reset(&txn->buf);
    }

    if ((hdr = spool_getheader(hdrcache, "Subject"))) {
        fprintf(f, "Subject: %s\r\n", hdr[0]);
    }

    if ((hdr = spool_getheader(hdrcache, "Date"))) {
        fprintf(f, "Date: %s\r\n", hdr[0]);
    }
    else {
        char datestr[80];
        time_to_rfc5322(now, datestr, sizeof(datestr));
        fprintf(f, "Date: %s\r\n", datestr);
    }

    if ((hdr = spool_getheader(hdrcache, "Message-ID"))) {
        fprintf(f, "Message-ID: %s\r\n", hdr[0]);
    }

    const char *type = "application/octet-stream";
    if ((hdr = spool_getheader(hdrcache, "Content-Type"))) {
        type = hdr[0];
    }
    fprintf(f, "Content-Type: %s\r\n", type);

    int domain = data_domain(data, datalen);
    switch (domain) {
        case DOMAIN_BINARY:
            fputs("Content-Transfer-Encoding: BINARY\r\n", f);
            break;
        case DOMAIN_8BIT:
            fputs("Content-Transfer-Encoding: 8BIT\r\n", f);
            break;
        default:
            break; // no CTE == 7bit
    }

    if ((hdr = spool_getheader(hdrcache, "Content-Disposition"))) {
        fprintf(f, "Content-Disposition: %s\r\n", hdr[0]);
    }

    if ((hdr = spool_getheader(hdrcache, "Content-Description"))) {
        fprintf(f, "Content-Description: %s\r\n", hdr[0]);
    }

    fprintf(f, "Content-Length: %u\r\n", (unsigned) datalen);

    fputs("MIME-Version: 1.0\r\n\r\n", f);

    /* Write the data to the file */
    fwrite(data, datalen, 1, f);
    fclose(f);

    /* Prepare to append the message to the mailbox */
    r = append_setup_mbox(&as, mailbox, httpd_userid, httpd_authstate,
                          0, /*quota*/NULL, 0, 0, /*event*/0);
    if (r) {
        syslog(LOG_ERR, "append_setup(%s) failed: %s",
               mailbox->name, error_message(r));
        ret = HTTP_SERVER_ERROR;
        txn->error.desc = "append_setup() failed";
        goto done;
    }

    /* Append the message to the mailbox */
    strarray_append(&flags, "\\Deleted");
    strarray_append(&flags, "\\Expunged");  // custom flag to insta-expunge!
    r = append_fromstage(&as, &body, stage, now, 0, &flags, 0, /*annots*/NULL);

    if (r) {
        append_abort(&as);
        syslog(LOG_ERR, "append_fromstage(%s) failed: %s",
               mailbox->name, error_message(r));
        ret = HTTP_SERVER_ERROR;
        txn->error.desc = "append_fromstage() failed";
        goto done;
    }

    r = append_commit(&as);
    if (r) {
        syslog(LOG_ERR, "append_commit(%s) failed: %s",
               mailbox->name, error_message(r));
        ret = HTTP_SERVER_ERROR;
        txn->error.desc = "append_commit() failed";
        goto done;
    }

    char datestr[RFC3339_DATETIME_MAX];
    time_to_rfc3339(now + 86400, datestr, RFC3339_DATETIME_MAX);

    char *blobid = jmap_blobid(&body->content_guid);

    /* Create response object */
    json_t *resp = json_pack("{s:s}", "accountId", accountid);
    json_object_set_new(resp, "blobId", json_string(blobid));
    free(blobid);
    json_object_set_new(resp, "size", json_integer(datalen));
    json_object_set_new(resp, "expires", json_string(datestr));

    /* Remove CFWS and encodings from type */
    char *normalisedtype = charset_decode_mimeheader(type, CHARSET_SNIPPET);
    json_object_set_new(resp, "type", json_string(normalisedtype));
    free(normalisedtype);

    /* Output the JSON object */
    ret = json_response(HTTP_CREATED, txn, resp);

done:
    free(accountid);
    if (body) {
        message_free_body(body);
        free(body);
    }
    strarray_fini(&flags);
    append_removestage(stage);
    if (mailbox) {
        if (r) mailbox_abort(mailbox);
        else r = mailbox_commit(mailbox);
        mailbox_close(&mailbox);
    }

    return ret;
}

static int jmap_core_echo(jmap_req_t *req)
{
    json_array_append_new(req->response,
                          json_pack("[s,O,s]", "Core/echo", req->args, req->tag));
    return 0;
}

static int jmap_copyblob(jmap_req_t *req,
                         const char *blobid,
                         const char *from_accountid,
                         struct mailbox *to_mbox)
{
    struct mailbox *mbox = NULL;
    msgrecord_t *mr = NULL;
    struct body *body = NULL;
    const struct body *part = NULL;
    struct buf msg_buf = BUF_INITIALIZER;
    FILE *to_fp = NULL;
    struct stagemsg *stage = NULL;

    int r = _findblob(req, blobid, from_accountid, &mbox, &mr, &body, &part, &msg_buf);
    if (r) return r;

    if (!part)
        part = body;

    if (!buf_base(&msg_buf)) {
        /* Map the message into memory */
        r = msgrecord_get_body(mr, &msg_buf);
        if (r) {
            syslog(LOG_ERR, "jmap_copyblob(%s): msgrecord_get_body: %s",
                   blobid, error_message(r));
            goto done;
        }
    }

    /* Create staging file */
    time_t internaldate = time(NULL);
    if (!(to_fp = append_newstage(to_mbox->name, internaldate, 0, &stage))) {
        syslog(LOG_ERR, "jmap_copyblob(%s): append_newstage(%s) failed",
                blobid, mbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Copy blob. Keep the original MIME headers, we wouldn't really
     * know which ones are safe to rewrite for arbitrary blobs. */
    fwrite(buf_base(&msg_buf) + part->header_offset,
           part->header_size + part->content_size, 1, to_fp);
    if (ferror(to_fp)) {
        syslog(LOG_ERR, "jmap_copyblob(%s): tofp=%s: %s",
               blobid, append_stagefname(stage), strerror(errno));
        r = IMAP_IOERROR;
        goto done;
    }
    fclose(to_fp);
    to_fp = NULL;

    /* Append blob to mailbox */
    struct body *to_body = NULL;
    struct appendstate as;
    r = append_setup_mbox(&as, to_mbox, httpd_userid, httpd_authstate,
            0, /*quota*/NULL, 0, 0, /*event*/0);
    if (r) {
        syslog(LOG_ERR, "jmap_copyblob(%s): append_setup_mbox: %s",
                blobid, error_message(r));
        goto done;
    }
    strarray_t flags = STRARRAY_INITIALIZER;
    strarray_append(&flags, "\\Deleted");
    strarray_append(&flags, "\\Expunged");  // custom flag to insta-expunge!
	r = append_fromstage(&as, &to_body, stage, 0, internaldate, &flags, 0, NULL);
    strarray_fini(&flags);
	if (r) {
        syslog(LOG_ERR, "jmap_copyblob(%s): append_fromstage: %s",
                blobid, error_message(r));
		append_abort(&as);
		goto done;
	}
	message_free_body(to_body);
	free(to_body);
	r = append_commit(&as);
	if (r) {
        syslog(LOG_ERR, "jmap_copyblob(%s): append_commit: %s",
                blobid, error_message(r));
        goto done;
    }

done:
    if (stage) append_removestage(stage);
    if (to_fp) fclose(to_fp);
    buf_free(&msg_buf);
    message_free_body(body);
    free(body);
    msgrecord_unref(&mr);
    jmap_closembox(req, &mbox);
    return r;
}

static int jmap_blob_copy(jmap_req_t *req)
{
    json_t *args = req->args;
    const char *from_accountid = NULL;
    const char *to_accountid = NULL;
    json_t *val, *blobids, *invalid = json_array();
    size_t i = 0;
    struct buf buf = BUF_INITIALIZER;

    /* Parse request */
    val = json_object_get(args, "fromAccountId");
    if (JNOTNULL(val) && !json_is_string(val)) {
        json_array_append_new(invalid, json_string("fromAccountId"));
    }
    from_accountid = json_string_value(val);
    if (from_accountid == NULL) {
        from_accountid = req->userid;
    }
    val = json_object_get(args, "toAccountId");
    if (JNOTNULL(val) && !json_is_string(val)) {
        json_array_append_new(invalid, json_string("toAccountId"));
    }
    to_accountid = json_string_value(val);
    if (to_accountid == NULL) {
        to_accountid = req->userid;
    }
    blobids = json_object_get(args, "blobIds");
    if (!json_is_array(blobids)) {
        json_array_append_new(invalid, json_string("blobIds"));
    }
    json_array_foreach(blobids, i, val) {
        if (!json_is_string(val)) {
            buf_printf(&buf, "blobIds[%zu]", i);
            json_array_append_new(invalid, json_string(buf_cstring(&buf)));
            buf_reset(&buf);
        }
    }
    if (json_array_size(invalid)) {
        json_t *err = json_pack("{s:s, s:o}",
                "type", "invalidArguments", "arguments", invalid);
        json_array_append_new(req->response, json_pack("[s,o,s]",
                    "error", err, req->tag));
        return 0;
    }
    json_decref(invalid);

    /* No return from here on */
    struct mailbox *to_mbox = NULL;
    json_t *not_copied = json_object();
    json_t *copied = json_object();

    /* Check if we can upload to toAccountId */
    int r = create_upload_collection(to_accountid, &to_mbox);
    if (r == IMAP_PERMISSION_DENIED) {
        json_array_foreach(blobids, i, val) {
            json_object_set(not_copied, json_string_value(val),
                    json_pack("{s:s}", "type", "toAccountNotFound"));
        }
        r = 0;
        goto done;
    } else if (r) {
        syslog(LOG_ERR, "jmap_blob_copy: create_upload_collection(%s): %s",
                to_accountid, error_message(r));
        goto done;
    }

    /* Check if we can access any mailbox of fromAccountId */
    r = mymblist(httpd_userid, from_accountid, httpd_authstate,
            req->mboxrights, is_accessible, NULL, 0/*all*/);
    if (r != IMAP_OK_COMPLETED) {
        json_array_foreach(blobids, i, val) {
            json_object_set(not_copied, json_string_value(val),
                    json_pack("{s:s}", "type", "fromAccountNotFound"));
        }
        r = 0;
        goto done;
    }
    r = 0;

    /* Copy blobs one by one. XXX should we batch copy here? */
    json_array_foreach(blobids, i, val) {
        const char *blobid = json_string_value(val);
        r = jmap_copyblob(req, blobid, from_accountid, to_mbox);
        if (r == IMAP_NOTFOUND) {
            json_object_set_new(not_copied, blobid,
                    json_pack("{s:s}", "type", "blobNotFound"));
            r = 0;
            continue;
        }
        else if (r) goto done;
        json_object_set_new(copied, blobid, json_string(blobid));
    }

done:
    if (!r) {
        /* Build response */
        if (!json_object_size(copied)) {
            json_decref(copied);
            copied = json_null();
        }
        if (!json_object_size(not_copied)) {
            json_decref(not_copied);
            not_copied = json_null();
        }
        json_t *res = json_pack("{s:O s:O s:o s:o}",
                "fromAccountId", json_object_get(args, "fromAccountId"),
                "toAccountId", json_object_get(args, "toAccountId"),
                "copied", copied, "notCopied", not_copied);
        json_array_append_new(req->response, json_pack("[s,o,s]",
                    "Blob/copy", res, req->tag));
    }
    mailbox_close(&to_mbox);
    return r;
}

EXPORTED int jmap_cmpstate(jmap_req_t* req, json_t *state, int mbtype)
{
    if (JNOTNULL(state)) {
        const char *s = json_string_value(state);
        if (!s) {
            return -1;
        }
        modseq_t client_modseq = atomodseq_t(s);
        modseq_t server_modseq = 0;
        switch (mbtype) {
         case MBTYPE_CALENDAR:
             server_modseq = req->counters.caldavmodseq;
             break;
         case MBTYPE_ADDRESSBOOK:
             server_modseq = req->counters.carddavmodseq;
             break;
         default:
             server_modseq = req->counters.mailmodseq;
        }
        if (client_modseq < server_modseq)
            return -1;
        else if (client_modseq > server_modseq)
            return 1;
        else
            return 0;
    }
    return 0;
}

EXPORTED modseq_t jmap_highestmodseq(jmap_req_t *req, int mbtype)
{
    modseq_t modseq;

    /* Determine current counter by mailbox type. */
    switch (mbtype) {
        case MBTYPE_CALENDAR:
            modseq = req->counters.caldavmodseq;
            break;
        case MBTYPE_ADDRESSBOOK:
            modseq = req->counters.carddavmodseq;
            break;
        case 0:
            modseq = req->counters.mailmodseq;
            break;
        default:
            modseq = req->counters.highestmodseq;
    }

    return modseq;
}

EXPORTED json_t* jmap_getstate(jmap_req_t *req, int mbtype, int refresh)
{
    if (refresh)
        assert (!mboxname_read_counters(req->inboxname, &req->counters));
    struct buf buf = BUF_INITIALIZER;
    json_t *state = NULL;
    modseq_t modseq = jmap_highestmodseq(req, mbtype);

    buf_printf(&buf, MODSEQ_FMT, modseq);
    state = json_string(buf_cstring(&buf));
    buf_free(&buf);

    return state;
}


EXPORTED json_t *jmap_fmtstate(modseq_t modseq)
{
    struct buf buf = BUF_INITIALIZER;
    json_t *state = NULL;
    buf_printf(&buf, MODSEQ_FMT, modseq);
    state = json_string(buf_cstring(&buf));
    buf_free(&buf);
    return state;
}

EXPORTED char *jmap_xhref(const char *mboxname, const char *resource)
{
    /* XXX - look up root path from namespace? */
    struct buf buf = BUF_INITIALIZER;
    char *userid = mboxname_to_userid(mboxname);

    const char *prefix = NULL;
    if (mboxname_isaddressbookmailbox(mboxname, 0)) {
        prefix = namespace_addressbook.prefix;
    }
    else if (mboxname_iscalendarmailbox(mboxname, 0)) {
        prefix = namespace_calendar.prefix;
    }

    if (strchr(userid, '@') || !httpd_extradomain) {
        buf_printf(&buf, "%s/%s/%s/%s", prefix, USER_COLLECTION_PREFIX,
                   userid, strrchr(mboxname, '.')+1);
    }
    else {
        buf_printf(&buf, "%s/%s/%s@%s/%s", prefix, USER_COLLECTION_PREFIX,
                   userid, httpd_extradomain, strrchr(mboxname, '.')+1);
    }
    if (resource)
        buf_printf(&buf, "/%s", resource);
    free(userid);
    return buf_release(&buf);
}

static int jmap_need_auth(struct transaction_t *txn __attribute__((unused)))
{
    /* All endpoints require authentication */
    return HTTP_UNAUTHORIZED;
}

struct findaccounts_data {
    json_t *accounts;
    struct buf userid;
    int rw;
    int has_mail;
    int has_contacts;
    int has_calendars;
};

static void findaccounts_add(struct findaccounts_data *ctx)
{
    if (!buf_len(&ctx->userid))
        return;

    const char *userid = buf_cstring(&ctx->userid);

    json_t *has_data_for = json_array();
    if (ctx->has_mail)
        json_array_append_new(has_data_for, json_string(JMAP_URN_MAIL));
    if (ctx->has_contacts)
        json_array_append_new(has_data_for, json_string(JMAP_URN_CONTACTS));
    if (ctx->has_calendars)
        json_array_append_new(has_data_for, json_string(JMAP_URN_CALENDARS));

    json_t *account = json_object();
    json_object_set_new(account, "name", json_string(userid));
    json_object_set_new(account, "isPrimary", json_false());
    json_object_set_new(account, "isReadOnly", json_boolean(!ctx->rw));
    json_object_set_new(account, "hasDataFor", has_data_for);

    json_object_set_new(ctx->accounts, userid, account);
}

static int findaccounts_cb(struct findall_data *data, void *rock)
{
    if (!data || !data->mbentry)
        return 0;

    const mbentry_t *mbentry = data->mbentry;
    mbname_t *mbname = mbname_from_intname(mbentry->name);
    const char *userid = mbname_userid(mbname);
    struct findaccounts_data *ctx = rock;
    const strarray_t *boxes = mbname_boxes(mbname);

    if (strcmp(buf_cstring(&ctx->userid), userid)) {
        /* We haven't yet seen this account. Add any previous account and reset state */
        findaccounts_add(ctx);
        buf_setcstr(&ctx->userid, userid);
        ctx->rw = 0;
        ctx->has_mail = 0;
        ctx->has_contacts = 0;
        ctx->has_calendars = 0;
    }

    if (!ctx->rw) {
        ctx->rw = httpd_myrights(httpd_authstate, data->mbentry) & ACL_READ_WRITE;
    }
    if (!ctx->has_mail) {
        ctx->has_mail = mbentry->mbtype == MBTYPE_EMAIL;
    }
    if (!ctx->has_contacts) {
        /* Only count children of user.foo.#addressbooks */
        const char *prefix = config_getstring(IMAPOPT_ADDRESSBOOKPREFIX);
        ctx->has_contacts =
            strarray_size(boxes) > 1 && !strcmpsafe(prefix, strarray_nth(boxes, 0));
    }
    if (!ctx->has_calendars) {
        /* Only count children of user.foo.#calendars */
        const char *prefix = config_getstring(IMAPOPT_CALENDARPREFIX);
        ctx->has_calendars =
            strarray_size(boxes) > 1 && !strcmpsafe(prefix, strarray_nth(boxes, 0));
    }

    mbname_free(&mbname);
    return 0;
}

static json_t *user_settings(const char *userid)
{
    json_t *accounts = json_pack("{s:{s:s s:b s:b s:[s,s,s]}}",
            userid, "name", userid,
            "isPrimary", 1,
            "isReadOnly", 0,
            /* JMAP autoprovisions calendars and contacts,
             * so these JMAP types always are available
             * for the primary account */
            "hasDataFor",
            JMAP_URN_MAIL,
            JMAP_URN_CONTACTS,
            JMAP_URN_CALENDARS);

    /* Find all shared accounts */
    strarray_t patterns = STRARRAY_INITIALIZER;
    char *userpat = xstrdup("user.*");
    userpat[4] = jmap_namespace.hier_sep;
    strarray_append(&patterns, userpat);
    struct findaccounts_data ctx = { accounts, BUF_INITIALIZER, 0, 0, 0, 0 };
    int r = mboxlist_findallmulti(&jmap_namespace, &patterns, 0, userid,
                                  httpd_authstate, findaccounts_cb, &ctx);
    free(userpat);
    strarray_fini(&patterns);
    if (r) {
        syslog(LOG_ERR, "Can't determine shared JMAP accounts for user %s: %s",
                userid, error_message(r));
    }
    /* Finalise last seen account */
    findaccounts_add(&ctx);
    buf_free(&ctx.userid);

    return json_pack("{s:s s:o s:O s:s s:s s:s}",
            "username", userid,
            "accounts", accounts,
            "capabilities", jmap_capabilities,
            "apiUrl", JMAP_BASE_URL,
            "downloadUrl", JMAP_BASE_URL JMAP_DOWNLOAD_COL JMAP_DOWNLOAD_TPL,
            /* FIXME eventSourceUrl */
            "uploadUrl", JMAP_BASE_URL JMAP_UPLOAD_COL JMAP_UPLOAD_TPL);
}

/* Handle a GET on the settings endpoint */
static int jmap_settings(struct transaction_t *txn)
{
    assert(httpd_userid);

    /* Create the response object */
    json_t *res = user_settings(httpd_userid);
    if (!res) {
        syslog(LOG_ERR, "JMAP auth: cannot determine user settings for %s",
                httpd_userid);
        return HTTP_SERVER_ERROR;
    }

    /* Write the JSON response */
    return json_response(HTTP_OK, txn, res);
}

static int myrights(struct auth_state *authstate,
                    const mbentry_t *mbentry,
                    hash_table *mboxrights)
{
    int *rightsptr = hash_lookup(mbentry->name, mboxrights);
    if (!rightsptr) {
        rightsptr = xmalloc(sizeof(int));
        *rightsptr = httpd_myrights(authstate, mbentry);
        hash_insert(mbentry->name, rightsptr, mboxrights);
    }
    return *rightsptr;
}

static int _rights_for_mbentry(jmap_req_t *req, const mbentry_t *mbentry)
{
    // for the mailbox owner, assume full rights
    int rights = -1;

    mbname_t *mbname = mbname_from_intname(mbentry->name);
    if (strcmp(mbname_userid(mbname), req->userid)) {
        if (mbentry->mbtype & MBTYPE_INTERMEDIATE) {
            // if it's an intermediate mailbox, we get rights from the parent
            mbentry_t *parententry = NULL;
            if (mboxlist_findparent(mbentry->name, &parententry))
                rights = 0;
            else
                rights = httpd_myrights(req->authstate, parententry);
            mboxlist_entry_free(&parententry);
        }
        else
            rights = httpd_myrights(req->authstate, mbentry);
    }
    mbname_free(&mbname);

    // intermediate mailboxes have limited rights, just see, create sub,
    // rename and delete:
    if (mbentry->mbtype & MBTYPE_INTERMEDIATE)
        rights &= ACL_LOOKUP | ACL_CREATE | ACL_DELETEMBOX;

    return rights;
}


EXPORTED int jmap_myrights(jmap_req_t *req, const mbentry_t *mbentry)
{
    int *rightsptr = hash_lookup(mbentry->name, req->mboxrights);

    if (!rightsptr) {
        rightsptr = xmalloc(sizeof(int));
        *rightsptr = _rights_for_mbentry(req, mbentry);
        hash_insert(mbentry->name, rightsptr, req->mboxrights);
    }

    return *rightsptr;
}

EXPORTED int jmap_myrights_byname(jmap_req_t *req, const char *mboxname)
{
    int *rightsptr = hash_lookup(mboxname, req->mboxrights);

    if (!rightsptr) {
        rightsptr = xmalloc(sizeof(int));

        // if unable to read, that means no rights
        int rights = 0;
        mbentry_t *mbentry = NULL;
        if (!mboxlist_lookup(mboxname, &mbentry, NULL)) {
            rights = _rights_for_mbentry(req, mbentry);
            mboxlist_entry_free(&mbentry);
        }

        *rightsptr = rights;
        hash_insert(mboxname, rightsptr, req->mboxrights);
    }

    return *rightsptr;
}


EXPORTED void jmap_myrights_delete(jmap_req_t *req, const char *mboxname)
{
    int *rightsptr = hash_del(mboxname, req->mboxrights);
    free(rightsptr);
}

EXPORTED json_t* jmap_patchobject_apply(json_t *val, json_t *patch)
{
    const char *path;
    json_t *newval, *dst;

    dst = json_deep_copy(val);
    json_object_foreach(patch, path, newval) {
        /* Start traversal at root object */
        json_t *it = dst;
        const char *base = path, *top;
        /* Find path in object tree */
        while ((top = strchr(base, '/'))) {
            char *name = json_pointer_decode(base, top-base);
            it = json_object_get(it, name);
            free(name);
            base = top + 1;
        }
        if (!it) {
            /* No such path in 'val' */
            json_decref(dst);
            return NULL;
        }
        /* Replace value at path */
        char *name = json_pointer_decode(base, strlen(base));
        json_object_set(it, name, newval);
        free(name);
    }

    return dst;
}

static void jmap_patchobject_diff(json_t *patch, struct buf *buf, json_t *a, json_t *b)
{
    const char *id;
    json_t *o;

    if (b == NULL || json_equal(a, b)) {
        return;
    }

    if (!a || json_is_null(a) || json_typeof(b) != JSON_OBJECT) {
        json_object_set(patch, buf_cstring(buf), b);
    }

    json_object_foreach(b, id, o) {
        char *encid = json_pointer_encode(id);
        size_t l = buf_len(buf);
        if (!l) {
            buf_setcstr(buf, encid);
        } else {
            buf_appendcstr(buf, "/");
            buf_appendcstr(buf, encid);
        }
        jmap_patchobject_diff(patch, buf, json_object_get(a, id), o);
        buf_truncate(buf, l);
        free(encid);
    }
}

EXPORTED json_t *jmap_patchobject_create(json_t *a, json_t *b)
{
    json_t *patch = json_object();
    struct buf buf = BUF_INITIALIZER;
    jmap_patchobject_diff(patch, &buf, a, b);
    buf_free(&buf);
    return patch;
}

EXPORTED void jmap_add_perf(jmap_req_t *req, json_t *res)
{
    if (req->do_perf) {
        struct rusage usage;

        getrusage(RUSAGE_SELF, &usage);

        json_t *perf = json_pack("{s:f s:f s:f}",
            "real", (now_ms() / 1000.0) - req->real_start,
            "user", timeval_get_double(&usage.ru_utime) - req->user_start,
            "sys", timeval_get_double(&usage.ru_stime) - req->sys_start);

        json_object_set_new(res, "performance", perf);
    }
}

EXPORTED void jmap_parser_fini(struct jmap_parser *parser)
{
    strarray_fini(&parser->path);
    json_decref(parser->invalid);
    buf_free(&parser->buf);
}

EXPORTED void jmap_parser_push(struct jmap_parser *parser, const char *prop)
{
    strarray_push(&parser->path, prop);
}

EXPORTED void jmap_parser_push_index(struct jmap_parser *parser,
                                     const char *prop, size_t index, const char *name)
{
    /* TODO make this more clever: won't need to printf most of the time */
    if (name) buf_printf(&parser->buf, "%s[%zu:%s]", prop, index, name);
    else buf_printf(&parser->buf, "%s[%zu]", prop, index);
    strarray_push(&parser->path, buf_cstring(&parser->buf));
    buf_reset(&parser->buf);
}

EXPORTED void jmap_parser_push_name(struct jmap_parser *parser,
                                    const char *prop, const char *name)
{
    /* TODO make this more clever: won't need to printf most of the time */
    buf_printf(&parser->buf, "%s{%s}", prop, name);
    strarray_push(&parser->path, buf_cstring(&parser->buf));
    buf_reset(&parser->buf);
}

EXPORTED void jmap_parser_pop(struct jmap_parser *parser)
{
    free(strarray_pop(&parser->path));
}

EXPORTED const char* jmap_parser_path(struct jmap_parser *parser, struct buf *buf)
{
    int i;
    buf_reset(buf);

    for (i = 0; i < parser->path.count; i++) {
        const char *p = strarray_nth(&parser->path, i);
        if (json_pointer_needsencode(p)) {
            char *tmp = json_pointer_encode(p);
            buf_appendcstr(buf, tmp);
            free(tmp);
        } else {
            buf_appendcstr(buf, p);
        }
        if ((i + 1) < parser->path.count) {
            buf_appendcstr(buf, "/");
        }
    }

    return buf_cstring(buf);
}

EXPORTED void jmap_parser_invalid(struct jmap_parser *parser, const char *prop)
{
    if (prop)
        jmap_parser_push(parser, prop);

    json_array_append_new(parser->invalid,
            json_string(jmap_parser_path(parser, &parser->buf)));

    if (prop)
        jmap_parser_pop(parser);
}

EXPORTED void jmap_ok(jmap_req_t *req, json_t *res)
{
    json_object_set_new(res, "accountId", json_string(req->accountid));

    json_t *item = json_pack("[]");
    json_array_append_new(item, json_string(req->method));
    json_array_append_new(item, res);
    json_array_append_new(item, json_string(req->tag));
    json_array_append_new(req->response, item);

    jmap_add_perf(req, res);
}

EXPORTED void jmap_error(jmap_req_t *req, json_t *err)
{
    json_array_append_new(req->response,
            json_pack("[s,o,s]", "error", err, req->tag));
}

EXPORTED json_t *jmap_server_error(int r)
{
    return json_pack("{s:s, s:s}",
                     "type", "serverError",
                     "description", error_message(r));
}


EXPORTED int jmap_parse_strings(json_t *arg,
                                struct jmap_parser *parser, const char *prop)
{
    if (!json_is_array(arg)) {
        jmap_parser_invalid(parser, prop);
        return 0;
    }
    int valid = 1;
    size_t i;
    json_t *val;
    json_array_foreach(arg, i, val) {
        if (!json_is_string(val)) {
            jmap_parser_push_index(parser, prop, i, NULL);
            jmap_parser_invalid(parser, NULL);
            jmap_parser_pop(parser);
            valid = 0;
        }
    }
    return valid;
}


EXPORTED const jmap_property_t *jmap_property_find(const char *name,
                                                   const jmap_property_t props[])
{
    const jmap_property_t *prop;

    for (prop = props; prop && prop->name; prop++) {
        if (!strcmp(name, prop->name)) return prop;
        else {
            size_t len = strlen(prop->name);
            if ((prop->name[len-1] == '*') && !strncmp(name, prop->name, len-1))
                return prop;
        }
    }

    return NULL;
}


/* Foo/get */

EXPORTED void jmap_get_parse(json_t *jargs,
                             struct jmap_parser *parser,
                             jmap_req_t *req,
                             const jmap_property_t valid_props[],
                             struct jmap_get *get,
                             json_t **err)
{
    json_t *arg, *val;
    size_t i;

    memset(get, 0, sizeof(struct jmap_get));

    get->list = json_array();
    get->not_found = json_array();

    arg = json_object_get(jargs, "ids");
    if (json_is_array(arg)) {
        get->ids = json_array();
        /* JMAP spec requires: "If an identical id is included more than once
         * in the request, the server MUST only include it once in either the
         * list or notFound argument of the response."
         * So let's weed out duplicate ids here. */
        hash_table _dedup = HASH_TABLE_INITIALIZER;
        construct_hash_table(&_dedup, json_array_size(arg) + 1, 0);
        json_array_foreach(arg, i, val) {
            const char *id = json_string_value(val);
            if (!id) {
                jmap_parser_push_index(parser, "ids", i, NULL);
                jmap_parser_invalid(parser, NULL);
                jmap_parser_pop(parser);
                continue;
            }
            /* Weed out unknown creation ids and add the ids of known
             * creation ids to the requested ids list. THis might
             * cause a race if the Foo object pointed to by creation
             * id is deleted between parsing the request and answering
             * it. But re-checking creation ids for their existence
             * later in the control flow just shifts the problem */
            if (*id == '#') {
                const char *id2 = jmap_lookup_id(req, id + 1);
                if (!id2) {
                    json_array_append_new(get->not_found, json_string(id));
                    continue;
                }
                id = id2;
            }
            if (hash_lookup(id, &_dedup)) {
                continue;
            }
            json_array_append_new(get->ids, json_string(id));
        }
        free_hash_table(&_dedup, NULL);
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "ids");
    }

    arg = json_object_get(jargs, "properties");
    if (json_is_array(arg)) {
        get->props = xzmalloc(sizeof(hash_table));
        construct_hash_table(get->props, json_array_size(arg) + 1, 0);
        json_array_foreach(arg, i, val) {
            const char *s = json_string_value(val);
            if (!s || !jmap_property_find(s, valid_props)) {
                jmap_parser_push_index(parser, "properties", i, s);
                jmap_parser_invalid(parser, NULL);
                jmap_parser_pop(parser);
                continue;
            }
            hash_insert(s, (void*)1, get->props);
        }
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "properties");
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }
}

EXPORTED void jmap_get_fini(struct jmap_get *get)
{
    free_hash_table(get->props, NULL);
    free(get->props);
    free(get->state);
    json_decref(get->ids);
    json_decref(get->list);
    json_decref(get->not_found);
}

EXPORTED json_t *jmap_get_reply(struct jmap_get *get)
{
    json_t *res = json_object();
    json_object_set_new(res, "state", json_string(get->state));
    json_object_set(res, "list", get->list);
    json_object_set(res, "notFound", get->not_found);
    return res;
}


/* Foo/set */

EXPORTED void jmap_set_parse(json_t *jargs, struct jmap_parser *parser,
                             struct jmap_set *set, json_t **err)
{
    memset(set, 0, sizeof(struct jmap_set));
    set->create = json_object();
    set->update = json_object();
    set->destroy = json_array();
    set->created = json_object();
    set->updated = json_object();
    set->destroyed = json_array();
    set->not_created = json_object();
    set->not_updated = json_object();
    set->not_destroyed = json_object();

    json_t *arg, *val;

    /* ifInState */
    arg = json_object_get(jargs, "ifInState");
    if (json_is_string(arg)) {
        set->if_in_state = json_string_value(arg);
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "ifInState");
    }

    /* create */
    arg = json_object_get(jargs, "create");
    if (json_is_object(arg)) {
        const char *id;
        json_object_foreach(arg, id, val) {
            if (!json_is_object(val)) {
                jmap_parser_push(parser, "create");
                jmap_parser_invalid(parser, id);
                jmap_parser_pop(parser);
                continue;
            }
            json_object_set(set->create, id, val);
        }
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "create");
    }

    /* update */
    arg = json_object_get(jargs, "update");
    if (json_is_object(arg)) {
        const char *id;
        json_object_foreach(arg, id, val) {
            if (!json_is_object(val)) {
                jmap_parser_push(parser, "update");
                jmap_parser_invalid(parser, id);
                jmap_parser_pop(parser);
                continue;
            }
            json_object_set(set->update, id, val);
        }
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "update");
    }

    /* destroy */
    arg = json_object_get(jargs, "destroy");
    if (JNOTNULL(arg)) {
        jmap_parse_strings(arg, parser, "destroy");
        if (!json_array_size(parser->invalid)) {
            json_decref(set->destroy);
            set->destroy = json_incref(arg);
        }
    }

    // TODO We could report the following set errors here:
    // -invalidPatch
    // - willDestroy

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }
}


EXPORTED void jmap_set_fini(struct jmap_set *set)
{
    free(set->old_state);
    free(set->new_state);
    json_decref(set->create);
    json_decref(set->update);
    json_decref(set->destroy);
    json_decref(set->created);
    json_decref(set->updated);
    json_decref(set->destroyed);
    json_decref(set->not_created);
    json_decref(set->not_updated);
    json_decref(set->not_destroyed);
}

EXPORTED json_t *jmap_set_reply(struct jmap_set *set)
{
    json_t *res = json_object();
    json_object_set_new(res, "oldState",
            set->old_state ? json_string(set->old_state) : json_null());
    json_object_set_new(res, "newState", json_string(set->new_state));
    json_object_set(res, "created", json_object_size(set->created) ?
            set->created : json_null());
    json_object_set(res, "updated", json_object_size(set->updated) ?
            set->updated : json_null());
    json_object_set(res, "destroyed", json_array_size(set->destroyed) ?
            set->destroyed : json_null());
    json_object_set(res, "notCreated", json_object_size(set->not_created) ?
            set->not_created : json_null());
    json_object_set(res, "notUpdated", json_object_size(set->not_updated) ?
            set->not_updated : json_null());
    json_object_set(res, "notDestroyed", json_object_size(set->not_destroyed) ?
            set->not_destroyed : json_null());
    return res;
}


/* Foo/changes */

EXPORTED void jmap_changes_parse(json_t *jargs,
                                 struct jmap_parser *parser,
                                 struct jmap_changes *changes,
                                 json_t **err)
{
    memset(changes, 0, sizeof(struct jmap_changes));
    changes->created = json_array();
    changes->updated = json_array();
    changes->destroyed = json_array();

    /* sinceState */
    json_t *arg = json_object_get(jargs, "sinceState");
    if (json_is_string(arg)) {
        changes->since_modseq = atomodseq_t(json_string_value(arg));
    }
    if (!changes->since_modseq) {
        jmap_parser_invalid(parser, "sinceState");
    }

    /* maxChanges */
    arg = json_object_get(jargs, "maxChanges");
    if (json_is_integer(arg) && json_integer_value(arg) > 0) {
        changes->max_changes = json_integer_value(arg);
    } else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "maxChanges");
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }
}

EXPORTED void jmap_changes_fini(struct jmap_changes *changes)
{
    json_decref(changes->created);
    json_decref(changes->updated);
    json_decref(changes->destroyed);
}

EXPORTED json_t *jmap_changes_reply(struct jmap_changes *changes)
{
    json_t *res = json_object();
    json_object_set_new(res, "oldState", jmap_fmtstate(changes->since_modseq));
    json_object_set_new(res, "newState", jmap_fmtstate(changes->new_modseq));
    json_object_set_new(res, "hasMoreChanges",
            json_boolean(changes->has_more_changes));
    json_object_set(res, "created", changes->created);
    json_object_set(res, "updated", changes->updated);
    json_object_set(res, "destroyed", changes->destroyed);
    return res;
}


/* Foo/query */

EXPORTED void jmap_filter_parse(json_t *filter, struct jmap_parser *parser,
                                jmap_filter_parse_cb parse_condition,
                                json_t *unsupported, void *rock)
{
    json_t *arg, *val;
    const char *s;
    size_t i;

    if (!JNOTNULL(filter) || json_typeof(filter) != JSON_OBJECT) {
        jmap_parser_invalid(parser, NULL);
        return;
    }
    arg = json_object_get(filter, "operator");
    if ((s = json_string_value(arg))) {
        if (strcmp("AND", s) && strcmp("OR", s) && strcmp("NOT", s)) {
            jmap_parser_invalid(parser, "operator");
        }
        arg = json_object_get(filter, "conditions");
        if (!json_array_size(arg)) {
            jmap_parser_invalid(parser, "conditions");
        }
        json_array_foreach(arg, i, val) {
            jmap_parser_push_index(parser, "conditions", i, NULL);
            jmap_filter_parse(val, parser, parse_condition, unsupported, rock);
            jmap_parser_pop(parser);
        }
    } else if (arg) {
        jmap_parser_invalid(parser, "operator");
    } else {
        parse_condition(filter, parser, unsupported, rock);
    }
}

EXPORTED void jmap_parse_comparator(json_t *jsort, struct jmap_parser *parser,
                                    jmap_comparator_parse_cb comp_cb,
                                    json_t *unsupported, void *rock)
{
    if (!json_is_object(jsort)) {
        jmap_parser_invalid(parser, NULL);
        return;
    }

    struct jmap_comparator comp = { NULL, 0, NULL };

    /* property */
    json_t *val = json_object_get(jsort, "property");
    comp.property = json_string_value(val);
    if (!comp.property) {
        jmap_parser_invalid(parser, "property");
    }

    /* isAscending */
    comp.is_ascending = 1;
    val = json_object_get(jsort, "isAscending");
    if (JNOTNULL(val)) {
        if (!json_is_boolean(val)) {
            jmap_parser_invalid(parser, "isAscending");
        }
        comp.is_ascending = json_boolean_value(val);
    }

    /* collation */
    val = json_object_get(jsort, "collation");
    if (JNOTNULL(val) && !json_is_string(val)) {
        jmap_parser_invalid(parser, "collation");
    }
    comp.collation = json_string_value(val);


    if (comp.property && !comp_cb(&comp, rock)) {
        struct buf buf = BUF_INITIALIZER;
        json_array_append_new(unsupported,
                json_string(jmap_parser_path(parser, &buf)));
        buf_free(&buf);
    }
}

EXPORTED void jmap_query_parse(json_t *jargs, struct jmap_parser *parser,
                               jmap_filter_parse_cb filter_cb, void *filter_rock,
                               jmap_comparator_parse_cb comp_cb, void *sort_rock,
                               struct jmap_query *query, json_t **err)
{
    json_t *arg, *val;
    size_t i;

    memset(query, 0, sizeof(struct jmap_query));
    query->ids = json_array();

    json_t *unsupported_filter = json_array();
    json_t *unsupported_sort = json_array();

    /* filter */
    arg = json_object_get(jargs, "filter");
    if (json_is_object(arg)) {
        jmap_parser_push(parser, "filter");
        jmap_filter_parse(arg, parser, filter_cb, unsupported_filter, filter_rock);
        jmap_parser_pop(parser);
        query->filter = arg;
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "filter");
    }

    /* sort */
    arg = json_object_get(jargs, "sort");
    if (json_is_array(arg)) {
        json_array_foreach(arg, i, val) {
            jmap_parser_push_index(parser, "sort", i, NULL);
            jmap_parse_comparator(val, parser, comp_cb, unsupported_sort, sort_rock);
            jmap_parser_pop(parser);
        }
        if (json_array_size(arg)) {
            query->sort = arg;
        }
    }
    else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "sort");
    }

    arg = json_object_get(jargs, "position");
    if (json_is_integer(arg)) {
        query->position = json_integer_value(arg);
    }
    else if (arg) {
        jmap_parser_invalid(parser, "position");
    }

    arg = json_object_get(jargs, "anchor");
    if (json_is_string(arg)) {
        query->anchor = json_string_value(arg);
    } else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "anchor");
    }

    arg = json_object_get(jargs, "anchorOffset");
    if (json_is_integer(arg)) {
        query->anchor_offset = json_integer_value(arg);
    } else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "anchorOffset");
    }

    arg = json_object_get(jargs, "limit");
    if (json_is_integer(arg) && json_integer_value(arg) >= 0) {
        query->limit = json_integer_value(arg);
        query->have_limit = 1;
    } else if (JNOTNULL(arg)) {
        jmap_parser_invalid(parser, "limit");
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }
	else if (json_array_size(unsupported_filter)) {
		*err = json_pack("{s:s s:O}", "type", "unsupportedFilter",
                "filters", unsupported_filter);
	}
	else if (json_array_size(unsupported_sort)) {
		*err = json_pack("{s:s s:O}", "type", "unsupportedSort",
                "sort", unsupported_sort);
	}

    json_decref(unsupported_filter);
    json_decref(unsupported_sort);
}

EXPORTED void jmap_query_fini(struct jmap_query *query)
{
    free(query->query_state);
    json_decref(query->ids);
}

EXPORTED json_t *jmap_query_reply(struct jmap_query *query)
{

    json_t *res = json_object();
    json_object_set(res, "filter", query->filter);
    json_object_set(res, "sort", query->sort);
    json_object_set_new(res, "queryState", json_string(query->query_state));
    json_object_set_new(res, "canCalculateChanges", json_boolean(query->can_calculate_changes));
    json_object_set_new(res, "position", json_integer(query->result_position));
    json_object_set_new(res, "total", json_integer(query->total));
    /* Special case total */
    if (query->position > 0 && query->total < SSIZE_MAX) {
        if (query->position > (ssize_t) query->total) {
            json_decref(query->ids);
            query->ids = json_array();
        }
    }
    /* Special case limit 0 */
    if (query->have_limit && query->limit == 0) {
        json_array_clear(query->ids);
    }

    json_object_set(res, "ids", query->ids);
    return res;
}
