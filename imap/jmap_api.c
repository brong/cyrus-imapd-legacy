/* jmap_api.c -- Routines for handling JMAP API requests
 *
 * Copyright (c) 1994-2018 Carnegie Mellon University.  All rights reserved.
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

#include <errno.h>

#include "append.h"
#include "cyrusdb.h"
#include "hash.h"
#include "httpd.h"
#include "http_dav.h"
#include "http_dav_sharing.h"
#include "http_jmap.h"
#include "mboxname.h"
#include "msgrecord.h"
#include "proxy.h"
#include "times.h"
#include "strhash.h"
#include "syslog.h"
#include "xstrlcpy.h"

/* generated headers are not necessarily in current directory */
#include "imap/http_err.h"
#include "imap/imap_err.h"
#include "imap/jmap_err.h"


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
        p = jmap_pointer_decode(path, top - path);
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

static int process_resultrefs(json_t *args, json_t *resp, json_t **err)
{
    json_t *ref;
    const char *arg;
    int ret = -1;

    void *tmp;
    json_object_foreach_safe(args, tmp, arg, ref) {
        if (*arg != '#' || *(arg+1) == '\0') {
            continue;
        }

        if (json_object_get(args, arg + 1)) {
            *err = json_pack("{s:s, s:[s]}",
                             "type", "invalidArguments", "arguments", arg);
            goto fail;
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

static int validate_request(struct transaction_t *txn, json_t *req,
                            jmap_settings_t *settings)
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

    if (buf_len(&txn->req_body.payload) >
        (size_t) settings->limits[MAX_SIZE_REQUEST]) {
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
        if (i >= (size_t) settings->limits[MAX_CALLS_IN_REQUEST]) {
            return JMAP_LIMIT_CALLS;
        }
        const char *mname = json_string_value(json_array_get(val, 0));
        mname = strchr(mname, '/');
        if (!mname) continue;

        if (!strcmp(mname, "get")) {
            json_t *ids = json_object_get(json_array_get(val, 1), "ids");
            if (json_array_size(ids) >
                (size_t) settings->limits[MAX_OBJECTS_IN_GET]) {
                return JMAP_LIMIT_OBJS_GET;
            }
        }
        else if (!strcmp(mname, "set")) {
            json_t *args = json_array_get(val, 1);
            size_t size = json_object_size(json_object_get(args, "create"));
            size += json_object_size(json_object_get(args, "update"));
            size += json_array_size(json_object_get(args, "destroy"));
            if (size > (size_t) settings->limits[MAX_OBJECTS_IN_SET]) {
                return JMAP_LIMIT_OBJS_SET;
            }
        }
    }

    json_array_foreach(using, i, val) {
        const char *s = json_string_value(val);
        if (!s) {
            return JMAP_NOT_REQUEST;
        }
        else if (!strcmp(s, "ietf:jmap")) {
            syslog(LOG_DEBUG, "old capability %s used", s);
        }
        else if (!strcmp(s, "ietf:jmapmail")) {
            syslog(LOG_DEBUG, "old capability %s used", s);
        }
        else if (!json_object_get(settings->server_capabilities, s))  {
#if 0 /* FIXME - FastMail Only, ignore unknown capabilities */
            return JMAP_UNKNOWN_CAPABILITY;
#endif
        }
    }

    /* FIXME - FastMail Only, set required capabilities */
    const char *capability;
    json_object_foreach(settings->server_capabilities, capability, val) {
        json_array_append_new(using, json_string(capability));
    }


    return 0;
}

HIDDEN int jmap_is_valid_id(const char *id)
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

static int jmap_error_response(struct transaction_t *txn,
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

    if (txn->meth == METH_UNKNOWN) {
        /* API request over WebSocket */
        *res = json_pack("{s:s s:s s:s s:i}",
                         "@type", "RequestError", "type", type, "title", title,
                         "status", atoi(error_message(http_code)));
    }
    else {
        *res = json_pack("{s:s s:s s:i}", "type", type, "title", title,
                         "status", atoi(error_message(http_code)));
    }
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

    return http_code;
}


HIDDEN int jmap_initreq(jmap_req_t *req)
{
    memset(req, 0, sizeof(struct jmap_req));
    req->mboxes = ptrarray_new();
    return 0;
}

struct _mboxcache_rec {
    struct mailbox *mbox;
    int refcount;
    int rw;
};

HIDDEN void jmap_finireq(jmap_req_t *req)
{
    int i;

    for (i = 0; i < req->mboxes->count; i++) {
        struct _mboxcache_rec *rec = ptrarray_nth(req->mboxes, i);
        syslog(LOG_ERR, "jmap: force-closing mailbox %s (refcount=%d)",
                        rec->mbox->name, rec->refcount);
        mailbox_close(&rec->mbox);
        free(rec);
    }
    /* Fail after cleaning up open mailboxes */
    assert(!req->mboxes->count);

    ptrarray_free(req->mboxes);
    req->mboxes = NULL;

    json_decref(req->perf_details);
    req->perf_details = NULL;
}

static jmap_method_t *find_methodproc(const char *name, hash_table *jmap_methods)
{
    return hash_lookup(name, jmap_methods);
}

/* Return the ACL for mbentry for the authstate of userid.
 * Lookup and store ACL rights in the mboxrights cache. */
static int _rights_for_mbentry(const char *userid,
                               struct auth_state *authstate,
                               const mbentry_t *mbentry,
                               hash_table *mboxrights)
{
    if (!mbentry) return 0;

    /* Lookup cached rights */
    int *rightsptr = hash_lookup(mbentry->name, mboxrights);
    if (rightsptr) return *rightsptr;

    int rights = 0;

    /* Lookup ACL */
    mbname_t *mbname = mbname_from_intname(mbentry->name);
    if (mbentry->mbtype & MBTYPE_INTERMEDIATE) {
        // if it's an intermediate mailbox, we get rights from the parent
        mbentry_t *parententry = NULL;
        if (mboxlist_findparent(mbentry->name, &parententry))
            rights = 0;
        else
            rights = httpd_myrights(authstate, parententry);
        mboxlist_entry_free(&parententry);
    }
    else rights = httpd_myrights(authstate, mbentry);

    /* XXX FastMail workaround: mailbox owner always has ADMIN */
    if (!strcmpsafe(mbname_userid(mbname), userid)) {
        rights |= ACL_ADMIN;
    }

    /* Cache rights */
    rightsptr = xmalloc(sizeof(int));
    *rightsptr = rights;
    hash_insert(mbentry->name, rightsptr, mboxrights);

    mbname_free(&mbname);
    return rights;
}

struct capabilities_rock {
    const char *authuserid;
    hash_table *mboxrights;
    struct auth_state *authstate;

    int is_visible;
    int has_mail;
    int has_contacts;
    int has_calendars;
};

static int capabilities_cb(const mbentry_t *mbentry, void *vrock)
{
    struct capabilities_rock *rock = vrock;

    if (!mbentry) return 0;

    if ((mbentry->mbtype & MBTYPE_DELETED) ||
        (mbentry->mbtype & MBTYPE_MOVING) ||
        (mbentry->mbtype & MBTYPE_REMOTE) ||
        (mbentry->mbtype & MBTYPE_RESERVE)) {
        return 0;
    }

    int rights = _rights_for_mbentry(rock->authuserid, rock->authstate, mbentry, rock->mboxrights);
    if (!(rights & ACL_LOOKUP)) return 0;
    rock->is_visible = 1;

    mbname_t *mbname = mbname_from_intname(mbentry->name);
    const strarray_t *boxes = mbname_boxes(mbname);
    if (!rock->has_mail) {
        rock->has_mail = mbentry->mbtype == MBTYPE_EMAIL;
    }
    if (!rock->has_contacts) {
        rock->has_contacts = strarray_size(boxes) >= 1 &&
            !strcmpsafe(config_getstring(IMAPOPT_ADDRESSBOOKPREFIX),
                    strarray_nth(boxes, 0));
    }
    if (!rock->has_calendars) {
        rock->has_calendars = strarray_size(boxes) >= 1 &&
            !strcmpsafe(config_getstring(IMAPOPT_CALENDARPREFIX),
                    strarray_nth(boxes, 0));
    }
    mbname_free(&mbname);

    return 0;
}

static json_t *lookup_capabilities(const char *accountid,
                                   const char *authuserid,
                                   struct auth_state *authstate,
                                   hash_table *mboxrights)
{
    json_t *capas = json_object();

    if (!strcmp(authuserid, accountid)) {
        /* Primary account has all capabilities */
        jmap_core_capabilities(capas);
        jmap_mail_capabilities(capas);
        jmap_contact_capabilities(capas);
        jmap_calendar_capabilities(capas);
    }
    else {
        /* Lookup capabilities for shared account */
        struct capabilities_rock rock = {
            authuserid, mboxrights, httpd_authstate, 0, 0, 0, 0
        };
        mboxlist_usermboxtree(accountid, authstate, capabilities_cb,
                              &rock, MBOXTREE_INTERMEDIATES);
        if (rock.is_visible) {
            jmap_core_capabilities(capas);
            if (rock.has_mail) {
                jmap_mail_capabilities(capas);
            }
            if (rock.has_contacts) {
                jmap_contact_capabilities(capas);
            }
            if (rock.has_calendars) {
                jmap_calendar_capabilities(capas);
            }
        }
    }

    if (!json_object_size(capas)) {
        json_decref(capas);
        capas = json_null();
    }
    return capas;
}

/* Perform an API request */
HIDDEN int jmap_api(struct transaction_t *txn, json_t **res,
                    jmap_settings_t *settings)
{
    json_t *jreq = NULL, *resp = NULL;
    size_t i;
    int ret, do_perf = 0;
    char *account_inboxname = NULL;
    int return_created_ids = 0;
    hash_table *created_ids = NULL;
    hash_table capabilities_by_accountid = HASH_TABLE_INITIALIZER;
    hash_table mboxrights = HASH_TABLE_INITIALIZER;
    strarray_t methods = STRARRAY_INITIALIZER;
    ptrarray_t method_calls = PTRARRAY_INITIALIZER;
    ptrarray_t processed_methods = PTRARRAY_INITIALIZER;
    strarray_t using_capabilities = STRARRAY_INITIALIZER;

    ret = parse_json_body(txn, &jreq);
    if (ret) return jmap_error_response(txn, ret, res);

    /* Validate Request object */
    if ((ret = validate_request(txn, jreq, settings))) {
        json_decref(jreq);
        return jmap_error_response(txn, ret, res);
    }

    /* Start JSON response */
    resp = json_array();
    if (!resp) {
        txn->error.desc = "Unable to create JSON response body";
        ret = HTTP_SERVER_ERROR;
        goto done;
    }

    /* Set up request-internal state */
    construct_hash_table(&capabilities_by_accountid, 8, 0);
    construct_hash_table(&mboxrights, 64, 0);

    /* Set up creation ids */
    long max_created_ids = (settings->limits[MAX_CALLS_IN_REQUEST] + 1) *
                            settings->limits[MAX_OBJECTS_IN_SET];
    created_ids = xzmalloc(sizeof(hash_table));
    construct_hash_table(created_ids, max_created_ids, 0);

    /* Parse client-supplied creation ids */
    json_t *jcreatedIds = json_object_get(jreq, "createdIds");
    if (json_is_object(jcreatedIds)) {
        return_created_ids = 1;
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
            hash_insert(creation_id, xstrdup(id), created_ids);
        }
    }
    else if (jcreatedIds && jcreatedIds != json_null()) {
        txn->error.desc = "Invalid createdIds argument";
        ret = HTTP_BAD_REQUEST;
        goto done;
    }

    json_t *jusing = json_object_get(jreq, "using");
    for (i = 0; i < json_array_size(jusing); i++) {
        strarray_add(&using_capabilities, json_string_value(json_array_get(jusing, i)));
    }
    /* Push client method calls on call stack */
    json_t *jmethod_calls = json_object_get(jreq, "methodCalls");
    for (i = json_array_size(jmethod_calls); i > 0; i--) {
        json_t *mc = json_array_get(jmethod_calls, i-1);
        ptrarray_push(&method_calls, json_incref(mc));
    }

    /* Process call stack */
    do_perf = strarray_find(&using_capabilities, JMAP_PERFORMANCE_EXTENSION, 0) >= 0;
    json_t *mc;
    while ((mc = ptrarray_pop(&method_calls))) {
        /* Send provisional response, if necessary */
        keepalive_response(txn);

        /* Mark method as processed */
        ptrarray_push(&processed_methods, mc);

        /* Process method */
        const jmap_method_t *mp;
        const char *mname = json_string_value(json_array_get(mc, 0));
        json_t *args = json_array_get(mc, 1);
        const char *tag = json_string_value(json_array_get(mc, 2));
        int r = 0;

        strarray_append(&methods, mname);
        json_incref(args);

        /* Find the message processor */
        mp = find_methodproc(mname, &settings->methods);
        if (!mp || strarray_find(&using_capabilities, mp->capability, 0) < 0) {
            json_array_append_new(resp, json_pack("[s {s:s} s]",
                        "error", "type", "unknownMethod", tag));
            json_decref(args);
            continue;
        }

        /* Validate accountId argument */
        const char *accountid = httpd_userid;
        json_t *err = NULL;
        json_t *arg = json_object_get(args, "accountId");
        if (arg && arg != json_null()) {
            accountid = json_string_value(arg);
        }
        if (!accountid) {
            err = json_pack("{s:s, s:[s]}",
                    "type", "invalidArguments", "arguments", "accountId");
            json_array_append_new(resp, json_pack("[s,o,s]", "error", err, tag));
            json_decref(args);
            continue;
        }

        /* Validate supported capabilities for this account */
        json_t *account_capas = hash_lookup(accountid, &capabilities_by_accountid);
        if (!account_capas) {
            account_capas = lookup_capabilities(accountid, httpd_userid,
                                                httpd_authstate, &mboxrights);
            hash_insert(accountid, account_capas, &capabilities_by_accountid);
        }
        if (json_is_null(account_capas)) {
            err = json_pack("{s:s}", "type", "accountNotFound");
        }
        else if (!json_object_get(account_capas, mp->capability)) {
            err = json_pack("{s:s}", "type", "accountNotSupportedByMethod");
        }
        if (err) {
            json_array_append_new(resp, json_pack("[s,o,s]", "error", err, tag));
            json_decref(args);
            continue;
        }

        /* Pre-process result references */
        if (process_resultrefs(args, resp, &err)) {
            if (!err) err = json_pack("{s:s}", "type", "resultReference");

            json_array_append_new(resp, json_pack("[s,o,s]", "error", err, tag));
            json_decref(args);
            continue;
        }

        struct conversations_state *cstate = NULL;
        r = conversations_open_user(accountid, mp->flags & JMAP_SHARED_CSTATE, &cstate);

        if (r) {
            txn->error.desc = error_message(r);
            ret = HTTP_SERVER_ERROR;
            json_decref(args);
            goto done;
        }

        /* Initialize request context */
        struct jmap_req req;
        jmap_initreq(&req);

        req.method = mname;
        req.userid = httpd_userid;
        req.accountid = accountid;
        req.cstate = cstate;
        req.authstate = httpd_authstate;
        req.args = args;
        req.response = resp;
        req.tag = tag;
        req.created_ids = created_ids;
        req.txn = txn;
        req.mboxrights = &mboxrights;
        req.method_calls = &method_calls;
        req.using_capabilities = &using_capabilities;

        if (do_perf) {
            struct rusage usage;

            getrusage(RUSAGE_SELF, &usage);
            req.user_start = timeval_get_double(&usage.ru_utime);
            req.sys_start = timeval_get_double(&usage.ru_stime);
            req.real_start = now_ms() / 1000.0;
            req.perf_details = json_object();
        }

        /* Read the current state data in */
        account_inboxname = mboxname_user_mbox(accountid, NULL);
        r = mboxname_read_counters(account_inboxname, &req.counters);
        free(account_inboxname);
        account_inboxname = NULL;
        if (r) {
            conversations_abort(&req.cstate);
            txn->error.desc = error_message(r);
            ret = HTTP_SERVER_ERROR;
            jmap_finireq(&req);
            json_decref(args);
            goto done;
        }

        /* Call the message processor. */
        r = mp->proc(&req);

        /* Finalize request context */
        jmap_finireq(&req);

        if (r) {
            conversations_abort(&req.cstate);
            txn->error.desc = error_message(r);
            ret = HTTP_SERVER_ERROR;
            json_decref(args);
            goto done;
        }
        conversations_commit(&req.cstate);

        json_decref(args);
    }

    /* tell syslog which methods were called */
    spool_replace_header(xstrdup(":jmap"),
                         strarray_join(&methods, ","), txn->req_hdrs);


    /* Build response */
    if (txn->meth == METH_UNKNOWN) {
        /* API request over WebSocket */
        *res = json_pack("{s:s s:O}",
                         "@type", "Response", "methodResponses", resp);
    }
    else {
        *res = json_pack("{s:O}", "methodResponses", resp);
    }
    if (return_created_ids) {
        json_t *jcreatedIds = json_object();
        hash_enumerate(created_ids, _make_created_ids, jcreatedIds);
        json_object_set_new(*res, "createdIds", jcreatedIds);
    }
    char *user_inboxname = mboxname_user_mbox(httpd_userid, NULL);
    struct buf state = BUF_INITIALIZER;
    buf_printf(&state, MODSEQ_FMT, mboxname_readraclmodseq(user_inboxname));
    free(user_inboxname);
    json_object_set_new(*res, "sessionState", json_string(buf_cstring(&state)));
    buf_free(&state);

  done:
    {
        /* Clean up call stack */
        json_t *jval;
        while ((jval = ptrarray_pop(&processed_methods)))  {
            json_decref(jval);
        }
        while ((jval = ptrarray_pop(&method_calls))) {
            json_decref(jval);
        }
        ptrarray_fini(&processed_methods);
        ptrarray_fini(&method_calls);
    }
    free_hash_table(created_ids, free);
    free(created_ids);
    if (hash_numrecords(&capabilities_by_accountid)) {
        hash_iter *it = hash_table_iter(&capabilities_by_accountid);
        while (hash_iter_next(it)) {
            json_decref((json_t*)hash_iter_val(it));
        }
        hash_iter_free(&it);
    }
    free_hash_table(&capabilities_by_accountid, NULL);
    free_hash_table(&mboxrights, free);
    free(account_inboxname);
    json_decref(jreq);
    json_decref(resp);
    strarray_fini(&methods);
    strarray_fini(&using_capabilities);

    return ret;
}

struct findaccounts_rock {
    struct buf current_accountid;
    int current_rights;
    json_t *accounts;
    const char *authuserid;
};

static void findaccounts_add(struct findaccounts_rock *rock)
{
    if (!buf_len(&rock->current_accountid))
        return;

    if (!(rock->current_rights & (ACL_LOOKUP|ACL_READ)))
        return;

    const char *accountid = buf_cstring(&rock->current_accountid);
    int is_rw = rock->current_rights & ACL_READ_WRITE;
    int is_primary = !strcmp(rock->authuserid, accountid);

    json_t *account = json_object();
    json_object_set_new(account, "name", json_string(accountid));
    json_object_set_new(account, "isPrimary", json_boolean(is_primary));
    json_object_set_new(account, "isPersonal", json_boolean(is_primary));
    json_object_set_new(account, "isReadOnly", json_boolean(!is_rw));
    json_object_set_new(rock->accounts, accountid, account);
}

static int findaccounts_cb(struct findall_data *data, void *vrock)
{
    if (!data || !data->mbentry) {
        return 0;
    }

    struct findaccounts_rock *rock = vrock;
    const mbentry_t *mbentry = data->mbentry;
    mbname_t *mbname = mbname_from_intname(mbentry->name);

    if (strcmp(buf_cstring(&rock->current_accountid), mbname_userid(mbname))) {
        findaccounts_add(rock);
        buf_setcstr(&rock->current_accountid, mbname_userid(mbname));
        rock->current_rights = 0;
    }
    rock->current_rights |= httpd_myrights(httpd_authstate, data->mbentry);

    mbname_free(&mbname);
    return 0;
}

HIDDEN void jmap_accounts(json_t *accounts, json_t *primary_accounts)
{
    /* Find shared accounts */
    strarray_t patterns = STRARRAY_INITIALIZER;
    char *userpat = xstrdup("user.*");
    userpat[4] = jmap_namespace.hier_sep;
    strarray_append(&patterns, userpat);
    struct findaccounts_rock rock = {
        BUF_INITIALIZER, 0, accounts, httpd_userid
    };
    int r = mboxlist_findallmulti(&jmap_namespace, &patterns, 0, httpd_userid,
                                  httpd_authstate, findaccounts_cb, &rock);
    if (r) {
        syslog(LOG_ERR, "Can't determine shared JMAP accounts for user %s: %s",
                         httpd_userid, error_message(r));
    }
    findaccounts_add(&rock);

    /* Add primary accout */
    buf_setcstr(&rock.current_accountid, httpd_userid);
    rock.current_rights = ACL_FULL;
    findaccounts_add(&rock);

    /* Determine account capabilities */
    hash_table mboxrights = HASH_TABLE_INITIALIZER;
    construct_hash_table(&mboxrights, 64, 0);
    json_t *jaccount;
    const char *accountid;
    json_object_foreach(accounts, accountid, jaccount) {
        json_t *capas = lookup_capabilities(accountid, httpd_userid,
                                            httpd_authstate, &mboxrights);
        json_object_set_new(jaccount, "accountCapabilities", capas);
    }
    free_hash_table(&mboxrights, free);

    json_t *jprimary = json_string(httpd_userid);
    json_object_set(primary_accounts, JMAP_URN_MAIL, jprimary);
    json_object_set(primary_accounts, JMAP_URN_SUBMISSION, jprimary);
    json_object_set(primary_accounts, JMAP_URN_VACATION, jprimary);
    json_object_set(primary_accounts, JMAP_CONTACTS_EXTENSION, jprimary);
    json_object_set(primary_accounts, JMAP_CALENDARS_EXTENSION, jprimary);
    json_decref(jprimary);

    /* Clean up */
    buf_free(&rock.current_accountid);
    free(userpat);
    strarray_fini(&patterns);
}


HIDDEN void jmap_add_subreq(jmap_req_t *req, const char *method,
                            json_t *args, const char *client_id)
{
    if (!client_id) client_id = req->tag;
    ptrarray_push(req->method_calls, json_pack("[s,o,s]", method, args, client_id));
}

const char *jmap_lookup_id(jmap_req_t *req, const char *creation_id)
{
    return hash_lookup(creation_id, req->created_ids);
}

const char *jmap_id_string_value(jmap_req_t *req, json_t *item)
{
    if (!item) return NULL;
    if (!json_is_string(item)) return NULL;
    const char *id = json_string_value(item);
    if (*id == '#')
        return jmap_lookup_id(req, id+1);
    return id;
}

void jmap_add_id(jmap_req_t *req, const char *creation_id, const char *id)
{
    /* It's OK to overwrite existing ids, as per Foo/set:
     * "A client SHOULD NOT reuse a creation id anywhere in the same API
     * request. If a creation id is reused, the server MUST map the creation
     * id to the most recently created item with that id."
     */
    hash_insert(creation_id, xstrdup(id), req->created_ids);
}

HIDDEN int jmap_openmbox(jmap_req_t *req, const char *name,
                         struct mailbox **mboxp, int rw)
{
    int i, r;
    struct _mboxcache_rec *rec;

    for (i = 0; i < req->mboxes->count; i++) {
        rec = (struct _mboxcache_rec*) ptrarray_nth(req->mboxes, i);
        if (!strcmp(name, rec->mbox->name)) {
            if (rw && !rec->rw) {
                /* Lock promotions are not supported */
                syslog(LOG_ERR, "jmapmbox: failed to grab write-lock"
                       " on cached read-only mailbox %s", name);
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

HIDDEN int jmap_isopenmbox(jmap_req_t *req, const char *name)
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

HIDDEN void jmap_closembox(jmap_req_t *req, struct mailbox **mboxp)
{
    struct _mboxcache_rec *rec = NULL;
    int i;

    if (mboxp == NULL || *mboxp == NULL) return;

    for (i = 0; i < req->mboxes->count; i++) {
        rec = (struct _mboxcache_rec*) ptrarray_nth(req->mboxes, i);
        if (rec->mbox == *mboxp) {
            if (!(--rec->refcount)) {
                ptrarray_remove(req->mboxes, i);
                mailbox_close(&rec->mbox);
                free(rec);
            }
            *mboxp = NULL;
            return;
        }
    }
    syslog(LOG_INFO, "jmap: ignoring non-cached mailbox %s", (*mboxp)->name);
}

HIDDEN void jmap_set_blobid(const struct message_guid *guid, char *buf)
{
    buf[0] = 'G';
    memcpy(buf+1, message_guid_encode(guid), 40);
    buf[41] = '\0';
}

HIDDEN void jmap_set_emailid(const struct message_guid *guid, char *buf)
{
    buf[0] = 'M';
    // appends NULL for us
    bin_to_lchex(&guid->value, 12, buf+1);
}

HIDDEN void jmap_set_threadid(conversation_id_t cid, char *buf)
{
    buf[0] = 'T';
    memcpy(buf+1, conversation_id_encode(cid), 16);
    buf[17] = 0;
}

struct findblob_data {
    jmap_req_t *req;
    const char *from_accountid;
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
        (mbname && !strcmp(mbname_userid(mbname), d->from_accountid));
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

HIDDEN int jmap_findblob(jmap_req_t *req, const char *from_accountid,
                         const char *blobid,
                         struct mailbox **mbox, msgrecord_t **mr,
                         struct body **body, const struct body **part,
                         struct buf *blob)
{

    struct findblob_data data = {
        req,
        /* from_accountid */
        from_accountid ? from_accountid : req->accountid, /* from_accountid */
        /* is_shared_account */
        strcmp(req->userid, from_accountid ? from_accountid : req->accountid),
        /* mbox */
        NULL,
        /* mr */
        NULL,
        /* part_id */
        NULL
    };
    struct body *mybody = NULL;
    const struct body *mypart = NULL;
    int i, r;
    struct conversations_state *cstate, *mycstate = NULL;

    if (from_accountid && strcmp(req->accountid, from_accountid)) {
        cstate = conversations_get_user(from_accountid);
        if (!cstate) {
            r = conversations_open_user(from_accountid, 1/*shared*/, &mycstate);
            if (r) goto done;

            cstate = mycstate;
        }
    }
    else {
        cstate = req->cstate;
    }

    if (blobid[0] != 'G')
        return IMAP_NOTFOUND;

    r = conversations_guid_foreach(cstate, blobid+1, findblob_cb, &data);
    if (r != IMAP_OK_COMPLETED) {
        if (!r) r = IMAP_NOTFOUND;
        goto done;
    }

    r = msgrecord_extract_bodystructure(data.mr, &mybody);
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
    if (mycstate) {
        conversations_commit(&mycstate);
    }
    if (r) {
        if (data.mbox) jmap_closembox(req, &data.mbox);
        if (mybody) message_free_body(mybody);
    }
    if (data.part_id) free(data.part_id);
    return r;
}


HIDDEN int jmap_cmpstate(jmap_req_t* req, json_t *state, int mbtype)
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

HIDDEN modseq_t jmap_highestmodseq(jmap_req_t *req, int mbtype)
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

HIDDEN json_t* jmap_getstate(jmap_req_t *req, int mbtype, int refresh)
{
    char *inboxname = mboxname_user_mbox(req->accountid, NULL);
    if (refresh)
        assert (!mboxname_read_counters(inboxname, &req->counters));
    struct buf buf = BUF_INITIALIZER;
    json_t *state = NULL;
    modseq_t modseq = jmap_highestmodseq(req, mbtype);

    buf_printf(&buf, MODSEQ_FMT, modseq);
    state = json_string(buf_cstring(&buf));
    buf_free(&buf);

    free(inboxname);
    return state;
}


HIDDEN json_t *jmap_fmtstate(modseq_t modseq)
{
    struct buf buf = BUF_INITIALIZER;
    json_t *state = NULL;
    buf_printf(&buf, MODSEQ_FMT, modseq);
    state = json_string(buf_cstring(&buf));
    buf_free(&buf);
    return state;
}

HIDDEN char *jmap_xhref(const char *mboxname, const char *resource)
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

HIDDEN int jmap_myrights(jmap_req_t *req, const mbentry_t *mbentry)
{
    return _rights_for_mbentry(req->userid, req->authstate, mbentry, req->mboxrights);
}

// gotta have them all
HIDDEN int jmap_hasrights(jmap_req_t *req, const mbentry_t *mbentry, int rights)
{
    int myrights = jmap_myrights(req, mbentry);
    if ((myrights & rights) == rights) return 1;
    return 0;
}

HIDDEN int jmap_myrights_byname(jmap_req_t *req, const char *mboxname)
{
    int *rightsptr = hash_lookup(mboxname, req->mboxrights);
    if (rightsptr) return *rightsptr;

    // if unable to read, that means no rights
    int rights = 0;

    mbentry_t *mbentry = NULL;
    if (!jmap_mboxlist_lookup(mboxname, &mbentry, NULL)) {
        rights = _rights_for_mbentry(req->userid, req->authstate, mbentry, req->mboxrights);
    }
    mboxlist_entry_free(&mbentry);

    return rights;
}

// gotta have them all
HIDDEN int jmap_hasrights_byname(jmap_req_t *req, const char *mboxname,
                                 int rights)
{
    int myrights = jmap_myrights_byname(req, mboxname);
    if ((myrights & rights) == rights) return 1;
    return 0;
}

HIDDEN void jmap_myrights_delete(jmap_req_t *req, const char *mboxname)
{
    int *rightsptr = hash_del(mboxname, req->mboxrights);
    free(rightsptr);
}

/* Add performance stats to method response */
static void jmap_add_perf(jmap_req_t *req, json_t *res)
{
    struct rusage usage;

    getrusage(RUSAGE_SELF, &usage);

    json_t *perf = json_pack("{s:f s:f s:f}",
            "real", (now_ms() / 1000.0) - req->real_start,
            "user", timeval_get_double(&usage.ru_utime) - req->user_start,
            "sys", timeval_get_double(&usage.ru_stime) - req->sys_start);
    json_object_set(perf, "details", req->perf_details); // incref

    json_object_set_new(res, "performance", perf);
}

HIDDEN void jmap_parser_fini(struct jmap_parser *parser)
{
    strarray_fini(&parser->path);
    json_decref(parser->invalid);
    buf_free(&parser->buf);
}

HIDDEN void jmap_parser_push(struct jmap_parser *parser, const char *prop)
{
    strarray_push(&parser->path, prop);
}

HIDDEN void jmap_parser_push_index(struct jmap_parser *parser, const char *prop,
                                   size_t index, const char *name)
{
    /* TODO make this more clever: won't need to printf most of the time */
    buf_reset(&parser->buf);
    if (name) buf_printf(&parser->buf, "%s[%zu:%s]", prop, index, name);
    else buf_printf(&parser->buf, "%s[%zu]", prop, index);
    strarray_push(&parser->path, buf_cstring(&parser->buf));
    buf_reset(&parser->buf);
}

HIDDEN void jmap_parser_push_name(struct jmap_parser *parser,
                                  const char *prop, const char *name)
{
    /* TODO make this more clever: won't need to printf most of the time */
    buf_reset(&parser->buf);
    buf_printf(&parser->buf, "%s{%s}", prop, name);
    strarray_push(&parser->path, buf_cstring(&parser->buf));
    buf_reset(&parser->buf);
}

HIDDEN void jmap_parser_pop(struct jmap_parser *parser)
{
    free(strarray_pop(&parser->path));
}

HIDDEN const char* jmap_parser_path(struct jmap_parser *parser, struct buf *buf)
{
    int i;
    buf_reset(buf);

    for (i = 0; i < parser->path.count; i++) {
        const char *p = strarray_nth(&parser->path, i);
        if (jmap_pointer_needsencode(p)) {
            char *tmp = jmap_pointer_encode(p);
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

HIDDEN void jmap_parser_invalid(struct jmap_parser *parser, const char *prop)
{
    if (prop)
        jmap_parser_push(parser, prop);

    json_array_append_new(parser->invalid,
            json_string(jmap_parser_path(parser, &parser->buf)));

    if (prop)
        jmap_parser_pop(parser);
}

HIDDEN void jmap_ok(jmap_req_t *req, json_t *res)
{
    json_object_set_new(res, "accountId", json_string(req->accountid));

    json_t *item = json_pack("[]");
    json_array_append_new(item, json_string(req->method));
    json_array_append_new(item, res);
    json_array_append_new(item, json_string(req->tag));
    json_array_append_new(req->response, item);

    if (jmap_is_using(req, JMAP_PERFORMANCE_EXTENSION))
        jmap_add_perf(req, res);
}

HIDDEN void jmap_error(jmap_req_t *req, json_t *err)
{
    json_array_append_new(req->response,
            json_pack("[s,o,s]", "error", err, req->tag));
}

HIDDEN json_t *jmap_server_error(int r)
{
    return json_pack("{s:s, s:s}",
                     "type", "serverError",
                     "description", error_message(r));
}


HIDDEN int jmap_parse_strings(json_t *arg,
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


HIDDEN const jmap_property_t *jmap_property_find(const char *name,
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

HIDDEN void jmap_get_parse(jmap_req_t *req,
                           struct jmap_parser *parser,
                           const jmap_property_t valid_props[],
                           int allow_null_ids,
                           jmap_args_parse_cb args_parse,
                           void *args_rock,
                           struct jmap_get *get,
                           json_t **err)
{
    json_t *jargs = req->args;
    const char *key;
    json_t *arg, *val;
    size_t i;

    memset(get, 0, sizeof(struct jmap_get));

    get->list = json_array();
    get->not_found = json_array();

    json_object_foreach(jargs, key, arg) {
        if (!strcmp(key, "accountId")) {
            /* already handled in jmap_api() */
        }

        else if (!strcmp(key, "ids")) {
            if (json_is_array(arg)) {
                get->ids = json_array();
                /* JMAP spec requires: "If an identical id is included
                 * more than once in the request, the server MUST only
                 * include it once in either the list or notFound
                 * argument of the response."
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
                            json_array_append_new(get->not_found,
                                                  json_string(id));
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
        }

        else if (!strcmp(key, "properties")) {
            if (json_is_array(arg)) {
                get->props = xzmalloc(sizeof(hash_table));
                construct_hash_table(get->props, json_array_size(arg) + 1, 0);
                json_array_foreach(arg, i, val) {
                    const char *name = json_string_value(val);
                    const jmap_property_t *propdef = NULL;
                    if (name) {
                        propdef = jmap_property_find(name, valid_props);
                        if (propdef && propdef->capability &&
                            !jmap_is_using(req, propdef->capability)) {
                            propdef = NULL;
                        }
                    }
                    if (!propdef) {
                        jmap_parser_push_index(parser, "properties", i, name);
                        jmap_parser_invalid(parser, NULL);
                        jmap_parser_pop(parser);
                        continue;
                    }
                    hash_insert(name, (void*)1, get->props);
                }
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "properties");
            }
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
        return;
    }

    if (!allow_null_ids && !JNOTNULL(get->ids)) {
        *err = json_pack("{s:s, s:s}", "type", "requestTooLarge",
                         "description", "ids must be specified");
        return;
    }

    if (*err) return;

    if (get->props == NULL) {
        /* Initialize default properties */
        int nvalid = 0;
        const jmap_property_t *prop;
        for (prop = valid_props; prop && prop->name; prop++) {
            nvalid++;
        }
        get->props = xzmalloc(sizeof(hash_table));
        construct_hash_table(get->props, nvalid + 1, 0);
        for (prop = valid_props; prop && prop->name; prop++) {
            if (prop->flags & JMAP_PROP_SKIP_GET) {
                continue;
            }
            if (!prop->capability || jmap_is_using(req, prop->capability)) {
                hash_insert(prop->name, (void*)1, get->props);
            }
        }
    }
    else {
        const jmap_property_t *prop;
        for (prop = valid_props; prop && prop->name; prop++) {
            if (prop->flags & JMAP_PROP_ALWAYS_GET) {
                if (!hash_lookup(prop->name, get->props)) {
                    hash_insert(prop->name, (void*)1, get->props);
                }
            }
        }
    }

    /* Number of ids checked in validate_request() */ 
}

HIDDEN void jmap_get_fini(struct jmap_get *get)
{
    free_hash_table(get->props, NULL);
    free(get->props);
    free(get->state);
    json_decref(get->ids);
    json_decref(get->list);
    json_decref(get->not_found);
}

HIDDEN json_t *jmap_get_reply(struct jmap_get *get)
{
    json_t *res = json_object();
    json_object_set_new(res, "state", json_string(get->state));
    json_object_set(res, "list", get->list);
    json_object_set(res, "notFound", get->not_found);
    return res;
}


/* Foo/set */

static void jmap_set_validate_props(jmap_req_t *req, json_t *jobj,
                                    const jmap_property_t valid_props[],
                                    json_t **err)
{
    json_t *invalid = json_array();
    const char *path;
    json_t *jval;

    json_object_foreach(jobj, path, jval) {
        /* Determine property name */
        const char *pname = path;
        char *tmp = NULL;
        const char *slash = strchr(pname, '/');
        if (slash) {
            tmp = jmap_pointer_decode(pname, slash - path);
            if (tmp) pname = tmp;
        }
        /* Validate against property spec */
        const jmap_property_t *prop = jmap_property_find(pname, valid_props);
        if (!prop) {
            json_array_append_new(invalid, json_string(path));
        }
        else if (prop->capability && !jmap_is_using(req, prop->capability)) {
            json_array_append_new(invalid, json_string(path));
        }
        /* XXX could check IMMUTABLE and SERVER_SET here, but we can't
         * reject such properties if they match the current value */
        if (tmp) free(tmp);
    }
    if (json_array_size(invalid)) {
        *err = json_pack("{s:s s:o}",
                "type", "invalidProperties",
                "properties", invalid);
    }
    else {
        json_decref(invalid);
    }
}

HIDDEN void jmap_set_parse(jmap_req_t *req, struct jmap_parser *parser,
                           const jmap_property_t valid_props[],
                           jmap_args_parse_cb args_parse, void *args_rock,
                           struct jmap_set *set, json_t **err)
{
    json_t *jargs = req->args;
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

    const char *key;
    json_t *arg, *val;

    json_object_foreach(jargs, key, arg) {
        if (!strcmp(key, "accountId")) {
            /* already handled in jmap_api() */
        }

        /* ifInState */
        else  if (!strcmp(key, "ifInState")) {
            if (json_is_string(arg)) {
                set->if_in_state = json_string_value(arg);
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "ifInState");
            }
        }

        /* create */
        else if (!strcmp(key, "create")) {
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
        }

        /* update */
        else if (!strcmp(key, "update")) {
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
        }

        /* destroy */
        else if (!strcmp(key, "destroy")) {
            if (JNOTNULL(arg)) {
                jmap_parse_strings(arg, parser, "destroy");
                if (!json_array_size(parser->invalid)) {
                    json_decref(set->destroy);
                    set->destroy = json_incref(arg);
                }
            }
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }

    if (valid_props) {
        json_t *jval;
        /* Make sure no property is set without its capability */
        json_object_foreach(json_object_get(jargs, "create"), key, jval) {
            json_t *err = NULL;
            jmap_set_validate_props(req, jval, valid_props, &err);
            if (err) {
                json_object_del(set->create, key);
                json_object_set_new(set->not_created, key, err);
            }
        }
        json_object_foreach(json_object_get(jargs, "update"), key, jval) {
            json_t *err = NULL;
            jmap_set_validate_props(req, jval, valid_props, &err);
            if (err) {
                json_object_del(set->update, key);
                json_object_set_new(set->not_updated, key, err);
            }
        }
        // TODO We could report the following set errors here:
        // -invalidPatch
        // - willDestroy
    }
}


HIDDEN void jmap_set_fini(struct jmap_set *set)
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

HIDDEN json_t *jmap_set_reply(struct jmap_set *set)
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

HIDDEN void jmap_changes_parse(jmap_req_t *req,
                               struct jmap_parser *parser,
                               jmap_args_parse_cb args_parse,
                               void *args_rock,
                               struct jmap_changes *changes,
                               json_t **err)
{
    json_t *jargs = req->args;
    const char *key;
    json_t *arg;

    memset(changes, 0, sizeof(struct jmap_changes));
    changes->created = json_array();
    changes->updated = json_array();
    changes->destroyed = json_array();

    json_object_foreach(jargs, key, arg) {
        if (!strcmp(key, "accountId")) {
            /* already handled in jmap_api() */
        }

        /* sinceState */
        else if (!strcmp(key, "sinceState")) {
            if (json_is_string(arg)) {
                changes->since_modseq = atomodseq_t(json_string_value(arg));
            }
            else {
                jmap_parser_invalid(parser, "sinceState");
            }
        }

        /* maxChanges */
        else if (!strcmp(key, "maxChanges")) {
            if (json_is_integer(arg) && json_integer_value(arg) > 0) {
                changes->max_changes = json_integer_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "maxChanges");
            }
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }
    else if (!changes->since_modseq) {
        *err = json_pack("{s:s}", "type", "cannotCalculateChanges");
    }
}

HIDDEN void jmap_changes_fini(struct jmap_changes *changes)
{
    json_decref(changes->created);
    json_decref(changes->updated);
    json_decref(changes->destroyed);
}

HIDDEN json_t *jmap_changes_reply(struct jmap_changes *changes)
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


/* Foo/copy */

HIDDEN void jmap_copy_parse(jmap_req_t *req, struct jmap_parser *parser,
                            jmap_args_parse_cb args_parse, void *args_rock,
                            struct jmap_copy *copy, json_t **err)
{
    json_t *jargs = req->args;

    memset(copy, 0, sizeof(struct jmap_copy));
    copy->blob_copy = !strcmp(req->method, "Blob/copy");
    copy->create = copy->blob_copy ? json_array() : json_object();
    copy->created = json_object();
    copy->not_created = json_object();

    const char *key;
    json_t *arg;

    json_object_foreach(jargs, key, arg) {
        /* fromAccountId */
        if (!strcmp(key, "fromAccountId")) {
            if (json_is_string(arg)) {
                copy->from_account_id = json_string_value(arg);
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "fromAccountId");
            }
        }

        /* accountId */
        else if (!strcmp(key, "accountId")) {
            /* JMAP request parser already set it */
            assert(req->accountid);
            continue;
        }

        /* blobIds */
        else if (copy->blob_copy &&
                 !strcmp(key, "blobIds") && json_is_array(arg)) {
            struct buf buf = BUF_INITIALIZER;
            json_t *id;
            size_t i;
            json_array_foreach(arg, i, id) {
                if (!json_is_string(id)) {
                    buf_printf(&buf, "blobIds[%zu]", i);
                    jmap_parser_invalid(parser, buf_cstring(&buf));
                    buf_reset(&buf);
                }
                else json_array_append(copy->create, id);
            }
        }

        /* create */
        else if (!copy->blob_copy &&
                 !strcmp(key, "create") && json_is_object(arg)) {
            jmap_parser_push(parser, "create");
            const char *creation_id;
            json_t *obj;
            json_object_foreach(arg, creation_id, obj) {
                if (!json_is_object(obj)) {
                    jmap_parser_invalid(parser, creation_id);
                }
                else if (!json_is_string(json_object_get(obj, "id"))) {
                    jmap_parser_push(parser, creation_id);
                    jmap_parser_invalid(parser, "id");
                    jmap_parser_pop(parser);
                }
                else json_object_set(copy->create, creation_id, obj);
            }
            jmap_parser_pop(parser);
        }

        /* onSuccessDestroyOriginal */
        else if (!copy->blob_copy && !strcmp(key, "onSuccessDestroyOriginal") &&
                 json_is_boolean(arg)) {
            copy->on_success_destroy_original = json_boolean_value(arg);
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
    }

    if (json_array_size(parser->invalid)) {
        *err = json_pack("{s:s s:O}", "type", "invalidArguments",
                "arguments", parser->invalid);
    }

    if (!req->accountid || !copy->from_account_id ||
        !strcmp(req->accountid, copy->from_account_id)) {
        *err = json_pack("{s:s s:[s,s]}", "type", "invalidArguments",
                "arguments", "accountId", "fromAccountId");
    }
}


HIDDEN void jmap_copy_fini(struct jmap_copy *copy)
{
    json_decref(copy->create);
    json_decref(copy->created);
    json_decref(copy->not_created);
}

HIDDEN json_t *jmap_copy_reply(struct jmap_copy *copy)
{
    json_t *res = json_object();
    json_object_set_new(res, "fromAccountId",
                        json_string(copy->from_account_id));
    json_object_set(res, copy->blob_copy ? "copied" : "created",
                    json_object_size(copy->created) ?
                    copy->created : json_null());
    json_object_set(res, copy->blob_copy ? "notCopied" : "notCreated",
                    json_object_size(copy->not_created) ?
                    copy->not_created : json_null());
    return res;
}


/* Foo/query */

HIDDEN void jmap_filter_parse(jmap_req_t *req, struct jmap_parser *parser,
                              json_t *filter, json_t *unsupported,
                              jmap_filter_parse_cb parse_condition, void *cond_rock)
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
            jmap_filter_parse(req, parser, val, unsupported, parse_condition, cond_rock);
            jmap_parser_pop(parser);
        }
    } else if (arg) {
        jmap_parser_invalid(parser, "operator");
    } else {
        parse_condition(req, parser, filter, unsupported, cond_rock);
    }
}

HIDDEN void jmap_comparator_parse(jmap_req_t *req, struct jmap_parser *parser,
                                  json_t *jsort, json_t *unsupported,
                                  jmap_comparator_parse_cb comp_cb, void *comp_rock)
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


    if (comp.property && !comp_cb(req, &comp, comp_rock)) {
        struct buf buf = BUF_INITIALIZER;
        json_array_append_new(unsupported,
                json_string(jmap_parser_path(parser, &buf)));
        buf_free(&buf);
    }
}

HIDDEN void jmap_query_parse(jmap_req_t *req, struct jmap_parser *parser,
                             jmap_args_parse_cb args_parse, void *args_rock,
                             jmap_filter_parse_cb filter_cb, void *filter_rock,
                             jmap_comparator_parse_cb comp_cb, void *comp_rock,
                             struct jmap_query *query, json_t **err)
{
    json_t *jargs = req->args;
    const char *key;
    json_t *arg, *val;
    size_t i;

    memset(query, 0, sizeof(struct jmap_query));
    query->ids = json_array();

    json_t *unsupported_filter = json_array();
    json_t *unsupported_sort = json_array();

    json_object_foreach(jargs, key, arg) {
        if (!strcmp(key, "accountId")) {
            /* already handled in jmap_api() */
        }

        /* filter */
        else if (!strcmp(key, "filter")) {
            if (json_is_object(arg)) {
                jmap_parser_push(parser, "filter");
                jmap_filter_parse(req, parser, arg, unsupported_filter,
                                  filter_cb, filter_rock);
                jmap_parser_pop(parser);
                query->filter = arg;
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "filter");
            }
        }

        /* sort */
        else if (!strcmp(key, "sort")) {
            if (json_is_array(arg)) {
                json_array_foreach(arg, i, val) {
                    jmap_parser_push_index(parser, "sort", i, NULL);
                    jmap_comparator_parse(req, parser, val, unsupported_sort,
                                          comp_cb, comp_rock);
                    jmap_parser_pop(parser);
                }
                if (json_array_size(arg)) {
                    query->sort = arg;
                }
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "sort");
            }
        }

        else if (!strcmp(key, "position")) {
            if (json_is_integer(arg)) {
                query->position = json_integer_value(arg);
            }
            else if (arg) {
                jmap_parser_invalid(parser, "position");
            }
        }

        else if (!strcmp(key, "anchor")) {
            if (json_is_string(arg)) {
                query->anchor = json_string_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "anchor");
            }
        }

        else if (!strcmp(key, "anchorOffset")) {
            if (json_is_integer(arg)) {
                query->anchor_offset = json_integer_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "anchorOffset");
            }
        }

        else if (!strcmp(key, "limit")) {
            if (json_is_integer(arg) && json_integer_value(arg) >= 0) {
                query->limit = json_integer_value(arg);
                query->have_limit = 1;
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "limit");
            }
        }

        else if (!strcmp(key, "calculateTotal")) {
            if (json_is_boolean(arg)) {
                query->calculate_total = json_boolean_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "calculateTotal");
            }
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
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

HIDDEN void jmap_query_fini(struct jmap_query *query)
{
    free(query->query_state);
    json_decref(query->ids);
}

HIDDEN json_t *jmap_query_reply(struct jmap_query *query)
{

    json_t *res = json_object();
    json_object_set(res, "filter", query->filter);
    json_object_set(res, "sort", query->sort);
    json_object_set_new(res, "queryState", json_string(query->query_state));
    json_object_set_new(res, "canCalculateChanges",
                        json_boolean(query->can_calculate_changes));
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


/* Foo/queryChanges */

HIDDEN void jmap_querychanges_parse(jmap_req_t *req,
                                    struct jmap_parser *parser,
                                    jmap_args_parse_cb args_parse, void *args_rock,
                                    jmap_filter_parse_cb filter_cb, void *filter_rock,
                                    jmap_comparator_parse_cb comp_cb, void *comp_rock,
                                    struct jmap_querychanges *query,
                                    json_t **err)
{
    json_t *jargs = req->args;
    const char *key;
    json_t *arg, *val;
    size_t i;

    memset(query, 0, sizeof(struct jmap_querychanges));
    query->removed = json_array();
    query->added = json_array();

    json_t *unsupported_filter = json_array();
    json_t *unsupported_sort = json_array();

    json_object_foreach(jargs, key, arg) {
        if (!strcmp(key, "accountId")) {
            /* already handled in jmap_api() */
        }

        /* filter */
        else if (!strcmp(key, "filter")) {
            if (json_is_object(arg)) {
                jmap_parser_push(parser, "filter");
                jmap_filter_parse(req, parser, arg, unsupported_filter,
                                  filter_cb, filter_rock);
                jmap_parser_pop(parser);
                query->filter = arg;
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "filter");
            }
        }

        /* sort */
        else if (!strcmp(key, "sort")) {
            if (json_is_array(arg)) {
                json_array_foreach(arg, i, val) {
                    jmap_parser_push_index(parser, "sort", i, NULL);
                    jmap_comparator_parse(req, parser, val, unsupported_sort,
                                          comp_cb, comp_rock);
                    jmap_parser_pop(parser);
                }
                if (json_array_size(arg)) {
                    query->sort = arg;
                }
            }
            else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "sort");
            }
        }

        /* sinceQueryState */
        else if (!strcmp(key, "sinceQueryState")) {
            if (json_is_string(arg)) {
                query->since_querystate = json_string_value(arg);
            } else {
                jmap_parser_invalid(parser, "sinceQueryState");
            }
        }

        /* maxChanges */
        else if (!strcmp(key, "maxChanges")) {
            if (json_is_integer(arg) && json_integer_value(arg) > 0) {
                query->max_changes = json_integer_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "maxChanges");
            }
        }

        /* upToId */
        else if (!strcmp(key, "upToId")) {
            if (json_is_string(arg)) {
                query->up_to_id = json_string_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "upToId");
            }
        }

        /* calculateTotal */
        else if (!strcmp(key, "calculateTotal")) {
            if (json_is_boolean(arg)) {
                query->calculate_total = json_boolean_value(arg);
            } else if (JNOTNULL(arg)) {
                jmap_parser_invalid(parser, "calculateTotal");
            }
        }

        else if (!args_parse || !args_parse(req, parser, key, arg, args_rock)) {
            jmap_parser_invalid(parser, key);
        }
    }

    if (query->since_querystate == NULL) {
        jmap_parser_invalid(parser, "sinceQueryState");
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

HIDDEN void jmap_querychanges_fini(struct jmap_querychanges *query)
{
    free(query->new_querystate);
    json_decref(query->removed);
    json_decref(query->added);
}

HIDDEN json_t *jmap_querychanges_reply(struct jmap_querychanges *query)
{
    json_t *res = json_object();
    json_object_set(res, "filter", query->filter);
    json_object_set(res, "sort", query->sort);
    json_object_set_new(res, "oldQueryState",
                        json_string(query->since_querystate));
    json_object_set_new(res, "newQueryState",
                        json_string(query->new_querystate));
    json_object_set_new(res, "upToId", query->up_to_id ?
            json_string(query->up_to_id) : json_null());
    json_object_set(res, "removed", query->removed);
    json_object_set(res, "added", query->added);
    json_object_set_new(res, "total", json_integer(query->total));
    return res;
}

static json_t *_json_has(int rights, int need)
{
  return (((rights & need) == need) ? json_true() : json_false());
}

/* create, update, delete */
#define WRITERIGHTS  (ACL_WRITE|ACL_INSERT|ACL_SETSEEN|ACL_DELETEMSG|ACL_EXPUNGE|ACL_ANNOTATEMSG)

HIDDEN json_t *jmap_get_sharewith(const mbentry_t *mbentry)
{
    char *aclstr = xstrdup(mbentry->acl);
    char *owner = mboxname_to_userid(mbentry->name);
    int iscalendar = (mbentry->mbtype & MBTYPE_CALENDAR);

    json_t *sharewith = json_null();

    char *userid;
    char *nextid;
    for (userid = aclstr; userid; userid = nextid) {
        int rights;
        char *rightstr;

        rightstr = strchr(userid, '\t');
        if (!rightstr) break;
        *rightstr++ = '\0';

        nextid = strchr(rightstr, '\t');
        if (!nextid) break;
        *nextid++ = '\0';

        cyrus_acl_strtomask(rightstr, &rights);

        // skip system users and owner
        if (is_system_user(userid)) continue;
        if (!strcmp(userid, owner)) continue;

        // we've got one! Create the object if this is the first
        if (!JNOTNULL(sharewith))
            sharewith = json_pack("{}");

        json_t *obj = json_pack("{}");
        json_object_set_new(sharewith, userid, obj);

        if (iscalendar)
            json_object_set_new(obj, "mayReadFreeBusy",
                                _json_has(rights, DACL_READFB));
        json_object_set_new(obj, "mayRead",
                                _json_has(rights, ACL_READ|ACL_LOOKUP));
        json_object_set_new(obj, "mayWrite",
                                _json_has(rights, WRITERIGHTS));
        json_object_set_new(obj, "mayAdmin",
                                _json_has(rights, ACL_ADMIN));
    }

    free(aclstr);
    free(owner);

    return sharewith;
}

struct acl_change {
    int old;
    int new;
};

struct invite_rock {
    xmlNodePtr notify;
    xmlNsPtr ns[NUM_NAMESPACE];
    struct buf resource;
    struct request_target_t tgt;
    const struct prop_entry *live_props;
};


/* Create and send a sharing invite */
static void send_dav_invite(const char *userid, void *val, void *rock)
{
    struct acl_change *change = (struct acl_change *) val;
    struct invite_rock *irock = (struct invite_rock *) rock;
    long old = change->old & (ACL_READ|ACL_LOOKUP|WRITERIGHTS);
    long new = change->new & (ACL_READ|ACL_LOOKUP|WRITERIGHTS);

    if (old != new) {
        int access, r;

        if (!new) access = SHARE_NONE;
        else if (new & WRITERIGHTS) access = SHARE_READWRITE;
        else access = SHARE_READONLY;

        /* Notify sharee */
        r = dav_create_invite(&irock->notify, irock->ns, &irock->tgt,
                              irock->live_props, userid, access,
                              BAD_CAST "Shared via JMAP");
        if (!r) {
            /* Create a resource name for the notifications -
               We use a consistent naming scheme so that multiple
               notifications of the same type for the same resource
               are coalesced (overwritten) */
            buf_reset(&irock->resource);
            buf_printf(&irock->resource, "%x-%x-%x-%x.xml",
                       strhash(XML_NS_DAV),
                       strhash(SHARE_INVITE_NOTIFICATION),
                       strhash(irock->tgt.mbentry->name),
                       strhash(userid));

            r = dav_send_notification(irock->notify->doc,
                                      userid, buf_cstring(&irock->resource));
        }
    }
}

HIDDEN int jmap_set_sharewith(struct mailbox *mbox,
                              json_t *shareWith, int overwrite)
{
    hash_table user_access = HASH_TABLE_INITIALIZER;
    int isdav = (mbox->mbtype & MBTYPES_DAV), iscalendar = 0;
    char *owner = mboxname_to_userid(mbox->name);
    char *acl = xstrdup(mbox->acl);
    struct acl_change *change;
    const char *userid;
    json_t *rights;
    int r;

    if (json_is_null(shareWith)) overwrite = 1;

    if (isdav) {
        /* Create a hash table of user/access for DAV invites */
        iscalendar = (mbox->mbtype & MBTYPE_CALENDAR);
        construct_hash_table(&user_access, 10, 0);
    }

    if (isdav || overwrite) {
        /* If DAV: Populate a table of existing users and their access.
           If overwrite: Create a new ACL with only
                         existing owner and system users preserved.
        */
        char *newacl, *nextid;

        if (overwrite) newacl = xstrdup("");  /* start with empty ACL */

        for (userid = acl; userid; userid = nextid) {
            char *rightstr;
            int access;

            rightstr = strchr(userid, '\t');
            if (!rightstr) break;
            *rightstr++ = '\0';

            nextid = strchr(rightstr, '\t');
            if (!nextid) break;
            *nextid++ = '\0';

            /* Is this the owner or system user? */
            if (strcmp(userid, owner) && !is_system_user(userid)) {
                if (isdav) {
                    /* Add regular user to our table */
                    change = xzmalloc(sizeof(struct acl_change));

                    cyrus_acl_strtomask(rightstr, &change->old);
                    hash_insert(userid, (void *) change, &user_access);
                }
            }
            else if (overwrite) {
                /* Add owner or system user to new ACL */
                cyrus_acl_strtomask(rightstr, &access);

                r = cyrus_acl_set(&newacl, userid,
                                  ACL_MODE_SET, access, NULL, NULL);
                if (r) {
                    syslog(LOG_ERR, "cyrus_acl_set(%s, %s) failed: %s",
                           mbox->name, userid, error_message(r));
                    free(newacl);
                    goto done;
                }
            }
        }

        free(acl);
        acl = overwrite ? newacl : xstrdup(mbox->acl);
    }

    /* Patch the ACL from shareWith */
    json_object_foreach(shareWith, userid, rights) {
        unsigned grant = 0, deny = 0;
        const char *right;
        json_t *val;

        /* Validate user id and rights */
        if (!(strlen(userid) && rights &&
              (json_is_object(rights) || json_is_null(rights)))) {
            continue;
        }

        /* skip system users and owner */
        if (is_system_user(userid)) continue;
        if (!strcmp(userid, owner)) continue;

        if (json_is_null(rights)) {
            /* remove user from ACL */
            r = cyrus_acl_remove(&acl, userid, NULL, NULL);
            if (r) {
                syslog(LOG_ERR, "cyrus_acl_remove(%s, %s) failed: %s",
                       mbox->name, userid, error_message(r));
                goto done;
            }
            if (isdav && (change = hash_lookup(userid, &user_access)))
                change->new = 0;
        }
        else {
            /* accumulate rights be granted and denied */
            json_object_foreach(rights, right, val) {
                unsigned access = 0;

                if (!strcmp(right, "mayAdmin"))
                    access = ACL_ADMIN;
                else if (!strcmp(right, "mayWrite"))
                    access = WRITERIGHTS;
                else if (!strcmp(right, "mayRead"))
                    access = ACL_READ|ACL_LOOKUP|ACL_SETSEEN;
                else if (iscalendar && !strcmp(right, "mayReadFreeBusy"))
                    access = DACL_READFB;

                if (json_boolean_value(val)) grant |= access;
                else deny |= access;
            }

            r = cyrus_acl_set(&acl, userid, ACL_MODE_ADD, grant, NULL, NULL);
            if (!r) {
                r = cyrus_acl_set(&acl, userid,
                                  ACL_MODE_REMOVE, deny, NULL, NULL);
            }
            if (r) {
                syslog(LOG_ERR, "cyrus_acl_set(%s, %s) failed: %s",
                       mbox->name, userid, error_message(r));
                goto done;
            }

            if (isdav) {
                change = hash_lookup(userid, &user_access);
                if (!change) {
                    change = xzmalloc(sizeof(struct acl_change));
                    hash_insert(userid, (void *) change, &user_access);
                }
                change->new = change->old | grant;
                change->new &= ~deny;
            }
        }
    }

    /* ok, change the mailboxes database */
    r = mboxlist_sync_setacls(mbox->name, acl);
    if (r) {
        syslog(LOG_ERR, "mboxlist_sync_setacls(%s) failed: %s",
               mbox->name, error_message(r));
    }
    else {
        /* ok, change the backup in cyrus.header */
        r = mailbox_set_acl(mbox, acl, 1 /*dirty_modseq*/);
        if (r) {
            syslog(LOG_ERR, "mailbox_set_acl(%s) failed: %s",
                   mbox->name, error_message(r));
        }
    }

    if (!r && isdav) {
        /* Send sharing invites */
        struct invite_rock irock;
        struct meth_params *pparams;
        mbname_t *mbname;
        const char *errstr = NULL;

        memset(&irock, 0, sizeof(struct invite_rock));

        /* Find the DAV namespace for this mailbox */
        if (iscalendar)
            irock.tgt.namespace = &namespace_calendar;
        else if (mbox->mbtype & MBTYPE_ADDRESSBOOK)
            irock.tgt.namespace = &namespace_addressbook;
        else
            irock.tgt.namespace = &namespace_drive;

        /* Get "live" properties for the namespace */
        pparams = irock.tgt.namespace->methods[METH_PROPFIND].params;
        irock.live_props = pparams->propfind.lprops;

        /* Create DAV URL for this collection */
        mbname = mbname_from_intname(mbox->name);
        if (!mbname_domain(mbname)) mbname_set_domain(mbname, httpd_extradomain);

        make_collection_url(&irock.resource, irock.tgt.namespace->prefix,
                            /*haszzzz*/0, mbname, mbname_userid(mbname));

        /* Create a request target for this collection */
        pparams->parse_path(buf_cstring(&irock.resource), &irock.tgt, &errstr);

        /* Process each user */
        hash_enumerate(&user_access, send_dav_invite, &irock);

        /* Cleanup */
        if (irock.notify) xmlFreeDoc(irock.notify->doc);
        mboxlist_entry_free(&irock.tgt.mbentry);
        free(irock.tgt.userid);
        buf_free(&irock.resource);
        mbname_free(&mbname);
    }

  done:
    free_hash_table(&user_access, &free);
    free(owner);
    free(acl);

    return r;
}

HIDDEN void jmap_parse_sharewith_patch(json_t *arg, json_t **shareWith)
{
    struct buf buf = BUF_INITIALIZER;
    const char *field = NULL;
    json_t *jval;

    json_object_foreach(arg, field, jval) {
        if (!strncmp(field, "shareWith/", 10))  {
            const char *userid = field + 10;
            const char *right = strchr(userid, '/');

            if (!*shareWith) *shareWith = json_object();

            if (right) {
                /* individual right */
                buf_setmap(&buf, userid, right - userid);
                userid = buf_cstring(&buf);

                json_t *rights = json_object_get(*shareWith, userid);
                if (rights) {
                    /* add to existing ShareRights for this userid */
                    json_object_set(rights, right+1, jval);
                }
                else {
                    /* create new ShareRights for this userid */
                    json_object_set_new(*shareWith, userid,
                                        json_pack("{s:o}", right+1, jval));
                }
            }
            else {
                /* complete ShareRights */
                json_object_set(*shareWith, userid, jval);
            }
        }
    }

    buf_free(&buf);
}

HIDDEN int jmap_is_using(jmap_req_t *req, const char *capa)
{
    return strarray_find(req->using_capabilities, capa, 0) >= 0;
}

/*
 * Lookup 'name' in the mailbox list, ignoring reserved/deleted records
 */
HIDDEN int jmap_mboxlist_lookup(const char *name,
                                mbentry_t **entryptr, struct txn **tid)
{
    mbentry_t *entry = NULL;
    int r;

    r = mboxlist_lookup_allow_all(name, &entry, tid);

    if (r) return r;

    /* Ignore "reserved" entries, like they aren't there */
    if (entry->mbtype & MBTYPE_RESERVE) {
        mboxlist_entry_free(&entry);
        return IMAP_MAILBOX_RESERVED;
    }

    /* Ignore "deleted" entries, like they aren't there */
    if (entry->mbtype & MBTYPE_DELETED) {
        mboxlist_entry_free(&entry);
        return IMAP_MAILBOX_NONEXISTENT;
    }

    if (entryptr) *entryptr = entry;
    else mboxlist_entry_free(&entry);

    return 0;
}
