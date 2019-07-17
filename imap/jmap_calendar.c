/* jmap_calendar.c -- Routines for handling JMAP calendar messages
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

#include <ctype.h>
#include <assert.h>
#include <string.h>
#include <syslog.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include "acl.h"
#include "annotate.h"
#include "caldav_db.h"
#include "global.h"
#include "hash.h"
#include "httpd.h"
#include "http_caldav.h"
#include "http_caldav_sched.h"
#include "http_dav.h"
#include "http_jmap.h"
#include "http_proxy.h"
#include "ical_support.h"
#include "json_support.h"
#include "jmap_ical.h"
#include "search_query.h"
#include "stristr.h"
#include "times.h"
#include "util.h"
#include "xmalloc.h"

/* generated headers are not necessarily in current directory */
#include "imap/http_err.h"
#include "imap/imap_err.h"

static int jmap_calendar_get(struct jmap_req *req);
static int jmap_calendar_changes(struct jmap_req *req);
static int jmap_calendar_set(struct jmap_req *req);
static int jmap_calendarevent_get(struct jmap_req *req);
static int jmap_calendarevent_changes(struct jmap_req *req);
static int jmap_calendarevent_query(struct jmap_req *req);
static int jmap_calendarevent_set(struct jmap_req *req);
static int jmap_calendarevent_copy(struct jmap_req *req);

#define JMAPCACHE_CALVERSION 1

jmap_method_t jmap_calendar_methods[] = {
    {
        "Calendar/get",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendar_get,
        JMAP_SHARED_CSTATE
    },
    {
        "Calendar/changes",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendar_changes,
        JMAP_SHARED_CSTATE
    },
    {
        "Calendar/set",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendar_set,
        /*flags*/0
    },
    {
        "CalendarEvent/get",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendarevent_get,
        JMAP_SHARED_CSTATE
    },
    {
        "CalendarEvent/changes",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendarevent_changes,
        JMAP_SHARED_CSTATE
    },
    {
        "CalendarEvent/query",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendarevent_query,
        JMAP_SHARED_CSTATE
    },
    {
        "CalendarEvent/set",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendarevent_set,
        /*flags*/0
    },
    {
        "CalendarEvent/copy",
        JMAP_CALENDARS_EXTENSION,
        &jmap_calendarevent_copy,
        /*flags*/0
    },
    { NULL, NULL, NULL, 0}
};

HIDDEN void jmap_calendar_init(jmap_settings_t *settings)
{
    jmap_method_t *mp;
    for (mp = jmap_calendar_methods; mp->name; mp++) {
        hash_insert(mp->name, mp, &settings->methods);
    }

    json_object_set_new(settings->server_capabilities,
            JMAP_CALENDARS_EXTENSION, json_object());
}

HIDDEN void jmap_calendar_capabilities(json_t *account_capabilities)
{
    json_object_set_new(account_capabilities, JMAP_CALENDARS_EXTENSION, json_object());
}

/* Helper flags for CalendarEvent/set */
#define JMAP_CREATE     (1<<0) /* Current request is a create. */
#define JMAP_UPDATE     (1<<1) /* Current request is an update. */
#define JMAP_DESTROY    (1<<2) /* Current request is a destroy. */

/* Return a non-zero value if uid maps to a special-purpose calendar mailbox,
 * that may not be read or modified by the user. */
static int jmap_calendar_isspecial(mbname_t *mbname) {
    if (!mboxname_iscalendarmailbox(mbname_intname(mbname), 0)) return 1;

    const strarray_t *boxes = mbname_boxes(mbname);
    const char *lastname = strarray_nth(boxes, boxes->count - 1);

    /* Don't return user.foo.#calendars */
    if (!strcmp(lastname, config_getstring(IMAPOPT_CALENDARPREFIX))) {
        return 1;
    }

    /* SCHED_INBOX  and SCHED_OUTBOX end in "/", so trim them */
    if (!strncmp(lastname, SCHED_INBOX, strlen(SCHED_INBOX)-1)) return 1;
    if (!strncmp(lastname, SCHED_OUTBOX, strlen(SCHED_OUTBOX)-1)) return 1;
    if (!strncmp(lastname, MANAGED_ATTACH, strlen(MANAGED_ATTACH)-1)) return 1;
    return 0;
}

struct getcalendars_rock {
    struct jmap_req *req;
    struct jmap_get *get;
    int skip_hidden;
};

static json_t *get_schedule_address_set(const char *userid,
                                        const char *mboxname)
{
    struct buf attrib = BUF_INITIALIZER;
    json_t *val = json_array();
    static const char *annot =
        DAV_ANNOT_NS "<" XML_NS_CALDAV ">calendar-user-address-set";
    int r = annotatemore_lookupmask(mboxname, annot, httpd_userid, &attrib);
    if (r || !attrib.len) {
        // fetch from my own principal
        char *prinmbox = mboxname_user_mbox(httpd_userid, "#calendars");
        r = annotatemore_lookupmask(prinmbox, annot, httpd_userid, &attrib);
        free(prinmbox);
    }
    if (!r && attrib.len) {
        strarray_t *values = strarray_split(buf_cstring(&attrib), ",", STRARRAY_TRIM);
        int i;
        for (i = 0; i < strarray_size(values); i++) {
            json_array_append_new(val, json_string(strarray_nth(values, i)));
        }
        strarray_free(values);
    }
    else if (strchr(userid, '@')) {
        json_array_append_new(val, json_string(userid));
    }
    else {
        char *value = strconcat("mailto:", userid, "@", config_defdomain, NULL);
        json_array_append_new(val, json_string(value));
        free(value);
    }
    buf_free(&attrib);
    return val;
}

static int getcalendars_cb(const mbentry_t *mbentry, void *vrock)
{
    struct getcalendars_rock *rock = vrock;
    mbname_t *mbname = NULL;
    int r = 0;

    /* Only calendars... */
    if (!(mbentry->mbtype & MBTYPE_CALENDAR)) return 0;

    /* ...which are at least readable or visible... */
    if (!jmap_hasrights(rock->req, mbentry, DACL_READ))
        return rock->skip_hidden ? 0 : IMAP_PERMISSION_DENIED;

    // needed for some fields
    int rights = jmap_myrights(rock->req, mbentry);

    /* ...and contain VEVENTs. */
    struct buf attrib = BUF_INITIALIZER;
    static const char *calcompset_annot =
        DAV_ANNOT_NS "<" XML_NS_CALDAV ">supported-calendar-component-set";
    unsigned long supported_components = -1; /* ALL component types by default. */
    r = annotatemore_lookupmask(mbentry->name, calcompset_annot,
                                rock->req->accountid, &attrib);
    if (attrib.len) {
        supported_components = strtoul(buf_cstring(&attrib), NULL, 10);
        buf_free(&attrib);
    }
    if (!(supported_components & CAL_COMP_VEVENT)) {
        goto done;
    }

    /* OK, we want this one... */
    mbname = mbname_from_intname(mbentry->name);
    /* ...unless it's one of the special names. */
    if (jmap_calendar_isspecial(mbname)) {
        r = 0;
        goto done;
    }

    json_t *obj = json_pack("{}");

    const strarray_t *boxes = mbname_boxes(mbname);
    const char *id = strarray_nth(boxes, boxes->count-1);
    json_object_set_new(obj, "id", json_string(id));

    if (jmap_wantprop(rock->get->props, "x-href")) {
        // FIXME - should the x-ref for a shared calendar point
        // to the authenticated user's calendar home?
        char *xhref = jmap_xhref(mbentry->name, NULL);
        json_object_set_new(obj, "x-href", json_string(xhref));
        free(xhref);
    }

    if (jmap_wantprop(rock->get->props, "name")) {
        buf_reset(&attrib);
        static const char *displayname_annot =
            DAV_ANNOT_NS "<" XML_NS_DAV ">displayname";
        r = annotatemore_lookupmask(mbentry->name, displayname_annot,
                                    httpd_userid, &attrib);
        /* fall back to last part of mailbox name */
        if (r || !attrib.len) buf_setcstr(&attrib, id);
        json_object_set_new(obj, "name", json_string(buf_cstring(&attrib)));
        buf_free(&attrib);
    }

    if (jmap_wantprop(rock->get->props, "color")) {
        struct buf attrib = BUF_INITIALIZER;
        static const char *color_annot =
            DAV_ANNOT_NS "<" XML_NS_APPLE ">calendar-color";
        r = annotatemore_lookupmask(mbentry->name, color_annot,
                                    httpd_userid, &attrib);
        if (buf_len(&attrib))
            json_object_set_new(obj, "color", json_string(buf_cstring(&attrib)));
        buf_free(&attrib);
    }

    if (jmap_wantprop(rock->get->props, "sortOrder")) {
        long sort_order = 0;
        buf_reset(&attrib);
        static const char *order_annot =
            DAV_ANNOT_NS "<" XML_NS_APPLE ">calendar-order";
        r = annotatemore_lookupmask(mbentry->name, order_annot,
                                    httpd_userid, &attrib);
        if (!r && attrib.len) {
            char *ptr;
            long val = strtol(buf_cstring(&attrib), &ptr, 10);
            if (ptr && *ptr == '\0') {
                sort_order = val;
            }
            else {
                /* Ignore, but report non-numeric calendar-order values */
                syslog(LOG_WARNING, "sortOrder: strtol(%s) failed",
                       buf_cstring(&attrib));
            }
        }
        json_object_set_new(obj, "sortOrder", json_integer(sort_order));
        buf_free(&attrib);
    }

    if (jmap_wantprop(rock->get->props, "isVisible")) {
        int is_visible = 1;
        buf_reset(&attrib);
        static const char *color_annot =
            DAV_ANNOT_NS "<" XML_NS_CALDAV ">X-FM-isVisible";
        r = annotatemore_lookupmask(mbentry->name, color_annot,
                                    httpd_userid, &attrib);
        if (!r && attrib.len) {
            const char *val = buf_cstring(&attrib);
            if (!strncmp(val, "true", 4) || !strncmp(val, "1", 1)) {
                is_visible = 1;
            } else if (!strncmp(val, "false", 5) || !strncmp(val, "0", 1)) {
                is_visible = 0;
            } else {
                /* Report invalid value and fall back to default. */
                syslog(LOG_WARNING,
                       "isVisible: invalid annotation value: %s", val);
                is_visible = 1;
            }
        }
        json_object_set_new(obj, "isVisible", json_boolean(is_visible));
        buf_free(&attrib);
    }

    if (jmap_wantprop(rock->get->props, "isSubscribed")) {
        int is_subscribed = 1;
        if (mboxname_userownsmailbox(httpd_userid, mbentry->name)) {
            /* Users always subscribe their own calendars */
            is_subscribed = 1;
        }
        else {
            /* Lookup mailbox subscriptions */
            if (mboxlist_checksub(mbentry->name, httpd_userid) == 0) {
                /* It's listed in the mailbox subscription database,
                 * so it must be subscribed. */
                is_subscribed = 1;
            }
            else {
                is_subscribed = 0;
            }
        }
        json_object_set_new(obj, "isSubscribed", json_boolean(is_subscribed));
    }

    int writerights = DACL_WRITECONT|DACL_WRITEPROPS;

    if (jmap_wantprop(rock->get->props, "mayReadFreeBusy")) {
        json_object_set_new(obj, "mayReadFreeBusy",
                            ((rights & DACL_READFB) == DACL_READFB) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayReadItems")) {
        json_object_set_new(obj, "mayReadItems",
                            ((rights & DACL_READ) == DACL_READ) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayAddItems")) {
        json_object_set_new(obj, "mayAddItems",
                            ((rights & writerights) == writerights) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayModifyItems")) {
        json_object_set_new(obj, "mayModifyItems",
                            ((rights & writerights) == writerights) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayRemoveItems")) {
        json_object_set_new(obj, "mayRemoveItems",
                            ((rights & DACL_RMRSRC) == DACL_RMRSRC) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayRename")) {
        json_object_set_new(obj, "mayRename",
                            ((rights & (DACL_RMCOL|DACL_MKCOL)) == (DACL_RMCOL|DACL_MKCOL)) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayDelete")) {
        json_object_set_new(obj, "mayDelete",
                            ((rights & DACL_RMCOL) == DACL_RMCOL) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "mayAdmin")) {
        json_object_set_new(obj, "mayAdmin",
                            ((rights & ACL_ADMIN) == ACL_ADMIN) ? json_true() : json_false());
    }

    if (jmap_wantprop(rock->get->props, "shareWith")) {
        json_t *sharewith = jmap_get_sharewith(mbentry);
        json_object_set_new(obj, "shareWith", sharewith);
    }

    if (jmap_wantprop(rock->get->props, "scheduleAddressSet")) {
        json_t *set = get_schedule_address_set(rock->req->userid, mbentry->name);
        json_object_set_new(obj, "scheduleAddressSet", set);
    }

    json_array_append_new(rock->get->list, obj);

done:
    buf_free(&attrib);
    mbname_free(&mbname);
    return r;
}

static const jmap_property_t calendar_props[] = {
    {
        "id",
        NULL,
        JMAP_PROP_SERVER_SET | JMAP_PROP_IMMUTABLE | JMAP_PROP_ALWAYS_GET
    },
    {
        "name",
        NULL,
        0
    },
    {
        "color",
        NULL,
        0
    },
    {
        "sortOrder",
        NULL,
        0
    },
    {
        "isVisible",
        NULL,
        0
    },
    {
        "isSubscribed",
        NULL,
        0
    },
    {
        "mayReadFreeBusy",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayReadItems",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayAddItems",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayModifyItems",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayRemoveItems",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayRename",
        NULL,
        JMAP_PROP_SERVER_SET
    },
    {
        "mayDelete",
        NULL,
        JMAP_PROP_SERVER_SET
    },

    /* FM extensions (do ALL of these get through to Cyrus?) */
    {
        "mayAdmin",
        JMAP_CALENDARS_EXTENSION,
        JMAP_PROP_SERVER_SET
    },
    {
        "syncedFrom",
        JMAP_CALENDARS_EXTENSION,
        0
    },
    {
        "isEventsPublic",
        JMAP_CALENDARS_EXTENSION,
        0
    },
    {
        "isFreeBusyPublic",
        JMAP_CALENDARS_EXTENSION,
        0
    },
    {
        "eventsUrl",
        JMAP_CALENDARS_EXTENSION,
        JMAP_PROP_SERVER_SET
    },
    {
        "freeBusyUrl",
        JMAP_CALENDARS_EXTENSION,
        JMAP_PROP_SERVER_SET
    },
    {
        "calDavUrl",
        JMAP_CALENDARS_EXTENSION,
        JMAP_PROP_SERVER_SET
    },
    {
        "shareWith",
        JMAP_CALENDARS_EXTENSION,
        0
    },
    {
        "x-href",
        JMAP_CALENDARS_EXTENSION,
        JMAP_PROP_SERVER_SET
    },
    {
        "scheduleAddressSet",
        JMAP_CALENDARS_EXTENSION,
        0
    },

    { NULL, NULL, 0 }
};

static int jmap_calendar_get(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_get get;
    json_t *err = NULL;
    int r = 0;

    r = caldav_create_defaultcalendars(req->accountid);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* The account exists but does not have a root mailbox. */
        jmap_error(req, json_pack("{s:s}", "type", "accountNoCalendars"));
        return 0;
    } else if (r) return r;

    /* Parse request */
    jmap_get_parse(req, &parser, calendar_props, /*allow_null_ids*/1,
                   NULL, NULL, &get, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    /* Build callback data */
    struct getcalendars_rock rock = { req, &get, 1 /*skiphidden*/ };

    /* Does the client request specific mailboxes? */
    if (JNOTNULL(get.ids)) {
        size_t i;
        json_t *jval;

        rock.skip_hidden = 0; /* complain about missing ACL rights */
        json_array_foreach(get.ids, i, jval) {
            const char *id = json_string_value(jval);
            char *mboxname = caldav_mboxname(req->accountid, id);
            mbentry_t *mbentry = NULL;

            r = mboxlist_lookup(mboxname, &mbentry, NULL);
            if (r == IMAP_NOTFOUND || !mbentry) {
                json_array_append(get.not_found, jval);
                r = 0;
            }
            else {
                r = getcalendars_cb(mbentry, &rock);
                if (r == IMAP_PERMISSION_DENIED) {
                    json_array_append(get.not_found, jval);
                    r = 0;
                }
            }

            if (mbentry) mboxlist_entry_free(&mbentry);
            free(mboxname);
            if (r) goto done;
        }
    }
    else {
        // XXX: replace with a function which only looks inside INBOX.#calendars
        r = mboxlist_usermboxtree(req->accountid, req->authstate, &getcalendars_cb, &rock, MBOXTREE_INTERMEDIATES);
        if (r) goto done;
    }

    /* Build response */
    json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/0);
    get.state = xstrdup(json_string_value(jstate));
    json_decref(jstate);
    jmap_ok(req, jmap_get_reply(&get));

done:
    jmap_parser_fini(&parser);
    jmap_get_fini(&get);
    return r;
}

struct calendarchanges_rock {
    jmap_req_t *req;
    struct jmap_changes *changes;
};

static int getcalendarchanges_cb(const mbentry_t *mbentry, void *vrock)
{
    struct calendarchanges_rock *rock = (struct calendarchanges_rock *) vrock;
    mbname_t *mbname = NULL;
    jmap_req_t *req = rock->req;
    int r = 0;

    /* Ignore old changes. */
    if (mbentry->foldermodseq <= rock->changes->since_modseq) {
        goto done;
    }

    /* Ignore any mailboxes that aren't (possibly deleted) calendars. */
    if (!mboxname_iscalendarmailbox(mbentry->name, mbentry->mbtype))
        return 0;

    /* Ignore mailboxes that are hidden from us. */
    /* XXX Deleted mailboxes loose their ACL so we can't determine
     * if they ever could be read by the authenticated user. We
     * need to leak these deleted entries to not mess up client state. */
    if (!(mbentry->mbtype & MBTYPE_DELETED) || strcmpsafe(mbentry->acl, "")) {
        if (!jmap_hasrights(req, mbentry, DACL_READ)) return 0;
    }

    /* Ignore special-purpose calendar mailboxes. */
    mbname = mbname_from_intname(mbentry->name);
    if (jmap_calendar_isspecial(mbname)) {
        goto done;
    }

    /* Ignore calendars that don't store VEVENTs */
    struct buf attrib = BUF_INITIALIZER;
    static const char *calcompset_annot =
        DAV_ANNOT_NS "<" XML_NS_CALDAV ">supported-calendar-component-set";
    unsigned long supported_components = -1; /* ALL component types by default. */
    r = annotatemore_lookupmask(mbentry->name, calcompset_annot,
                                rock->req->accountid, &attrib);
    if (attrib.len) {
        supported_components = strtoul(buf_cstring(&attrib), NULL, 10);
        buf_free(&attrib);
    }
    if (!(supported_components & CAL_COMP_VEVENT)) {
        goto done;
    }

    const strarray_t *boxes = mbname_boxes(mbname);
    const char *id = strarray_nth(boxes, boxes->count-1);

    /* Report this calendar as created, updated or destroyed. */
    if (mbentry->mbtype & MBTYPE_DELETED) {
        if (mbentry->createdmodseq <= rock->changes->since_modseq)
            json_array_append_new(rock->changes->destroyed, json_string(id));
    }
    else {
        if (mbentry->createdmodseq <= rock->changes->since_modseq)
            json_array_append_new(rock->changes->updated, json_string(id));
        else
            json_array_append_new(rock->changes->created, json_string(id));
    }

done:
    mbname_free(&mbname);
    return r;
}

static int jmap_calendar_changes(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_changes changes;
    json_t *err = NULL;
    int r = 0;

    r = caldav_create_defaultcalendars(req->accountid);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* The account exists but does not have a root mailbox. */
        jmap_error(req, json_pack("{s:s}", "type", "accountNoCalendars"));
        return 0;
    } else if (r) goto done;

    /* Parse request */
    jmap_changes_parse(req, &parser, NULL, NULL, &changes, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    /* Lookup any changes. */
    char *mboxname = caldav_mboxname(req->accountid, NULL);
    struct calendarchanges_rock rock = { req, &changes };

    r = mboxlist_mboxtree(mboxname, getcalendarchanges_cb, &rock,
                          MBOXTREE_TOMBSTONES|MBOXTREE_SKIP_ROOT);
    free(mboxname);
    if (r) {
        jmap_error(req, json_pack("{s:s}", "type", "cannotCalculateChanges"));
        r = 0;
        goto done;
    }

    /* Determine new state.  XXX  what about max_changes? */
    changes.new_modseq = /*changes.has_more_changes ? rock.highestmodseq :*/
        jmap_highestmodseq(req, MBTYPE_CALENDAR);

    /* Build response */
    jmap_ok(req, jmap_changes_reply(&changes));

  done:
    jmap_changes_fini(&changes);
    jmap_parser_fini(&parser);
    if (r) {
        jmap_error(req, jmap_server_error(r));
    }
    return 0;
}

/* jmap calendar APIs */

/* Update the calendar properties in the calendar mailbox named mboxname.
 * NULL values and negative integers are ignored. Return 0 on success. */
static int setcalendars_update(jmap_req_t *req,
                               const char *mboxname,
                               const char *name,
                               const char *color,
                               int sortOrder,
                               int isVisible,
                               int isSubscribed,
                               json_t *shareWith,
                               json_t *scheduleAddressSet,
                               int overwrite_acl)
{
    struct mailbox *mbox = NULL;
    annotate_state_t *astate = NULL;
    struct buf val = BUF_INITIALIZER;
    int r;

    if (!jmap_hasrights_byname(req, mboxname, DACL_READ))
        return IMAP_MAILBOX_NONEXISTENT;

    r = mailbox_open_iwl(mboxname, &mbox);
    if (r) {
        syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s",
                mboxname, error_message(r));
        return r;
    }

    r = mailbox_get_annotate_state(mbox, 0, &astate);
    if (r) {
        syslog(LOG_ERR, "IOERROR: failed to open annotations %s: %s",
                mbox->name, error_message(r));
    }
    /* name */
    if (!r && name) {
        buf_setcstr(&val, name);
        static const char *displayname_annot =
            DAV_ANNOT_NS "<" XML_NS_DAV ">displayname";
        r = annotate_state_writemask(astate, displayname_annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                    displayname_annot, error_message(r));
        }
        buf_reset(&val);
    }
    /* color */
    if (!r && color) {
        buf_setcstr(&val, color);
        static const char *color_annot =
            DAV_ANNOT_NS "<" XML_NS_APPLE ">calendar-color";
        r = annotate_state_writemask(astate, color_annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                    color_annot, error_message(r));
        }
        buf_reset(&val);
    }
    /* sortOrder */
    if (!r && sortOrder >= 0) {
        buf_printf(&val, "%d", sortOrder);
        static const char *sortOrder_annot =
            DAV_ANNOT_NS "<" XML_NS_APPLE ">calendar-order";
        r = annotate_state_writemask(astate, sortOrder_annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                    sortOrder_annot, error_message(r));
        }
        buf_reset(&val);
    }
    /* isVisible */
    if (!r && isVisible >= 0) {
        buf_setcstr(&val, isVisible ? "true" : "false");
        static const char *visible_annot =
            DAV_ANNOT_NS "<" XML_NS_CALDAV ">X-FM-isVisible";
        r = annotate_state_writemask(astate, visible_annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                    visible_annot, error_message(r));
        }
        buf_reset(&val);
    }
    /* scheduleAddressSet */
    if (!r && json_is_array(scheduleAddressSet)) {
        static const char *annot =
            DAV_ANNOT_NS "<" XML_NS_CALDAV ">calendar-user-address-set";
        strarray_t *array = strarray_new();
        size_t i;
        json_t *jval;
        json_array_foreach(scheduleAddressSet, i, jval) {
            strarray_add(array, json_string_value(jval));
        }
        char *joined = strarray_join(array, ",");
        buf_setcstr(&val, joined);
        r = annotate_state_writemask(astate, annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                   annot, error_message(r));
        }
        free(joined);
        strarray_free(array);
        buf_reset(&val);
    }

    /* isSubscribed */
    if (!r && isSubscribed >= 0) {
        /* Update subscription database */
        r = mboxlist_changesub(mboxname, req->userid, req->authstate,
                               isSubscribed, 0, /*notify*/1);

        /* Set invite status for CalDAV */
        buf_setcstr(&val, isSubscribed ? "invite-accepted" : "invite-declined");
        static const char *invite_annot =
            DAV_ANNOT_NS "<" XML_NS_DAV ">invite-status";
        r = annotate_state_writemask(astate, invite_annot, req->userid, &val);
        if (r) {
            syslog(LOG_ERR, "failed to write annotation %s: %s",
                    invite_annot, error_message(r));
        }
        buf_reset(&val);
    }
    /* shareWith */
    if (!r && shareWith) {
        r = jmap_set_sharewith(mbox, shareWith, overwrite_acl);
    }

    buf_free(&val);
    if (r) {
        mailbox_abort(mbox);
    }
    mailbox_close(&mbox);
    return r;
}

/* Delete the calendar mailbox named mboxname for the userid in req. */
static int setcalendars_destroy(jmap_req_t *req, const char *mboxname)
{
    if (!jmap_hasrights_byname(req, mboxname, DACL_READ))
        return IMAP_NOTFOUND;
    if (!jmap_hasrights_byname(req, mboxname, DACL_RMCOL))
        return IMAP_PERMISSION_DENIED;

    struct caldav_db *db = caldav_open_userid(req->userid);
    if (!db) {
        syslog(LOG_ERR, "caldav_open_mailbox failed for user %s", req->userid);
        return IMAP_INTERNAL;
    }
    /* XXX 
     * JMAP spec says that: "A calendar MAY be deleted that is currently
     * associated with one or more events. In this case, the events belonging
     * to this calendar MUST also be deleted. Conceptually, this MUST happen
     * prior to the calendar itself being deleted, and MUST generate a push
     * event that modifies the calendarState for the account, and has a
     * clientId of null, to indicate that a change has been made to the
     * calendar data not explicitly requested by the client."
     *
     * Need the Events API for this requirement.
     */
    int r = caldav_delmbox(db, mboxname);
    if (r) {
        syslog(LOG_ERR, "failed to delete mailbox from caldav_db: %s",
                error_message(r));
        return r;
    }
    jmap_myrights_delete(req, mboxname);

    /* Remove from subscriptions db */
    mboxlist_changesub(mboxname, req->userid, req->authstate, 0, 1, 0);

    struct mboxevent *mboxevent = mboxevent_new(EVENT_MAILBOX_DELETE);
    if (mboxlist_delayed_delete_isenabled()) {
        r = mboxlist_delayed_deletemailbox(mboxname,
                httpd_userisadmin || httpd_userisproxyadmin,
                httpd_userid, req->authstate, mboxevent,
                1 /* checkacl */, 0 /* local_only */, 0 /* force */,
                0 /* keep_intermediaries */);
    } else {
        r = mboxlist_deletemailbox(mboxname,
                httpd_userisadmin || httpd_userisproxyadmin,
                httpd_userid, req->authstate, mboxevent,
                1 /* checkacl */, 0 /* local_only */, 0 /* force */,
                0 /* keep_intermediaries */);
    }
    mboxevent_free(&mboxevent);

    int rr = caldav_close(db);
    if (!r) r = rr;

    return r;
}

static int jmap_calendar_set(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_set set;
    json_t *err = NULL;
    int r = 0;

    /* Parse arguments */
    jmap_set_parse(req, &parser, calendar_props, NULL, NULL, &set, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    if (set.if_in_state) {
        /* TODO rewrite state function to use char* not json_t* */
        json_t *jstate = json_string(set.if_in_state);
        if (jmap_cmpstate(req, jstate, MBTYPE_CALENDAR)) {
            jmap_error(req, json_pack("{s:s}", "type", "stateMismatch"));
            json_decref(jstate);
            goto done;
        }
        json_decref(jstate);
        set.old_state = xstrdup(set.if_in_state);
    }
    else {
        json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/0);
        set.old_state = xstrdup(json_string_value(jstate));
        json_decref(jstate);
    }

    r = caldav_create_defaultcalendars(req->accountid);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* The account exists but does not have a root mailbox. */
        json_t *err = json_pack("{s:s}", "type", "accountNoCalendars");
        json_array_append_new(req->response, json_pack("[s,o,s]",
                    "error", err, req->tag));
        return 0;
    } else if (r) return r;


    /* create */
    const char *key;
    json_t *arg, *record;
    json_object_foreach(set.create, key, arg) {
        /* Validate calendar id. */
        if (!strlen(key)) {
            json_t *err= json_pack("{s:s}", "type", "invalidArguments");
            json_object_set_new(set.not_created, key, err);
            continue;
        }

        /* Parse and validate properties. */
        json_t *invalid = json_pack("[]"), *shareWith = NULL;
        const char *name = NULL;
        const char *color = NULL;
        int32_t sortOrder = 0;
        int isVisible = 1;
        int isSubscribed = 1;
        int pe; /* parse error */
        short flag;
        json_t *scheduleAddressSet = NULL;

        /* Mandatory properties. */
        pe = jmap_readprop(arg, "name", 1,  invalid, "s", &name);
        if (pe > 0 && strnlen(name, 256) == 256) {
            json_array_append_new(invalid, json_string("name"));
        }

        jmap_readprop(arg, "color", 1,  invalid, "s", &color);

        pe = jmap_readprop(arg, "sortOrder", 0,  invalid, "i", &sortOrder);
        if (pe > 0 && sortOrder < 0) {
            json_array_append_new(invalid, json_string("sortOrder"));
        }
        jmap_readprop(arg, "isVisible", 0,  invalid, "b", &isVisible);
        pe = jmap_readprop(arg, "isSubscribed", 0,  invalid, "b", &isSubscribed);
        if (pe > 0 && !strcmp(req->accountid, req->userid)) {
            if (!isSubscribed) {
                /* XXX unsubscribing own calendars isn't supported */
                json_array_append_new(invalid, json_string("isSubscribed"));
            }
            else {
                isSubscribed = -1; // ignore
            }
        }

        /* Optional properties. */
        jmap_readprop(arg, "shareWith", 0,  invalid, "o", &shareWith);

        jmap_readprop(arg, "scheduleAddressSet", 0,  invalid, "o", &scheduleAddressSet);

        /* Optional properties. If present, these MUST be set to true. */
        flag = 1; jmap_readprop(arg, "mayReadFreeBusy", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayReadFreeBusy"));
        }
        flag = 1; jmap_readprop(arg, "mayReadItems", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayReadItems"));
        }
        flag = 1; jmap_readprop(arg, "mayAddItems", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayAddItems"));
        }
        flag = 1; jmap_readprop(arg, "mayModifyItems", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayModifyItems"));
        }
        flag = 1; jmap_readprop(arg, "mayRemoveItems", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayRemoveItems"));
        }
        flag = 1; jmap_readprop(arg, "mayRename", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayRename"));
        }
        flag = 1; jmap_readprop(arg, "mayDelete", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayDelete"));
        }
        flag = 1; jmap_readprop(arg, "mayAdmin", 0,  invalid, "b", &flag);
        if (!flag) {
            json_array_append_new(invalid, json_string("mayAdmin"));
        }

        /* Report any property errors and bail out. */
        if (json_array_size(invalid)) {
            json_t *err = json_pack("{s:s, s:o}",
                                    "type", "invalidProperties",
                                    "properties", invalid);
            json_object_set_new(set.not_created, key, err);
            continue;
        }
        json_decref(invalid);

        /* Make sure we are allowed to create the calendar */
        char *parentname = caldav_mboxname(req->accountid, NULL);
        mbentry_t *mbparent = NULL;
        mboxlist_lookup(parentname, &mbparent, NULL);
        free(parentname);
        if (!jmap_hasrights(req, mbparent, DACL_MKCOL)) {
            json_t *err = json_pack("{s:s}", "type", "accountReadOnly");
            json_object_set_new(set.not_created, key, err);
            mboxlist_entry_free(&mbparent);
            continue;
        }
        mboxlist_entry_free(&mbparent);

        /* Create the calendar */
        char *uid = xstrdup(makeuuid());
        char *mboxname = caldav_mboxname(req->accountid, uid);
        r = mboxlist_createmailbox(mboxname, MBTYPE_CALENDAR,
                                   NULL /* partition */,
                                   httpd_userisadmin || httpd_userisproxyadmin,
                                   httpd_userid, httpd_authstate,
                                   /*localonly*/0, /*forceuser*/0,
                                   /*dbonly*/0, /*notify*/0,
                                   /*mailboxptr*/NULL);
        if (r) {
            syslog(LOG_ERR, "IOERROR: failed to create %s (%s)",
                   mboxname, error_message(r));
            if (r == IMAP_PERMISSION_DENIED) {
                json_t *err = json_pack("{s:s}", "type", "accountReadOnly");
                json_object_set_new(set.not_created, key, err);
            }
            free(mboxname);
            goto done;
        }
        r = setcalendars_update(req, mboxname, name, color, sortOrder,
                                isVisible, isSubscribed, shareWith, scheduleAddressSet, 1);
        if (r) {
            free(uid);
            int rr = mboxlist_delete(mboxname);
            if (rr) {
                syslog(LOG_ERR, "could not delete mailbox %s: %s",
                       mboxname, error_message(rr));
            }
            free(mboxname);
            goto done;
        }

        /* Report calendar as created. */
        record = json_pack("{s:s}", "id", uid);

        /* Add additional properties */
        if (jmap_is_using(req, JMAP_CALENDARS_EXTENSION)) {
            json_t *addrset = get_schedule_address_set(req->userid, mboxname);
            if (addrset) json_object_set_new(record, "scheduleAddressSet", addrset);
        }

        json_object_set_new(set.created, key, record);
        jmap_add_id(req, key, uid);
        free(uid);
        free(mboxname);
    }


    /* update */
    const char *uid;
    json_object_foreach(set.update, uid, arg) {

        /* Validate uid */
        if (!uid) {
            continue;
        }
        if (uid && uid[0] == '#') {
            const char *newuid = jmap_lookup_id(req, uid + 1);
            if (!newuid) {
                json_t *err = json_pack("{s:s}", "type", "notFound");
                json_object_set_new(set.not_updated, uid, err);
                continue;
            }
            uid = newuid;
        }

        /* Parse and validate properties. */
        json_t *invalid = json_pack("[]"), *shareWith = NULL;

        char *mboxname = caldav_mboxname(req->accountid, uid);
        const char *name = NULL;
        const char *color = NULL;
        int32_t sortOrder = -1;
        int isVisible = -1;
        int isSubscribed = -1;
        int overwrite_acl = 1;
        int flag;
        json_t *scheduleAddressSet = NULL;
        int pe = 0; /* parse error */
        pe = jmap_readprop(arg, "name", 0,  invalid, "s", &name);
        if (pe > 0 && strnlen(name, 256) == 256) {
            json_array_append_new(invalid, json_string("name"));
        }
        jmap_readprop(arg, "color", 0,  invalid, "s", &color);
        pe = jmap_readprop(arg, "sortOrder", 0,  invalid, "i", &sortOrder);
        if (pe > 0 && sortOrder < 0) {
            json_array_append_new(invalid, json_string("sortOrder"));
        }
        jmap_readprop(arg, "isVisible", 0,  invalid, "b", &isVisible);
        pe = jmap_readprop(arg, "isSubscribed", 0,  invalid, "b", &isSubscribed);
        if (pe > 0 && !strcmp(req->accountid, req->userid)) {
            if (!isSubscribed) {
                /* XXX unsubscribing own calendars isn't supported */
                json_array_append_new(invalid, json_string("isSubscribed"));
            }
            else {
                isSubscribed = -1; // ignore
            }
        }

        /* Is shareWith overwritten or patched? */
        jmap_parse_sharewith_patch(arg, &shareWith);
        if (shareWith) {
            overwrite_acl = 0;
            json_object_set_new(arg, "shareWith", shareWith);
        }
        pe = jmap_readprop(arg, "shareWith", 0,  invalid, "o", &shareWith);
        if (pe > 0 && !jmap_hasrights_byname(req, mboxname, ACL_ADMIN)) {
            json_array_append_new(invalid, json_string("shareWith"));
        }

        jmap_readprop(arg, "scheduleAddressSet", 0,  invalid, "o", &scheduleAddressSet);

        /* The mayFoo properties are immutable and MUST NOT set. */
        pe = jmap_readprop(arg, "mayReadFreeBusy", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayReadFreeBusy"));
        }
        pe = jmap_readprop(arg, "mayReadItems", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayReadItems"));
        }
        pe = jmap_readprop(arg, "mayAddItems", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayAddItems"));
        }
        pe = jmap_readprop(arg, "mayModifyItems", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayModifyItems"));
        }
        pe = jmap_readprop(arg, "mayRemoveItems", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayRemoveItems"));
        }
        pe = jmap_readprop(arg, "mayRename", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayRename"));
        }
        pe = jmap_readprop(arg, "mayDelete", 0,  invalid, "b", &flag);
        if (pe > 0) {
            json_array_append_new(invalid, json_string("mayDelete"));
        }
        
        /* Report any property errors and bail out. */
        if (json_array_size(invalid)) {
            json_t *err = json_pack("{s:s, s:o}",
                                    "type", "invalidProperties",
                                    "properties", invalid);
            json_object_set_new(set.not_updated, uid, err);
            free(mboxname);
            continue;
        }
        json_decref(invalid);

        /* Make sure we don't mess up special calendars */
        mbname_t *mbname = mbname_from_intname(mboxname);
        if (!mbname || jmap_calendar_isspecial(mbname)) {
            json_t *err = json_pack("{s:s}", "type", "notFound");
            json_object_set_new(set.not_updated, uid, err);
            mbname_free(&mbname);
            free(mboxname);
            continue;
        }
        mbname_free(&mbname);

        /* Update the calendar */
        r = setcalendars_update(req, mboxname, name, color, sortOrder,
                                isVisible, isSubscribed, shareWith, scheduleAddressSet, overwrite_acl);
        free(mboxname);
        if (r == IMAP_NOTFOUND || r == IMAP_MAILBOX_NONEXISTENT) {
            json_t *err = json_pack("{s:s}", "type", "notFound");
            json_object_set_new(set.not_updated, uid, err);
            r = 0;
            continue;
        }
        else if (r == IMAP_PERMISSION_DENIED) {
            json_t *err = json_pack("{s:s}", "type", "accountReadOnly");
            json_object_set_new(set.not_updated, uid, err);
            r = 0;
            continue;
        }

        /* Report calendar as updated. */
        json_object_set_new(set.updated, uid, json_null());
    }


    /* destroy */
    size_t index;
    json_t *juid;

    json_array_foreach(set.destroy, index, juid) {

        /* Validate uid */
        const char *uid = json_string_value(juid);
        if (!uid) {
            continue;
        }
        if (uid && uid[0] == '#') {
            const char *newuid = jmap_lookup_id(req, uid + 1);
            if (!newuid) {
                json_t *err = json_pack("{s:s}", "type", "notFound");
                json_object_set_new(set.not_destroyed, uid, err);
                continue;
            }
            uid = newuid;
        }

        /* Do not allow to remove the default calendar. */
        char *mboxname = caldav_mboxname(req->accountid, NULL);
        static const char *defaultcal_annot =
            DAV_ANNOT_NS "<" XML_NS_CALDAV ">schedule-default-calendar";
        struct buf attrib = BUF_INITIALIZER;
        r = annotatemore_lookupmask(mboxname, defaultcal_annot,
                                    req->accountid, &attrib);
        free(mboxname);
        const char *defaultcal = "Default";
        if (!r && attrib.len) {
            defaultcal = buf_cstring(&attrib);
        }
        if (!strcmp(uid, defaultcal)) {
            /* XXX - The isDefault set error is not documented in the spec. */
            json_t *err = json_pack("{s:s}", "type", "isDefault");
            json_object_set_new(set.not_destroyed, uid, err);
            buf_free(&attrib);
            continue;
        }
        buf_free(&attrib);

        /* Make sure we don't delete special calendars */
        mboxname = caldav_mboxname(req->accountid, uid);
        mbname_t *mbname = mbname_from_intname(mboxname);
        if (!mbname || jmap_calendar_isspecial(mbname)) {
            json_t *err = json_pack("{s:s}", "type", "notFound");
            json_object_set_new(set.not_destroyed, uid, err);
            mbname_free(&mbname);
            free(mboxname);
            continue;
        }
        mbname_free(&mbname);

        /* Destroy calendar. */
        r = setcalendars_destroy(req, mboxname);
        free(mboxname);
        if (r == IMAP_NOTFOUND || r == IMAP_MAILBOX_NONEXISTENT) {
            json_t *err = json_pack("{s:s}", "type", "notFound");
            json_object_set_new(set.not_destroyed, uid, err);
            r = 0;
            continue;
        } else if (r == IMAP_PERMISSION_DENIED) {
            json_t *err = json_pack("{s:s}", "type", "accountReadOnly");
            json_object_set_new(set.not_destroyed, uid, err);
            r = 0;
            continue;
        } else if (r) {
            goto done;
        }

        /* Report calendar as destroyed. */
        json_array_append_new(set.destroyed, json_string(uid));
    }


    // TODO refactor jmap_getstate to return a string, once
    // all code has been migrated to the new JMAP parser.
    json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/1);
    set.new_state = xstrdup(json_string_value(jstate));
    json_decref(jstate);

    jmap_ok(req, jmap_set_reply(&set));

done:
    jmap_parser_fini(&parser);
    jmap_set_fini(&set);
    return r;
}

/* FIXME dup from jmapical.c */
/* Convert the JMAP local datetime in buf to tm time. Return non-zero on success. */
static int localdate_to_tm(const char *buf, struct tm *tm) {
    /* Initialize tm. We don't know about daylight savings time here. */
    memset(tm, 0, sizeof(struct tm));
    tm->tm_isdst = -1;

    /* Parse LocalDate. */
    const char *p = strptime(buf, "%Y-%m-%dT%H:%M:%S", tm);
    if (!p || *p) {
        return 0;
    }
    return 1;
}

/* FIXME dup from jmapical.c */
static int localdate_to_icaltime(const char *buf,
                                 icaltimetype *dt,
                                 icaltimezone *tz,
                                 int is_allday) {
    struct tm tm;
    int r;
    char *s = NULL;
    icaltimetype tmp;
    int is_utc;
    size_t n;

    r = localdate_to_tm(buf, &tm);
    if (!r) return 0;

    if (is_allday && (tm.tm_sec || tm.tm_min || tm.tm_hour)) {
        return 0;
    }

    is_utc = tz == icaltimezone_get_utc_timezone();

    /* Can't use icaltime_from_timet_with_zone since it tries to convert
     * t from UTC into tz. Let's feed ical a DATETIME string, instead. */
    s = xcalloc(19, sizeof(char));
    n = strftime(s, 18, "%Y%m%dT%H%M%S", &tm);
    if (is_utc) {
        s[n]='Z';
    }
    tmp = icaltime_from_string(s);
    free(s);
    if (icaltime_is_null_time(tmp)) {
        return 0;
    }
    tmp.zone = tz;
    tmp.is_date = is_allday;
    *dt = tmp;
    return 1;
}

/* FIXME dup from jmapical.c */
static int utcdate_to_icaltime(const char *src,
                               icaltimetype *dt)
{
    struct buf buf = BUF_INITIALIZER;
    size_t len = strlen(src);
    int r;
    icaltimezone *utc = icaltimezone_get_utc_timezone();

    if (!len || src[len-1] != 'Z') {
        return 0;
    }

    buf_setmap(&buf, src, len-1);
    r = localdate_to_icaltime(buf_cstring(&buf), dt, utc, 0);
    buf_free(&buf);
    return r;
}

struct getcalendarevents_rock {
    struct caldav_db *db;
    struct jmap_req *req;
    struct jmap_get *get;
    struct mailbox *mailbox;
    int check_acl;
};

static int getcalendarevents_cb(void *vrock, struct caldav_data *cdata)
{
    struct getcalendarevents_rock *rock = vrock;
    int r = 0;
    icalcomponent* ical = NULL;
    json_t *jsevent = NULL;
    jmap_req_t *req = rock->req;
    char *schedule_address = NULL;

    if (!cdata->dav.alive)
        return 0;

    /* check that it's the right type */
    if (cdata->comp_type != CAL_COMP_VEVENT)
        return 0;

    /* Check mailbox ACL rights */
    if (!jmap_hasrights_byname(req, cdata->dav.mailbox, DACL_READ))
        return 0;

    if (cdata->jmapversion == JMAPCACHE_CALVERSION) {
        json_error_t jerr;
        jsevent = json_loads(cdata->jmapdata, 0, &jerr);
        if (jsevent) goto gotevent;
    }

    /* Open calendar mailbox. */
    if (!rock->mailbox || strcmp(rock->mailbox->name, cdata->dav.mailbox)) {
        mailbox_close(&rock->mailbox);
        r = mailbox_open_irl(cdata->dav.mailbox, &rock->mailbox);
        if (r) goto done;
    }

    /* Load message containing the resource and parse iCal data */
    ical = caldav_record_to_ical(rock->mailbox, cdata, httpd_userid, &schedule_address);
    if (!ical) {
        syslog(LOG_ERR, "caldav_record_to_ical failed for record %u:%s",
                cdata->dav.imap_uid, rock->mailbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Convert to JMAP */
    jsevent = jmapical_tojmap(ical, NULL);
    if (!jsevent) {
        syslog(LOG_ERR, "jmapical_tojson: can't convert %u:%s",
                cdata->dav.imap_uid, rock->mailbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }
    icalcomponent_free(ical);
    ical = NULL;

    /* Add participant id */
    const char *participant_id = NULL;
    if (schedule_address) {
        const char *key;
        json_t *participant;
        json_object_foreach(json_object_get(jsevent, "participants"), key, participant) {
            const char *email = json_string_value(json_object_get(participant, "email"));
            if (email && !strcmp(email, schedule_address)) {
                participant_id = key;
                break;
            }
        }
    }
    json_object_set_new(jsevent, "participantId", participant_id ?
            json_string(participant_id) : json_null());

    char *eventrep = json_dumps(jsevent, 0);
    r = caldav_write_jmapcache(rock->db, cdata->dav.rowid, httpd_userid,
                               JMAPCACHE_CALVERSION, eventrep);
    free(eventrep);

gotevent:
    jmap_filterprops(jsevent, rock->get->props);

    /* Add JMAP-only fields. */
    if (jmap_wantprop(rock->get->props, "x-href")) {
        char *xhref = jmap_xhref(cdata->dav.mailbox, cdata->dav.resource);
        json_object_set_new(jsevent, "x-href", json_string(xhref));
        free(xhref);
    }
    if (jmap_wantprop(rock->get->props, "calendarId")) {
        json_object_set_new(jsevent, "calendarId",
                            json_string(strrchr(cdata->dav.mailbox, '.')+1));
    }
    json_object_set_new(jsevent, "id", json_string(cdata->ical_uid));
    json_object_set_new(jsevent, "uid", json_string(cdata->ical_uid));
    json_object_set_new(jsevent, "@type", json_string("jsevent"));

    /* Add JMAP event to response */
    json_array_append_new(rock->get->list, jsevent);

done:
    free(schedule_address);
    if (ical) icalcomponent_free(ical);
    return r;
}

static const jmap_property_t event_props[] = {
    {
        "id",
        NULL,
        JMAP_PROP_IMMUTABLE | JMAP_PROP_ALWAYS_GET
    },
    {
        "calendarId",
        NULL,
        0
    },
    {
        "participantId",
        NULL,
        0
    },

    /* JSCalendar common properties */
    {
        "@type",
        NULL,
        0
    },
    {
        "uid",
        NULL,
        0
    },
    {
        "relatedTo",
        NULL,
        0
    },
    {
        "prodId",
        NULL,
        0
    },
    {
        "created",
        NULL,
        0
    },
    {
        "updated",
        NULL,
        0
    },
    {
        "sequence",
        NULL,
        0
    },
    {
        "method",
        NULL,
        0
    },
    {
        "title",
        NULL,
        0
    },
    {
        "description",
        NULL,
        0
    },
    {
        "descriptionContentType",
        NULL,
        0
    },
    {
        "locations",
        NULL,
        0
    },
    {
        "virtualLocations",
        NULL,
        0
    },
    {
        "links",
        NULL,
        0
    },
    {
        "locale",
        NULL,
        0
    },
    {
        "keywords",
        NULL,
        0
    },
    {
        "categories",
        NULL,
        0
    },
    {
        "color",
        NULL,
        0
    },
    {
        "recurrenceRule",
        NULL,
        0
    },
    {
        "recurrenceOverrides",
        NULL,
        0
    },
    {
        "excluded",
        NULL,
        0
    },
    {
        "priority",
        NULL,
        0
    },
    {
        "freeBusyStatus",
        NULL,
        0
    },
    {
        "privacy",
        NULL,
        0
    },
    {
        "replyTo",
        NULL,
        0
    },
    {
        "participants",
        NULL,
        0
    },
    {
        "useDefaultAlerts",
        NULL,
        0
    },
    {
        "alerts",
        NULL,
        0
    },
    {
        "localizations",
        NULL,
        0
    },

    /* JSEvent properties */
    {
        "start",
        NULL,
        0
    },
    {
        "timeZone",
        NULL,
        0
    },
    {
        "duration",
        NULL,
        0
    },
    {
        "isAllDay",
        NULL,
        0
    },
    {
        "status",
        NULL,
        0
    },

    /* FM specific */
    {
        "x-href",
        JMAP_CALENDARS_EXTENSION,
        0
    },
    { NULL, NULL, 0 }
};

static int jmap_calendarevent_get(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_get get;
    struct caldav_db *db = NULL;
    json_t *err = NULL;
    int r = 0;

    r = caldav_create_defaultcalendars(req->accountid);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* The account exists but does not have a root mailbox. */
        jmap_error(req, json_pack("{s:s}", "type", "accountNoCalendars"));
        return 0;
    } else if (r) return r;

    /* Build callback data */
    int checkacl = strcmp(req->accountid, req->userid);
    struct getcalendarevents_rock rock = { NULL, req, &get, NULL /*mbox*/, checkacl };

    /* Parse request */
    jmap_get_parse(req, &parser, event_props, /*allow_null_ids*/1,
                   NULL, NULL, &get, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    rock.db = db = caldav_open_userid(req->accountid);
    if (!db) {
        syslog(LOG_ERR,
               "caldav_open_mailbox failed for user %s", req->accountid);
        r = IMAP_INTERNAL;
        goto done;
    }

    r = caldav_begin(db);
    if (r) {
        syslog(LOG_ERR,
               "caldav_begin failed for user %s", req->accountid);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Does the client request specific events? */
    if (JNOTNULL(get.ids)) {
        size_t i;
        json_t *jval;
        json_array_foreach(get.ids, i, jval) {
            const char *id = json_string_value(jval);
            size_t nfound = json_array_size(get.list);
            r = caldav_get_events(db, httpd_userid, NULL, id, &getcalendarevents_cb, &rock);
            if (r || nfound == json_array_size(get.list)) {
                json_array_append(get.not_found, jval);
            }
        }
    } else {
        r = caldav_get_events(db, httpd_userid, NULL, NULL, &getcalendarevents_cb, &rock);
        if (r) goto done;
    }

    r = caldav_commit(db);
    if (r) {
        syslog(LOG_ERR,
               "caldav_commit failed for user %s", req->accountid);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Build response */
    json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/0);
    get.state = xstrdup(json_string_value(jstate));
    json_decref(jstate);
    jmap_ok(req, jmap_get_reply(&get));

done:
    jmap_parser_fini(&parser);
    jmap_get_fini(&get);
    if (db) caldav_close(db);
    if (rock.mailbox) mailbox_close(&rock.mailbox);
    return r;
}

static int setcalendarevents_schedule(jmap_req_t *req,
                                      char **schedaddrp,
                                      icalcomponent *oldical,
                                      icalcomponent *ical,
                                      int mode)
{
    /* Determine if any scheduling is required. */
    icalcomponent *src = mode & JMAP_DESTROY ? oldical : ical;
    icalcomponent *comp =
        icalcomponent_get_first_component(src, ICAL_VEVENT_COMPONENT);
    icalproperty *prop =
        icalcomponent_get_first_property(comp, ICAL_ORGANIZER_PROPERTY);
    if (!prop) return 0;
    const char *organizer = icalproperty_get_organizer(prop);
    if (!organizer) return 0;
    if (!strncasecmp(organizer, "mailto:", 7)) organizer += 7;

    if (!*schedaddrp) {
        const char **hdr =
            spool_getheader(req->txn->req_hdrs, "Schedule-Address");
        if (hdr) *schedaddrp = xstrdup(hdr[0]);
    }

    /* XXX - after legacy records are gone, we can strip this and just not send a
     * cancellation if deleting a record which was never replied to... */
    if (!*schedaddrp) {
        /* userid corresponding to target */
        *schedaddrp = xstrdup(req->userid);

        /* or overridden address-set for target user */
        const char *annotname =
            DAV_ANNOT_NS "<" XML_NS_CALDAV ">calendar-user-address-set";
        char *mailboxname = caldav_mboxname(*schedaddrp, NULL);
        struct buf buf = BUF_INITIALIZER;
        int r = annotatemore_lookupmask(mailboxname, annotname,
                                        *schedaddrp, &buf);
        free(mailboxname);
        if (!r && buf.len > 7 && !strncasecmp(buf_cstring(&buf), "mailto:", 7)) {
            free(*schedaddrp);
            *schedaddrp = xstrdup(buf_cstring(&buf) + 7);
        }
        buf_free(&buf);
    }

    /* Validate create/update. */
    if (oldical && (mode & (JMAP_CREATE|JMAP_UPDATE))) {
        /* Don't allow ORGANIZER to be updated */
        const char *oldorganizer = NULL;

        icalcomponent *oldcomp = NULL;
        icalproperty *prop = NULL;
        oldcomp =
            icalcomponent_get_first_component(oldical, ICAL_VEVENT_COMPONENT);
        if (oldcomp) {
            prop = icalcomponent_get_first_property(oldcomp,
                                                    ICAL_ORGANIZER_PROPERTY);
        }
        if (prop) oldorganizer = icalproperty_get_organizer(prop);
        if (oldorganizer) {
            if (!strncasecmp(oldorganizer, "mailto:", 7)) oldorganizer += 7;
            if (strcasecmp(oldorganizer, organizer)) {
                /* XXX This should become a set error. */
                return 0;
            }
        }
    }

    if (organizer &&
            /* XXX Hack for Outlook */ icalcomponent_get_first_invitee(comp)) {
        /* Send scheduling message. */
        if (!strcmpsafe(organizer, *schedaddrp)) {
            /* Organizer scheduling object resource */
            sched_request(req->userid, *schedaddrp, oldical, ical);
        } else {
            /* Attendee scheduling object resource */
            int omit_reply = 0;
            if (oldical && (mode & JMAP_DESTROY)) {
                for (prop = icalcomponent_get_first_property(comp, ICAL_ATTENDEE_PROPERTY);
                     prop;
                     prop = icalcomponent_get_next_property(comp, ICAL_ATTENDEE_PROPERTY)) {
                    const char *addr = icalproperty_get_attendee(prop);
                    if (!addr || strncasecmp(addr, "mailto:", 7) || strcmp(addr + 7, *schedaddrp))
                        continue;
                    icalparameter *param = icalproperty_get_first_parameter(prop, ICAL_PARTSTAT_PARAMETER);
                    omit_reply = !param || icalparameter_get_partstat(param) == ICAL_PARTSTAT_NEEDSACTION;
                    break;
                }
            }
            if (!omit_reply)
                sched_reply(req->userid, *schedaddrp, oldical, ical);
        }
    }

    return 0;
}

static void remove_itip_properties(icalcomponent *ical)
{
    icalproperty *prop, *next;
    icalproperty_kind kind = ICAL_METHOD_PROPERTY;

    for (prop = icalcomponent_get_first_property(ical, kind);
         prop;
         prop = next) {

        next = icalcomponent_get_next_property(ical, kind);
        icalcomponent_remove_property(ical, prop);
        icalproperty_free(prop);
    }

}

static int setcalendarevents_create(jmap_req_t *req,
                                    const char *account_id,
                                    json_t *event,
                                    struct caldav_db *db,
                                    json_t *invalid,
                                    json_t *create)
{
    int r, pe;
    int needrights = DACL_WRITEPROPS|DACL_WRITECONT;
    char *uid = NULL;

    struct mailbox *mbox = NULL;
    char *mboxname = NULL;
    char *resource = NULL;

    icalcomponent *ical = NULL;
    const char *calendarId = NULL;
    char *schedule_address = NULL;

    if ((uid = (char *) json_string_value(json_object_get(event, "uid")))) {
        /* Use custom iCalendar UID from request object */
        uid = xstrdup(uid);
    }  else {
        /* Create a iCalendar UID */
        uid = xstrdup(makeuuid());
    }

    /* Validate calendarId */
    pe = jmap_readprop(event, "calendarId", 1, invalid, "s", &calendarId);
    if (pe > 0 && *calendarId &&*calendarId == '#') {
        calendarId = jmap_lookup_id(req, calendarId + 1);
        if (!calendarId) {
            json_array_append_new(invalid, json_string("calendarId"));
        }
    }
    if (json_array_size(invalid)) {
        free(uid);
        return 0;
    }

    /* Determine mailbox and resource name of calendar event.
     * We attempt to reuse the UID as DAV resource name; but
     * only if it looks like a reasonable URL path segment. */
    struct buf buf = BUF_INITIALIZER;
    mboxname = caldav_mboxname(account_id, calendarId);
    const char *p;
    for (p = uid; *p; p++) {
        if ((*p >= '0' && *p <= '9') ||
            (*p >= 'a' && *p <= 'z') ||
            (*p >= 'A' && *p <= 'Z') ||
            (*p == '@' || *p == '.') ||
            (*p == '_' || *p == '-')) {
            continue;
        }
        break;
    }
    if (*p == '\0' && p - uid >= 16 && p - uid <= 200) {
        buf_setcstr(&buf, uid);
    } else {
        buf_setcstr(&buf, makeuuid());
    }
    buf_appendcstr(&buf, ".ics");
    resource = buf_newcstring(&buf);
    buf_free(&buf);

    /* Check permissions. */
    if (!jmap_hasrights_byname(req, mboxname, needrights)) {
        json_array_append_new(invalid, json_string("calendarId"));
        r = 0; goto done;
    }

    /* Open mailbox for writing */
    r = mailbox_open_iwl(mboxname, &mbox);
    if (r) {
        syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s", mboxname, error_message(r));
        if (r == IMAP_MAILBOX_NONEXISTENT) {
            json_array_append_new(invalid, json_string("calendarId"));
            r = 0;
        }
        goto done;
    }

    /* Convert the JMAP calendar event to ical. */
    if (!json_object_get(event, "uid")) {
        json_object_set_new(event, "uid", json_string(uid));
    }

    if (!json_object_get(event, "created") || !json_object_get(event, "updated")) {
        char datestr[RFC3339_DATETIME_MAX+1];
        time_to_rfc3339(time(NULL), datestr, RFC3339_DATETIME_MAX);
        datestr[RFC3339_DATETIME_MAX] = '\0';
        if (!json_object_get(event, "created")) {
            json_object_set_new(event, "created", json_string(datestr));
        }
        if (!json_object_get(event, "updated")) {
            json_object_set_new(event, "updated", json_string(datestr));
        }
    }
    ical = jmapical_toical(event, invalid);

    json_t *jparticipantId = json_object_get(event, "participantId");
    if (json_is_string(jparticipantId)) {
        const char *participant_id = json_string_value(jparticipantId);
        json_t *participants = json_object_get(event, "participants");
        json_t *participant = json_object_get(participants, participant_id);
        schedule_address = xstrdupnull(json_string_value(json_object_get(participant, "email")));
    }
    else if (JNOTNULL(jparticipantId)) {
        json_array_append_new(invalid, json_string("participantId"));
    }

    if (json_array_size(invalid)) {
        r = 0;
        goto done;
    } else if (!ical) {
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Handle scheduling. */
    r = setcalendarevents_schedule(req, &schedule_address,
                                   NULL, ical, JMAP_CREATE);
    if (r) goto done;

    /* Remove METHOD property */
    remove_itip_properties(ical);

    /* Store the VEVENT. */
    struct transaction_t txn;
    memset(&txn, 0, sizeof(struct transaction_t));
    txn.req_hdrs = spool_new_hdrcache();
    /* XXX - fix userid */

    /* Locate the mailbox */
    r = http_mlookup(mbox->name, &txn.req_tgt.mbentry, NULL);
    if (r) {
        syslog(LOG_ERR, "mlookup(%s) failed: %s", mbox->name, error_message(r));
    }
    else {
        r = caldav_store_resource(&txn, ical, mbox, resource, 0,
                                  db, 0, httpd_userid, schedule_address);
    }
    mboxlist_entry_free(&txn.req_tgt.mbentry);
    spool_free_hdrcache(txn.req_hdrs);
    buf_free(&txn.buf);
    if (r && r != HTTP_CREATED && r != HTTP_NO_CONTENT) {
        syslog(LOG_ERR, "caldav_store_resource failed for user %s: %s",
               req->accountid, error_message(r));
        goto done;
    }
    r = 0;
    json_object_set_new(create, "uid", json_string(uid));

    char *xhref = jmap_xhref(mbox->name, resource);
    json_object_set_new(create, "x-href", json_string(xhref));
    free(xhref);

done:
    if (mbox) mailbox_close(&mbox);
    if (ical) icalcomponent_free(ical);
    free(schedule_address);
    free(resource);
    free(mboxname);
    free(uid);
    return r;
}

static int setcalendarevents_update(jmap_req_t *req,
                                    json_t *event_patch,
                                    const char *id,
                                    struct caldav_db *db,
                                    json_t *invalid,
                                    json_t *update)
{
    int r, pe;
    int needrights = DACL_RMRSRC|DACL_WRITEPROPS|DACL_WRITECONT;

    struct caldav_data *cdata = NULL;
    struct mailbox *mbox = NULL;
    char *mboxname = NULL;
    struct mailbox *dstmbox = NULL;
    char *dstmboxname = NULL;
    struct mboxevent *mboxevent = NULL;
    char *resource = NULL;

    icalcomponent *oldical = NULL;
    icalcomponent *ical = NULL;
    struct index_record record;
    const char *calendarId = NULL;
    char *schedule_address = NULL;

    /* Validate calendarId */
    pe = jmap_readprop(event_patch, "calendarId", 0, invalid, "s", &calendarId);
    if (pe > 0 && *calendarId && *calendarId == '#') {
        calendarId = jmap_lookup_id(req, calendarId + 1);
        if (!calendarId) {
            json_array_append_new(invalid, json_string("calendarId"));
        }
    }
    if (json_array_size(invalid)) {
        return 0;
    }

    /* Determine mailbox and resource name of calendar event. */
    r = caldav_lookup_uid(db, id, &cdata);
    if (r && r != CYRUSDB_NOTFOUND) {
        syslog(LOG_ERR,
               "caldav_lookup_uid(%s) failed: %s", id, error_message(r));
        goto done;
    }
    if (r == CYRUSDB_NOTFOUND || !cdata->dav.alive ||
            !cdata->dav.rowid || !cdata->dav.imap_uid ||
            cdata->comp_type != CAL_COMP_VEVENT) {
        r = IMAP_NOTFOUND;
        goto done;
    }
    mboxname = xstrdup(cdata->dav.mailbox);
    resource = xstrdup(cdata->dav.resource);

    /* Check permissions. */
    if (!jmap_hasrights_byname(req, mboxname, needrights)) {
        json_array_append_new(invalid, json_string("calendarId"));
        r = 0;
        goto done;
    }

    /* Open mailbox for writing */
    r = mailbox_open_iwl(mboxname, &mbox);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        json_array_append_new(invalid, json_string("calendarId"));
        r = 0;
        goto done;
    }
    else if (r) {
        syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s",
                mboxname, error_message(r));
        goto done;
    }

    /* Fetch index record for the resource */
    memset(&record, 0, sizeof(struct index_record));
    r = mailbox_find_index_record(mbox, cdata->dav.imap_uid, &record);
    if (r == IMAP_NOTFOUND) {
        json_array_append_new(invalid, json_string("calendarId"));
        r = 0;
        goto done;
    } else if (r) {
        syslog(LOG_ERR, "mailbox_index_record(0x%x) failed: %s",
                cdata->dav.imap_uid, error_message(r));
        goto done;
    }
    /* Load VEVENT from record, personalizing as needed. */
    oldical = caldav_record_to_ical(mbox, cdata, httpd_userid, &schedule_address);
    if (!oldical) {
        syslog(LOG_ERR, "record_to_ical failed for record %u:%s",
                cdata->dav.imap_uid, mbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Patch the old JMAP calendar event */
    json_t *old_event = jmapical_tojmap(oldical, NULL);
    if (!old_event) {
        syslog(LOG_ERR, "jmapical_tojmap: can't convert oldical %u:%s",
                cdata->dav.imap_uid, mbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }
    json_object_del(old_event, "updated");
    json_t *new_event = jmap_patchobject_apply(old_event, event_patch);
    ical = jmapical_toical(new_event, invalid);

    json_t *jparticipantId = json_object_get(new_event, "participantId");
    if (json_is_string(jparticipantId)) {
        const char *participant_id = json_string_value(jparticipantId);
        json_t *participants = json_object_get(new_event, "participants");
        json_t *participant = json_object_get(participants, participant_id);
        schedule_address = xstrdupnull(json_string_value(json_object_get(participant, "email")));
    }
    else if (JNOTNULL(jparticipantId)) {
        json_array_append_new(invalid, json_string("participantId"));
    }

    json_t *jnewsequence = json_object_get(event_patch, "sequence");
    if (!JNOTNULL(jnewsequence)) {
        json_t *joldseq = json_object_get(old_event, "sequence");
        int oldseq = joldseq ? json_integer_value(joldseq) : 0;
        int newseq = oldseq + 1;
        json_object_set_new(new_event, "sequence", json_integer(newseq));
        json_object_set_new(update, "sequence", json_integer(newseq));
    }

    json_decref(new_event);
    json_decref(old_event);

    if (json_array_size(invalid)) {
        r = 0;
        goto done;
    } else if (!ical) {
        r = IMAP_INTERNAL;
        goto done;
    }

    if (calendarId) {
        /* Check, if we need to move the event. */
        dstmboxname = caldav_mboxname(req->accountid, calendarId);
        if (strcmp(mbox->name, dstmboxname)) {
            /* Check permissions */
            if (!jmap_hasrights_byname(req, dstmboxname, needrights)) {
                json_array_append_new(invalid, json_string("calendarId"));
                r = 0;
                goto done;
            }
            /* Open destination mailbox for writing. */
            r = mailbox_open_iwl(dstmboxname, &dstmbox);
            if (r == IMAP_MAILBOX_NONEXISTENT) {
                json_array_append_new(invalid, json_string("calendarId"));
                r = 0;
                goto done;
            } else if (r) {
                syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s",
                        dstmboxname, error_message(r));
                goto done;
            }
        }
    }

    /* Handle scheduling. */
    r = setcalendarevents_schedule(req, &schedule_address,
                                   oldical, ical, JMAP_UPDATE);
    if (r) goto done;


    if (dstmbox) {
        /* Expunge the resource from mailbox. */
        record.internal_flags |= FLAG_INTERNAL_EXPUNGED;
        mboxevent = mboxevent_new(EVENT_MESSAGE_EXPUNGE);
        r = mailbox_rewrite_index_record(mbox, &record);
        if (r) {
            syslog(LOG_ERR, "mailbox_rewrite_index_record (%s) failed: %s",
                    cdata->dav.mailbox, error_message(r));
            mailbox_close(&mbox);
            goto done;
        }
        mboxevent_extract_record(mboxevent, mbox, &record);
        mboxevent_extract_mailbox(mboxevent, mbox);
        mboxevent_set_numunseen(mboxevent, mbox, -1);
        mboxevent_set_access(mboxevent, NULL, NULL,
                             req->userid, cdata->dav.mailbox, 0);
        mailbox_close(&mbox);
        mboxevent_notify(&mboxevent);
        mboxevent_free(&mboxevent);

        /* Close the mailbox we moved the event from. */
        mailbox_close(&mbox);
        mbox = dstmbox;
        dstmbox = NULL;
        free(mboxname);
        mboxname = dstmboxname;
        dstmboxname = NULL;
    }

    /* Remove METHOD property */
    remove_itip_properties(ical);

    /* Store the updated VEVENT. */
    struct transaction_t txn;
    memset(&txn, 0, sizeof(struct transaction_t));
    txn.req_hdrs = spool_new_hdrcache();
    /* XXX - fix userid */
    r = http_mlookup(mbox->name, &txn.req_tgt.mbentry, NULL);
    if (r) {
        syslog(LOG_ERR, "mlookup(%s) failed: %s", mbox->name, error_message(r));
    }
    else {
        r = caldav_store_resource(&txn, ical, mbox, resource, record.createdmodseq,
                                  db, 0, httpd_userid, schedule_address);
    }
    transaction_free(&txn);
    if (r && r != HTTP_CREATED && r != HTTP_NO_CONTENT) {
        syslog(LOG_ERR, "caldav_store_resource failed for user %s: %s",
               req->accountid, error_message(r));
        goto done;
    }
    r = 0;

done:
    if (mbox) mailbox_close(&mbox);
    if (dstmbox) mailbox_close(&dstmbox);
    if (ical) icalcomponent_free(ical);
    if (oldical) icalcomponent_free(oldical);
    free(schedule_address);
    free(dstmboxname);
    free(resource);
    free(mboxname);
    return r;
}

static int setcalendarevents_destroy(jmap_req_t *req,
                                     const char *id,
                                     struct caldav_db *db)
{
    int r;
    int needrights = DACL_RMRSRC;

    struct caldav_data *cdata = NULL;
    struct mailbox *mbox = NULL;
    char *mboxname = NULL;
    struct mboxevent *mboxevent = NULL;
    char *resource = NULL;

    icalcomponent *oldical = NULL;
    icalcomponent *ical = NULL;
    struct index_record record;
    char *schedule_address = NULL;

    /* Determine mailbox and resource name of calendar event. */
    r = caldav_lookup_uid(db, id, &cdata);
    if (r) {
        syslog(LOG_ERR,
               "caldav_lookup_uid(%s) failed: %s", id, cyrusdb_strerror(r));
        r = CYRUSDB_NOTFOUND ? IMAP_NOTFOUND : IMAP_INTERNAL;
        goto done;
    }
    mboxname = xstrdup(cdata->dav.mailbox);
    resource = xstrdup(cdata->dav.resource);

    /* Check permissions. */
    if (!jmap_hasrights_byname(req, mboxname, DACL_READ)) {
        r = IMAP_NOTFOUND;
        goto done;
    }
    if (!jmap_hasrights_byname(req, mboxname, needrights)) {
        r = IMAP_PERMISSION_DENIED;
        goto done;
    }

    /* Open mailbox for writing */
    r = mailbox_open_iwl(mboxname, &mbox);
    if (r) {
        syslog(LOG_ERR, "mailbox_open_iwl(%s) failed: %s",
                mboxname, error_message(r));
        goto done;
    }

    /* Fetch index record for the resource. Need this for scheduling. */
    memset(&record, 0, sizeof(struct index_record));
    r = mailbox_find_index_record(mbox, cdata->dav.imap_uid, &record);
    if (r) {
        syslog(LOG_ERR, "mailbox_index_record(0x%x) failed: %s",
                cdata->dav.imap_uid, error_message(r));
        goto done;
    }
    /* Load VEVENT from record. */
    oldical = record_to_ical(mbox, &record, &schedule_address);
    if (!oldical) {
        syslog(LOG_ERR, "record_to_ical failed for record %u:%s",
                cdata->dav.imap_uid, mbox->name);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Handle scheduling. */
    r = setcalendarevents_schedule(req, &schedule_address,
                                   oldical, ical, JMAP_DESTROY);
    if (r) goto done;


    /* Expunge the resource from mailbox. */
    record.internal_flags |= FLAG_INTERNAL_EXPUNGED;
    mboxevent = mboxevent_new(EVENT_MESSAGE_EXPUNGE);
    r = mailbox_rewrite_index_record(mbox, &record);
    if (r) {
        syslog(LOG_ERR, "mailbox_rewrite_index_record (%s) failed: %s",
                cdata->dav.mailbox, error_message(r));
        mailbox_close(&mbox);
        goto done;
    }
    mboxevent_extract_record(mboxevent, mbox, &record);
    mboxevent_extract_mailbox(mboxevent, mbox);
    mboxevent_set_numunseen(mboxevent, mbox, -1);
    mboxevent_set_access(mboxevent, NULL, NULL,
                         req->userid, cdata->dav.mailbox, 0);
    mailbox_close(&mbox);
    mboxevent_notify(&mboxevent);
    mboxevent_free(&mboxevent);

    /* Keep the VEVENT in the database but set alive to 0, to report
     * with CalendarEvents/changes. */
    cdata->dav.alive = 0;
    cdata->dav.modseq = record.modseq;
    cdata->dav.imap_uid = record.uid;
    r = caldav_write(db, cdata);

done:
    if (mbox) mailbox_close(&mbox);
    if (oldical) icalcomponent_free(oldical);
    free(schedule_address);
    free(resource);
    free(mboxname);
    return r;
}

static int jmap_calendarevent_set(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_set set;
    json_t *err = NULL;
    struct caldav_db *db = NULL;
    int r = 0;

    /* Parse arguments */
    jmap_set_parse(req, &parser, event_props, NULL, NULL, &set, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    if (set.if_in_state) {
        /* TODO rewrite state function to use char* not json_t* */
        json_t *jstate = json_string(set.if_in_state);
        if (jmap_cmpstate(req, jstate, MBTYPE_CALENDAR)) {
            jmap_error(req, json_pack("{s:s}", "type", "stateMismatch"));
            goto done;
        }
        json_decref(jstate);
        set.old_state = xstrdup(set.if_in_state);
    }
    else {
        json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/0);
        set.old_state = xstrdup(json_string_value(jstate));
        json_decref(jstate);
    }

    r = caldav_create_defaultcalendars(req->accountid);
    if (r == IMAP_MAILBOX_NONEXISTENT) {
        /* The account exists but does not have a root mailbox. */
        json_t *err = json_pack("{s:s}", "type", "accountNoCalendars");
        json_array_append_new(req->response, json_pack("[s,o,s]",
                    "error", err, req->tag));
        return 0;
    } else if (r) return r;

    db = caldav_open_userid(req->accountid);
    if (!db) {
        syslog(LOG_ERR, "caldav_open_mailbox failed for user %s", req->userid);
        r = IMAP_INTERNAL;
        goto done;
    }


    /* create */
    const char *key;
    json_t *arg;
    json_object_foreach(set.create, key, arg) {
        /* Validate calendar event id. */
        if (!strlen(key)) {
            json_t *err= json_pack("{s:s}", "type", "invalidArguments");
            json_object_set_new(set.not_created, key, err);
            continue;
        }

        /* Create the calendar event. */
        json_t *invalid = json_pack("[]");
        json_t *create = json_pack("{}");
        r = setcalendarevents_create(req, req->accountid, arg, db, invalid, create);
        if (r) {
            json_t *err;
            switch (r) {
                case HTTP_FORBIDDEN:
                case IMAP_PERMISSION_DENIED:
                    err = json_pack("{s:s}", "type", "forbidden");
                    break;
                case IMAP_QUOTA_EXCEEDED:
                    err = json_pack("{s:s}", "type", "overQuota");
                    break;
                default:
                    err = jmap_server_error(r);
            }
            json_object_set_new(set.not_created, key, err);
            json_decref(create);
            r = 0;
            continue;
        }
        if (json_array_size(invalid)) {
            json_t *err = json_pack("{s:s s:o}",
                                    "type", "invalidProperties",
                                    "properties", invalid);
            json_object_set_new(set.not_created, key, err);
            json_decref(create);
            continue;
        }
        json_decref(invalid);

        /* Report calendar event as created. */
        const char *uid = json_string_value(json_object_get(create, "uid"));
        json_object_set_new(create, "id", json_string(uid));
        json_object_set_new(set.created, key, create);
        jmap_add_id(req, key, uid);
    }


    /* update */
    const char *uid;

    json_object_foreach(set.update, uid, arg) {
        const char *val = NULL;

        /* Validate uid. */
        if (!uid) {
            continue;
        }
        if (uid && uid[0] == '#') {
            const char *newuid = jmap_lookup_id(req, uid + 1);
            if (!newuid) {
                json_t *err = json_pack("{s:s}", "type", "notFound");
                json_object_set_new(set.not_updated, uid, err);
                continue;
            }
            uid = newuid;
        }

        if ((val = (char *)json_string_value(json_object_get(arg, "uid")))) {
            /* The uid property must match the current iCalendar UID */
            if (strcmp(val, uid)) {
                json_t *err = json_pack(
                    "{s:s, s:o}",
                    "type", "invalidProperties",
                    "properties", json_pack("[s]"));
                json_object_set_new(set.not_updated, uid, err);
                continue;
            }
        }

        /* Update the calendar event. */
        json_t *invalid = json_pack("[]");
        json_t *update = json_pack("{}");
        r = setcalendarevents_update(req, arg, uid, db, invalid, update);
        if (r) {
            json_t *err;
            switch (r) {
                case IMAP_NOTFOUND:
                    err = json_pack("{s:s}", "type", "notFound");
                    break;
                case HTTP_FORBIDDEN:
                case IMAP_PERMISSION_DENIED:
                    err = json_pack("{s:s}", "type", "forbidden");
                    break;
                case HTTP_NO_STORAGE:
                case IMAP_QUOTA_EXCEEDED:
                    err = json_pack("{s:s}", "type", "overQuota");
                    break;
                default:
                    err = jmap_server_error(r);
            }
            json_object_set_new(set.not_updated, uid, err);
            json_decref(invalid);
            json_decref(update);
            r = 0;
            continue;
        }
        if (json_array_size(invalid)) {
            json_t *err = json_pack(
                "{s:s, s:o}", "type", "invalidProperties",
                "properties", invalid);
            json_object_set_new(set.not_updated, uid, err);
            continue;
        }
        json_decref(invalid);

        if(!json_object_size(update)) {
            json_decref(update);
            update = json_null();
        }

        /* Report calendar event as updated. */
        json_object_set_new(set.updated, uid, update);
    }


    /* destroy */
    size_t index;
    json_t *juid;

    json_array_foreach(set.destroy, index, juid) {
        /* Validate uid. */
        const char *uid = json_string_value(juid);
        if (!uid) {
            continue;
        }
        if (uid && uid[0] == '#') {
            const char *newuid = jmap_lookup_id(req, uid + 1);
            if (!newuid) {
                json_t *err = json_pack("{s:s}", "type", "notFound");
                json_object_set_new(set.not_destroyed, uid, err);
                continue;
            }
            uid = newuid;
        }

        /* Destroy the calendar event. */
        r = setcalendarevents_destroy(req, uid, db);
        if (r == IMAP_NOTFOUND) {
            json_t *err = json_pack("{s:s}", "type", "notFound");
            json_object_set_new(set.not_destroyed, uid, err);
            r = 0;
            continue;
        } else if (r == IMAP_PERMISSION_DENIED) {
            json_t *err = json_pack("{s:s}", "type", "forbidden");
            json_object_set_new(set.not_destroyed, uid, err);
            r = 0;
            continue;
        } else if (r) {
            goto done;
        }

        /* Report calendar event as destroyed. */
        json_array_append_new(set.destroyed, json_string(uid));
    }


    // TODO refactor jmap_getstate to return a string, once
    // all code has been migrated to the new JMAP parser.
    json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/1);
    set.new_state = xstrdup(json_string_value(jstate));
    json_decref(jstate);

    jmap_ok(req, jmap_set_reply(&set));

done:
    jmap_parser_fini(&parser);
    jmap_set_fini(&set);
    if (db) caldav_close(db);
    return r;
}

struct geteventchanges_rock {
    jmap_req_t *req;
    struct jmap_changes *changes;
    size_t seen_records;
    modseq_t highestmodseq;
    int check_acl;
    hash_table *mboxrights;
};

static void strip_spurious_deletes(struct geteventchanges_rock *urock)
{
    /* if something is mentioned in both DELETEs and UPDATEs, it's probably
     * a move.  O(N*M) algorithm, but there are rarely many, and the alternative
     * of a hash will cost more */
    unsigned i, j;

    for (i = 0; i < json_array_size(urock->changes->destroyed); i++) {
        const char *del = json_string_value(json_array_get(urock->changes->destroyed, i));

        for (j = 0; j < json_array_size(urock->changes->updated); j++) {
            const char *up =
                json_string_value(json_array_get(urock->changes->updated, j));
            if (!strcmpsafe(del, up)) {
                json_array_remove(urock->changes->destroyed, i--);
                break;
            }
        }
    }
}

static int geteventchanges_cb(void *vrock, struct caldav_data *cdata)
{
    struct geteventchanges_rock *rock = vrock;
    jmap_req_t *req = rock->req;
    struct jmap_changes *changes = rock->changes;

    /* Check permissions */
    if (!jmap_hasrights_byname(req, cdata->dav.mailbox, DACL_READ))
        return 0;

    if (cdata->comp_type != CAL_COMP_VEVENT)
        return 0;

    /* Count, but don't process items that exceed the maximum record count. */
    if (changes->max_changes && ++(rock->seen_records) > changes->max_changes) {
        changes->has_more_changes = 1;
        return 0;
    }

    /* Report item as updated or destroyed. */
    if (cdata->dav.alive) {
        if (cdata->dav.createdmodseq <= changes->since_modseq)
            json_array_append_new(changes->updated, json_string(cdata->ical_uid));
        else
            json_array_append_new(changes->created, json_string(cdata->ical_uid));
    } else {
        if (cdata->dav.createdmodseq <= changes->since_modseq)
            json_array_append_new(changes->destroyed, json_string(cdata->ical_uid));
    }

    if (cdata->dav.modseq > rock->highestmodseq) {
        rock->highestmodseq = cdata->dav.modseq;
    }

    return 0;
}

static int jmap_calendarevent_changes(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_changes changes;
    json_t *err = NULL;
    struct caldav_db *db;
    struct geteventchanges_rock rock = {
        req,
        &changes,
        0            /*seen_records*/,
        0            /*highestmodseq*/,
        strcmp(req->accountid, req->userid) /* check_acl */,
        NULL         /*mboxrights*/
    };
    int r = 0;

    db = caldav_open_userid(req->accountid);
    if (!db) {
        syslog(LOG_ERR, "caldav_open_mailbox failed for user %s", req->accountid);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Parse request */
    jmap_changes_parse(req, &parser, NULL, NULL, &changes, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    /* Lookup changes. */
    r = caldav_get_updates(db, changes.since_modseq, NULL /*mboxname*/,
                           CAL_COMP_VEVENT, 
                           changes.max_changes ? (int) changes.max_changes + 1 : -1,
                           &geteventchanges_cb, &rock);
    if (r) goto done;
    strip_spurious_deletes(&rock);

    /* Determine new state. */
    changes.new_modseq = changes.has_more_changes ?
        rock.highestmodseq : jmap_highestmodseq(req, MBTYPE_CALENDAR);

    /* Build response */
    jmap_ok(req, jmap_changes_reply(&changes));

  done:
    jmap_changes_fini(&changes);
    jmap_parser_fini(&parser);
    if (rock.mboxrights) {
        free_hash_table(rock.mboxrights, free);
        free(rock.mboxrights);
    }
    if (db) caldav_close(db);
    if (r) {
        jmap_error(req, jmap_server_error(r));
    }
    return 0;
}

static void match_fuzzy(search_expr_t *parent, const char *s, const char *name)
{
    search_expr_t *e;
    const search_attr_t *attr = search_attr_find(name);

    e = search_expr_new(parent, SEOP_FUZZYMATCH);
    e->attr = attr;
    e->value.s = xstrdup(s);
    if (!e->value.s) {
        e->op = SEOP_FALSE;
        e->attr = NULL;
    }
}

static search_expr_t *buildsearch(jmap_req_t *req, json_t *filter,
                                  search_expr_t *parent)
{
    search_expr_t *this, *e;
    const char *s;
    size_t i;
    json_t *val, *arg;

    if (!JNOTNULL(filter)) {
        return search_expr_new(parent, SEOP_TRUE);
    }

    if ((s = json_string_value(json_object_get(filter, "operator")))) {
        enum search_op op = SEOP_UNKNOWN;

        if (!strcmp("AND", s)) {
            op = SEOP_AND;
        } else if (!strcmp("OR", s)) {
            op = SEOP_OR;
        } else if (!strcmp("NOT", s)) {
            op = SEOP_NOT;
        }

        this = search_expr_new(parent, op);
        e = op == SEOP_NOT ? search_expr_new(this, SEOP_OR) : this;

        json_array_foreach(json_object_get(filter, "conditions"), i, val) {
            buildsearch(req, val, e);
        }
    } else {
        this = search_expr_new(parent, SEOP_AND);

        if ((arg = json_object_get(filter, "inCalendars"))) {
            e = search_expr_new(this, SEOP_OR);
            json_array_foreach(arg, i, val) {
                const char *id = json_string_value(val);
                search_expr_t *m = search_expr_new(e, SEOP_MATCH);
                m->attr = search_attr_find("folder");
                m->value.s = caldav_mboxname(req->accountid, id);
            }
        }

        if ((s = json_string_value(json_object_get(filter, "text")))) {
            e = search_expr_new(this, SEOP_OR);
            match_fuzzy(e, s, "body");
            match_fuzzy(e, s, "subject");
            match_fuzzy(e, s, "from");
            match_fuzzy(e, s, "to");
            match_fuzzy(e, s, "location");
        }
        if ((s = json_string_value(json_object_get(filter, "title")))) {
            match_fuzzy(this, s, "subject");
        }
        if ((s = json_string_value(json_object_get(filter, "description")))) {
            match_fuzzy(this, s, "body");
        }
        if ((s = json_string_value(json_object_get(filter, "location")))) {
            match_fuzzy(this, s, "location");
        }
        if ((s = json_string_value(json_object_get(filter, "owner")))) {
            match_fuzzy(this, s, "from");
        }
        if ((s = json_string_value(json_object_get(filter, "attendee")))) {
            match_fuzzy(this, s, "to");
        }
    }

    return this;
}

static void filter_timerange(json_t *filter, time_t *before, time_t *after,
                             int *skip_search)
{
    *before = caldav_eternity;
    *after = caldav_epoch;

    if (!JNOTNULL(filter)) {
        return;
    }

    if (json_object_get(filter, "conditions")) {
        json_t *val;
        size_t i;
        time_t bf, af;

        json_array_foreach(json_object_get(filter, "conditions"), i, val) {
            const char *op =
                json_string_value(json_object_get(filter, "operator"));
            bf = caldav_eternity;
            af = caldav_epoch;

            filter_timerange(val, &bf, &af, skip_search);

            if (bf != caldav_eternity) {
                if (!strcmp(op, "OR")) {
                    if (*before == caldav_eternity || *before < bf) {
                        *before = bf;
                    }
                }
                else if (!strcmp(op, "AND")) {
                    if (*before == caldav_eternity || *before > bf) {
                        *before = bf;
                    }
                }
                else if (!strcmp(op, "NOT")) {
                    if (*after == caldav_epoch || *after < bf) {
                        *after = bf;
                    }
                }
            }

            if (af != caldav_epoch) {
                if (!strcmp(op, "OR")) {
                    if (*after == caldav_epoch || *after > af) {
                        *after = af;
                    }
                }
                else if (!strcmp(op, "AND")) {
                    if (*after == caldav_epoch || *after < af) {
                        *after = af;
                    }
                }
                else if (!strcmp(op, "NOT")) {
                    if (*before == caldav_eternity || *before < af) {
                        *before = af;
                    }
                }
            }
        }
    } else {
        const char *sb = json_string_value(json_object_get(filter, "before"));
        const char *sa = json_string_value(json_object_get(filter, "after"));

        if (!sb || time_from_iso8601(sb, before) == -1) {
            *before = caldav_eternity;
        }
        if (!sa || time_from_iso8601(sa, after) == -1) {
            *after = caldav_epoch;
        }

        if (json_object_get(filter, "inCalendars") ||
            json_object_get(filter, "text") ||
            json_object_get(filter, "title") ||
            json_object_get(filter, "description") ||
            json_object_get(filter, "location") ||
            json_object_get(filter, "owner") ||
            json_object_get(filter, "attendee")) {

            *skip_search = 0;
        }
    }
}

struct search_timerange_rock {
    jmap_req_t *req;
    hash_table *search_timerange;  /* hash of all UIDs within timerange */
    size_t seen;               /* seen uids inside and outside of window */
    int check_acl;             /* if true, check mailbox ACL for read access */
    hash_table *mboxrights;    /* cache of (int) ACLs, keyed by mailbox name */

    int build_result; /* if true, filter search window and buidl result */
    size_t limit;     /* window limit */
    size_t pos;       /* window start position */
    json_t *result;   /* windowed search result */
};

static int search_timerange_cb(void *vrock, struct caldav_data *cdata)
{
    struct search_timerange_rock *rock = vrock;
    jmap_req_t *req = rock->req;

    /* Ignore tombstones */
    if (!cdata->dav.alive) {
        return 0;
    }

    /* check that it's the right type */
    if (cdata->comp_type != CAL_COMP_VEVENT)
        return 0;

    /* Check permissions */
    if (!jmap_hasrights_byname(req, cdata->dav.mailbox, DACL_READ))
        return 0;

    /* Keep track of this event */
    hash_insert(cdata->ical_uid, (void*)1, rock->search_timerange);
    rock->seen++;

    if (rock->build_result) {
        /* Is it within the search window? */
        if (rock->pos > rock->seen) {
            return 0;
        }
        if (rock->limit && json_array_size(rock->result) >= rock->limit) {
            return 0;
        }
        /* Add the event to the result list */
        json_array_append_new(rock->result, json_string(cdata->ical_uid));
    }
    return 0;
}

static int jmapevent_search(jmap_req_t *req,  struct jmap_query *jquery)
{
    int r, i;
    json_t *filter = jquery->filter;
    size_t limit = jquery->limit;
    size_t pos = jquery->position;
    size_t *total = &jquery->total;
    json_t **eventids = &jquery->ids;
    struct searchargs *searchargs = NULL;
    struct index_init init;
    struct index_state *state = NULL;
    search_query_t *query = NULL;
    struct caldav_db *db = NULL;
    time_t before, after;
    char *icalbefore = NULL, *icalafter = NULL;
    hash_table *search_timerange = NULL;
    int skip_search = 1;
    icaltimezone *utc = icaltimezone_get_utc_timezone();
    struct sortcrit *sortcrit = NULL;
    hash_table mboxrights = HASH_TABLE_INITIALIZER;
    int check_acl = strcmp(req->accountid, req->userid);

    if (check_acl) {
        construct_hash_table(&mboxrights, 128, 0);
    }

    /* Initialize return values */
    *total = 0;

    /* Determine the filter timerange, if any */
    filter_timerange(filter, &before, &after, &skip_search);
    if (before != caldav_eternity) {
        icaltimetype t = icaltime_from_timet_with_zone(before, 0, utc);
        icalbefore = icaltime_as_ical_string_r(t);
    }
    if (after != caldav_epoch) {
        icaltimetype t = icaltime_from_timet_with_zone(after, 0, utc);
        icalafter = icaltime_as_ical_string_r(t);
    }
    if (!icalbefore && !icalafter) {
        skip_search = 0;
    }

    /* Open the CalDAV database */
    db = caldav_open_userid(req->accountid);
    if (!db) {
        syslog(LOG_ERR,
               "caldav_open_mailbox failed for user %s", req->accountid);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Filter events by timerange */
    if (before != caldav_eternity || after != caldav_epoch) {
        search_timerange = xzmalloc(sizeof(hash_table));
        construct_hash_table(search_timerange, 64, 0);

        struct search_timerange_rock rock = {
            req,
            search_timerange,
            0, /*seen*/
            check_acl,
            &mboxrights,
            skip_search, /*build_result*/
            limit,
            pos,
            *eventids /*result*/
        };
        r = caldav_foreach_timerange(db, NULL,
                                     after, before, search_timerange_cb, &rock);
        if (r) goto done;

        *total = rock.seen;
    }

    /* Can we skip search? */
    if (skip_search) goto done;

    /* Reset search results */
    *total = 0;
    json_array_clear(*eventids);

    /* Build searchargs */
    searchargs = new_searchargs(NULL, GETSEARCH_CHARSET_FIRST,
            &jmap_namespace, req->accountid, req->authstate, 0);
    searchargs->root = buildsearch(req, filter, NULL);

    /* Need some stable sort criteria for windowing */
    sortcrit = xzmalloc(2 * sizeof(struct sortcrit));
    sortcrit[0].flags |= SORT_REVERSE;
    sortcrit[0].key = SORT_ARRIVAL;
    sortcrit[1].key = SORT_SEQUENCE;

    /* Run the search query */
    memset(&init, 0, sizeof(init));
    init.userid = req->accountid;
    init.authstate = req->authstate;
    init.want_expunged = 0;
    init.want_mbtype = MBTYPE_CALENDAR;
    init.examine_mode = 1;

    char *inboxname = mboxname_user_mbox(req->accountid, NULL);
    r = index_open(inboxname, &init, &state);
    free(inboxname);
    if (r) goto done;

    query = search_query_new(state, searchargs);
    query->sortcrit = sortcrit;
    query->multiple = 1;
    query->need_ids = 1;
    query->want_expunged = 0;
    query->want_mbtype = MBTYPE_CALENDAR;
    r = search_query_run(query);
    if (r && r != IMAP_NOTFOUND) goto done;
    r = 0;

    /* Aggregate result */
    for (i = 0 ; i < query->merged_msgdata.count; i++) {
        MsgData *md = ptrarray_nth(&query->merged_msgdata, i);
        search_folder_t *folder = md->folder;
        struct caldav_data *cdata;

        if (!folder) continue;

        /* Check permissions */
        if (!jmap_hasrights_byname(req, folder->mboxname, DACL_READ))
            continue;

        /* Fetch the CalDAV db record */
        r = caldav_lookup_imapuid(db, folder->mboxname, md->uid, &cdata, 0);
        if (r) continue;

        /* Filter by timerange, if any */
        if (search_timerange && !hash_lookup(cdata->ical_uid, search_timerange)) {
            continue;
        }

        /* It's a legit search hit... */
        *total = *total + 1;

        /* ...probably outside the search window? */
        if (limit && json_array_size(*eventids) + 1 > limit) {
            continue;
        }
        if (pos >= *total) {
            continue;
        }

        /* Add the search result */
        json_array_append_new(*eventids, json_string(cdata->ical_uid));
    }

done:
    index_close(&state);
    if (search_timerange) {
        free_hash_table(search_timerange, NULL);
        free(search_timerange);
    }
    free_hash_table(&mboxrights, free);
    if (searchargs) freesearchargs(searchargs);
    if (sortcrit) freesortcrit(sortcrit);
    if (query) search_query_free(query);
    if (db) caldav_close(db);
    free(icalbefore);
    free(icalafter);
    return r;
}

static void validatefilter(jmap_req_t *req __attribute__((unused)),
                           struct jmap_parser *parser,
                           json_t *filter,
                           json_t *unsupported __attribute__((unused)),
                           void *rock __attribute__((unused)),
                           json_t **err __attribute__((unused)))
{
    icaltimetype timeval;
    const char *field;
    json_t *arg;

    json_object_foreach(filter, field, arg) {
        if (!strcmp(field, "inCalendars")) {
            if (!(json_is_array(arg) && json_array_size(arg))) {
                jmap_parser_invalid(parser, field);
            }
            else {
                size_t i;
                json_t *uid;
                json_array_foreach(arg, i, uid) {
                    const char *id = json_string_value(uid);
                    if (!id || id[0] == '#') {
                        jmap_parser_push_index(parser, field, i, id);
                        jmap_parser_invalid(parser, NULL);
                        jmap_parser_pop(parser);
                    }
                }
            }
        }
        else if (!strcmp(field, "before") ||
                 !strcmp(field, "after")) {
            if (!json_is_string(arg) ||
                !utcdate_to_icaltime(json_string_value(arg), &timeval)) {
                jmap_parser_invalid(parser, field);
            }
        }
        else if (!strcmp(field, "text") ||
                 !strcmp(field, "title") ||
                 !strcmp(field, "description") ||
                 !strcmp(field, "location") ||
                 !strcmp(field, "owner") ||
                 !strcmp(field, "attendee")) {
            if (!json_is_string(arg)) {
                jmap_parser_invalid(parser, field);
            }
        }
        else {
            jmap_parser_invalid(parser, field);
        }
    }
}

static int validatecomparator(jmap_req_t *req __attribute__((unused)),
                              struct jmap_comparator *comp,
                              void *rock __attribute__((unused)),
                              json_t **err __attribute__((unused)))
{
    /* Reject any collation */
    if (comp->collation) {
        return 0;
    }
    if (!strcmp(comp->property, "start") ||
        !strcmp(comp->property, "uid")) {
        return 1;
    }
    return 0;
}

static int jmap_calendarevent_query(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_query query;
    int r = 0;

    /* Parse request */
    json_t *err = NULL;
    jmap_query_parse(req, &parser, NULL, NULL,
                     validatefilter, NULL,
                     validatecomparator, NULL,
                     &query, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }
    if (query.position < 0) {
        /* we currently don't support negative positions */
        jmap_parser_invalid(&parser, "position");
    }
    if (json_array_size(parser.invalid)) {
        err = json_pack("{s:s}", "type", "invalidArguments");
        json_object_set(err, "arguments", parser.invalid);
        jmap_error(req, err);
        goto done;
    }

    /* Call search */
    r = jmapevent_search(req, &query);
    if (r) {
        err = jmap_server_error(r);
        jmap_error(req, err);
        goto done;
    }

    /* Build response */
    json_t *jstate = jmap_getstate(req, MBTYPE_CALENDAR, /*refresh*/0);
    query.query_state = xstrdup(json_string_value(jstate));
    json_decref(jstate);

    json_t *res = jmap_query_reply(&query);
    jmap_ok(req, res);

done:
    jmap_query_fini(&query);
    jmap_parser_fini(&parser);
    return 0;
}

static void _calendarevent_copy(jmap_req_t *req,
                                json_t *jevent,
                                struct caldav_db *src_db,
                                struct caldav_db *dst_db,
                                json_t **new_event,
                                json_t **set_err)
{
    struct jmap_parser myparser = JMAP_PARSER_INITIALIZER;
    icalcomponent *src_ical = NULL;
    json_t *dst_event = NULL;
    struct mailbox *src_mbox = NULL;
    int r = 0;

    /* Read mandatory properties */
    const char *src_id = json_string_value(json_object_get(jevent, "id"));
    const char *dst_calendar_id = json_string_value(json_object_get(jevent, "calendarId"));
    if (!src_id) {
        jmap_parser_invalid(&myparser, "id");
    }
    if (!dst_calendar_id) {
        jmap_parser_invalid(&myparser, "calendarId");
    }
    if (json_array_size(myparser.invalid)) {
        *set_err = json_pack("{s:s s:O}", "type", "invalidProperties",
                                          "properties", myparser.invalid);
        goto done;
    }

    /* Lookup event */
    struct caldav_data *cdata = NULL;
    r = caldav_lookup_uid(src_db, src_id, &cdata);
    if (r && r != CYRUSDB_NOTFOUND) {
        syslog(LOG_ERR, "caldav_lookup_uid(%s) failed: %s", src_id, error_message(r));
        goto done;
    }
    if (r == CYRUSDB_NOTFOUND || !cdata->dav.alive || !cdata->dav.rowid ||
            !cdata->dav.imap_uid || cdata->comp_type != CAL_COMP_VEVENT) {
        *set_err = json_pack("{s:s}", "type", "notFound");
        goto done;
    }
    if (!jmap_hasrights_byname(req, cdata->dav.mailbox, DACL_READ)) {
        *set_err = json_pack("{s:s}", "type", "notFound");
        goto done;
    }

    /* Read source event */
    r = jmap_openmbox(req, cdata->dav.mailbox, &src_mbox, /*rw*/0);
    if (r) goto done;
    char *schedule_address = NULL;
    src_ical = caldav_record_to_ical(src_mbox, cdata, httpd_userid, &schedule_address);
    if (!src_ical) {
        syslog(LOG_ERR, "calendarevent_copy: can't convert %s to JMAP", src_id);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Patch JMAP event */
    json_t *src_event = jmapical_tojmap(src_ical, NULL);
    if (src_event) {
        dst_event = jmap_patchobject_apply(src_event, jevent);
    }
    json_decref(src_event);
    if (!dst_event) {
        syslog(LOG_ERR, "calendarevent_copy: can't convert to ical: %s", src_id);
        r = IMAP_INTERNAL;
        goto done;
    }

    /* Create event */
    json_t *invalid = json_array();
    *new_event = json_pack("{}");
    r = setcalendarevents_create(req, req->accountid, dst_event,
                                 dst_db, invalid, *new_event);
    if (r || json_array_size(invalid)) {
        if (!r) {
            *set_err = json_pack("{s:s s:o}", "type", "invalidProperties",
                                              "properties", invalid);
        }
        goto done;
    }
    json_decref(invalid);
    json_object_set(*new_event, "id", json_object_get(*new_event, "uid"));

done:
    if (r && *set_err == NULL) {
        if (r == CYRUSDB_NOTFOUND)
            *set_err = json_pack("{s:s}", "type", "notFound");
        else
            *set_err = jmap_server_error(r);
        return;
    }
    jmap_closembox(req, &src_mbox);
    if (src_ical) icalcomponent_free(src_ical);
    json_decref(dst_event);
    jmap_parser_fini(&myparser);
}

static int jmap_calendarevent_copy(struct jmap_req *req)
{
    struct jmap_parser parser = JMAP_PARSER_INITIALIZER;
    struct jmap_copy copy;
    json_t *err = NULL;
    struct caldav_db *src_db = NULL;
    struct caldav_db *dst_db = NULL;
    json_t *destroy_events = json_array();

    /* Parse request */
    jmap_copy_parse(req, &parser, NULL, NULL, &copy, &err);
    if (err) {
        jmap_error(req, err);
        goto done;
    }

    src_db = caldav_open_userid(copy.from_account_id);
    if (!src_db) {
        jmap_error(req, json_pack("{s:s}", "type", "fromAccountNotFound"));
        goto done;
    }
    dst_db = caldav_open_userid(req->accountid);
    if (!dst_db) {
        jmap_error(req, json_pack("{s:s}", "type", "toAccountNotFound"));
        goto done;
    }

    /* Process request */
    const char *creation_id;
    json_t *jevent;
    json_object_foreach(copy.create, creation_id, jevent) {
        /* Copy event */
        json_t *set_err = NULL;
        json_t *new_event = NULL;

        _calendarevent_copy(req, jevent, src_db, dst_db, &new_event, &set_err);
        if (set_err) {
            json_object_set_new(copy.not_created, creation_id, set_err);
            continue;
        }

        // copy the ID for later deletion
        json_array_append(destroy_events, json_object_get(jevent, "id"));

        /* Report event as created */
        json_object_set_new(copy.created, creation_id, new_event);
        const char *event_id = json_string_value(json_object_get(new_event, "id"));
        jmap_add_id(req, creation_id, event_id);
    }

    /* Build response */
    jmap_ok(req, jmap_copy_reply(&copy));

    /* Destroy originals, if requested */
    if (copy.on_success_destroy_original && json_array_size(destroy_events)) {
        json_t *subargs = json_object();
        json_object_set(subargs, "destroy", destroy_events);
        json_object_set_new(subargs, "accountId", json_string(copy.from_account_id));
        jmap_add_subreq(req, "CalendarEvent/set", subargs, NULL);
    }

done:
    json_decref(destroy_events);
    if (src_db) caldav_close(src_db);
    if (dst_db) caldav_close(dst_db);
    jmap_parser_fini(&parser);
    jmap_copy_fini(&copy);
    return 0;
}
