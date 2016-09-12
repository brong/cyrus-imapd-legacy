/* jmapical.c --Routines to convert calendar events between JMAP and iCalendar
 *
 * Copyright (c) 1994-2016 Carnegie Mellon University.  All rights reserved.
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

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <ctype.h>
#include <math.h>
#include <string.h>
#include <syslog.h>
#include <assert.h>
#include <jansson.h>

#include "acl.h"
#include "annotate.h"
#include "append.h"
#include "caldav_db.h"
#include "carddav_db.h"
#include "global.h"
#include "hash.h"
#include "httpd.h"
#include "http_caldav.h"
#include "http_carddav.h"
#include "http_caldav_sched.h"
#include "http_dav.h"
#include "http_proxy.h"
#include "ical_support.h"
#include "json_support.h"
#include "imap_err.h"
#include "mailbox.h"
#include "mboxlist.h"
#include "mboxname.h"
#include "parseaddr.h"
#include "seen.h"
#include "statuscache.h"
#include "stristr.h"
#include "times.h"
#include "util.h"
#include "vcard_support.h"
#include "version.h"
#include "xmalloc.h"
#include "xsha1.h"
#include "xstrlcat.h"
#include "xstrlcpy.h"
#include "zoneinfo_db.h"

/* for sasl_encode64 */
#include <sasl/sasl.h>
#include <sasl/saslutil.h>

/* generated headers are not necessarily in current directory */
#include "imap/http_err.h"

#include "jmapical.h"

/* Custom iCalendar properties */
#define JMAPICAL_XPROP_LOCATION     "X-JMAP-LOCATION"
#define JMAPICAL_XPROP_TRANSLATION  "X-JMAP-TRANSLATION"

/* Custom iCalendar parameters */
#define JMAPICAL_XPARAM_NAME    "X-JMAP-NAME"
#define JMAPICAL_XPARAM_ID      "X-JMAP-ID"
#define JMAPICAL_XPARAM_PROP    "X-JMAP-PROP"

/* Magic data URI prefix for locations */
#define JMAPICAL_LOCATION_DATAURI_PREFIX \
    "data:application/json;x-jmap-type=location;base64,"

static int JNOTNULL(json_t *item)
{
   if (!item) return 0;
   if (json_is_null(item)) return 0;
   return 1;
}

static char *hexkey(const char *val)
{
    unsigned char dest[SHA1_DIGEST_LENGTH];
    char idbuf[2*SHA1_DIGEST_LENGTH+1];
    int r;

    xsha1((const unsigned char *) val, strlen(val), dest);
    r = bin_to_hex(dest, SHA1_DIGEST_LENGTH, idbuf, BH_LOWER);
    assert(r == 2*SHA1_DIGEST_LENGTH);
    idbuf[2*SHA1_DIGEST_LENGTH] = '\0';
    return xstrdup(idbuf);
}

static char *mailaddr_from_uri(const char *uri)
{
    if (!uri || strncasecmp(uri, "mailto:", 7)) {
        return NULL;
    }
    uri += 7;
    return address_canonicalise(uri);
}

static char *mailaddr_to_uri(const char *addr)
{
    struct buf buf = BUF_INITIALIZER;
    buf_setcstr(&buf, "mailto:");
    buf_appendcstr(&buf, addr);
    return buf_release(&buf);
}


/* TODO
 * - use kmurchinson's icalparameter_get_value_as_string where appropriate
 * - valgrind checks
 * - timezone by reference make ical datetimes have NULL zone
 *   fields even if TZID is specified. tzid_from_icalprop takes care
 *   of that but revise code to make sure we properly set zone for
 *   any icaltime
 */

static void remove_icalxparam(icalproperty *prop, const char *name)
{
    icalparameter *param, *next;

    for (param = icalproperty_get_first_parameter(prop, ICAL_X_PARAMETER);
         param;
         param = next) {

        next = icalproperty_get_next_parameter(prop, ICAL_X_PARAMETER);
        if (strcasecmp(icalparameter_get_xname(param), name)) {
            continue;
        }
        icalproperty_remove_parameter_by_ref(prop, param);
    }
}


static const char*
get_icalxparam_value(icalproperty *prop, const char *name)
{
    icalparameter *param;

    for (param = icalproperty_get_first_parameter(prop, ICAL_X_PARAMETER);
         param;
         param = icalproperty_get_next_parameter(prop, ICAL_X_PARAMETER)) {

        if (strcasecmp(icalparameter_get_xname(param), name)) {
            continue;
        }
        return icalparameter_get_xvalue(param);
    }

    return NULL;
}

static void
set_icalxparam(icalproperty *prop, const char *name, const char *val)
{
    icalparameter *param;
   
    remove_icalxparam(prop, name);

    param = icalparameter_new(ICAL_X_PARAMETER);
    icalparameter_set_xname(param, name);
    icalparameter_set_xvalue(param, val);
    icalproperty_add_parameter(prop, param);
}

/* Compare the value of the first occurences of property kind in components
 * a and b. Return 0 if they match or if both do not contain kind. Note that
 * this function does not define an order on property values, so it can't be
 * used for sorting. */
int compare_icalprop(icalcomponent *a, icalcomponent *b,
                     icalproperty_kind kind) {
    icalproperty *pa, *pb;
    icalvalue *va, *vb;

    pa = icalcomponent_get_first_property(a, kind);
    pb = icalcomponent_get_first_property(b, kind);
    if (!pa && !pb) {
        return 0;
    }

    va = icalproperty_get_value(pa);
    vb = icalproperty_get_value(pb);
    enum icalparameter_xliccomparetype cmp = icalvalue_compare(va, vb);
    return cmp != ICAL_XLICCOMPARETYPE_EQUAL;
}

/* Remove and deallocate any x-properties with name in comp. */
static void remove_icalxprop(icalcomponent *comp, const char *name)
{
    icalproperty *prop, *next;
    icalproperty_kind kind = ICAL_X_PROPERTY;

    for (prop = icalcomponent_get_first_property(comp, kind);
         prop;
         prop = next) {

        next = icalcomponent_get_next_property(comp, kind);

        if (strcasecmp(icalproperty_get_x_name(prop), name))
            continue;

        icalcomponent_remove_property(comp, prop);
        icalproperty_free(prop);
    }
}

static char *xjmapid_from_ical(icalproperty *prop)
{
    struct buf buf = BUF_INITIALIZER;

    char *id = (char *) get_icalxparam_value(prop, JMAPICAL_XPARAM_ID);
    if (!id) {
        id = hexkey(icalproperty_as_ical_string(prop));
        buf_setcstr(&buf, id);
        buf_appendcstr(&buf, "-auto");
        free(id);
        id = buf_newcstring(&buf);
    } else {
        id = xstrdup(id);
    }

    buf_free(&buf);
    return id;
}

/* XXX use where applicable */
static void xjmapid_to_ical(icalproperty *prop, const char *id)
{
    struct buf buf = BUF_INITIALIZER;
    icalparameter *param;

    buf_setcstr(&buf, JMAPICAL_XPARAM_ID);
    buf_appendcstr(&buf, "=");
    buf_appendcstr(&buf, id);
    param = icalparameter_new_from_string(buf_cstring(&buf));
    icalproperty_add_parameter(prop, param);

    buf_free(&buf);
}

static int _wantprop(json_t *props, const char *name)
{
    if (!props) {
        return 1;
    }
    return json_object_get(props, name) != NULL;
}

/* FIXME libical doesn't return the builtin UTC timezone for Etc/UTC */
static icaltimezone *tz_from_tzid(const char *tzid)
{
    if (!tzid)
        return NULL;

    if (!strcmp(tzid, "Etc/UTC") || !strcmp(tzid, "UTC"))
        return icaltimezone_get_utc_timezone();

    return icaltimezone_get_builtin_timezone(tzid);
}

/* Determine the Olson TZID, if any, of the ical property prop. */
static const char *tzid_from_icalprop(icalproperty *prop, int guess) {
    const char *tzid = NULL;
    icalparameter *param = NULL;

    if (prop) param = icalproperty_get_first_parameter(prop, ICAL_TZID_PARAMETER);
    if (param) tzid = icalparameter_get_tzid(param);
    /* Check if the tzid already corresponds to an Olson name. */
    if (tzid) {
        icaltimezone *tz = tz_from_tzid(tzid);
        if (!tz && guess) {
            /* Try to guess the timezone. */
            icalvalue *val = icalproperty_get_value(prop);
            icaltimetype dt = icalvalue_get_datetime(val);
            tzid = dt.zone ? icaltimezone_get_location((icaltimezone*) dt.zone) : NULL;
            tzid = tzid && tz_from_tzid(tzid) ? tzid : NULL;
        }
    } else {
        icalvalue *val = icalproperty_get_value(prop);
        icaltimetype dt = icalvalue_get_datetime(val);
        if (icaltime_is_valid_time(dt) && dt.is_utc) {
            tzid = "Etc/UTC";
        }
    }
    return tzid;
}

/* Determine the Olson TZID, if any, of the ical property kind in component comp. */
static const char *tzid_from_ical(icalcomponent *comp,
                                  icalproperty_kind kind) {
    icalproperty *prop = icalcomponent_get_first_property(comp, kind);
    if (!prop) {
        return NULL;
    }
    return tzid_from_icalprop(prop, 1/*guess*/);
}

static struct icaltimetype dtstart_from_ical(icalcomponent *comp)
{
    struct icaltimetype dt;
    const char *tzid;

    dt = icalcomponent_get_dtstart(comp);
    if (dt.zone) return dt;

    if ((tzid = tzid_from_ical(comp, ICAL_DTSTART_PROPERTY))) {
        dt.zone = tz_from_tzid(tzid);
    }

    return dt;
}

static struct icaltimetype dtend_from_ical(icalcomponent *comp)
{
    struct icaltimetype dt;
    icalproperty *prop;
    const char *tzid;

    /* Handles DURATION vs DTEND */
    dt = icalcomponent_get_dtend(comp);
    if (dt.zone) return dt;

    prop = icalcomponent_get_first_property(comp, ICAL_DTEND_PROPERTY);
    if (prop) {
        if ((tzid = tzid_from_icalprop(prop, 1))) {
            dt.zone = tz_from_tzid(tzid);
        }
    } else {
        dt.zone = dtstart_from_ical(comp).zone;
    }

    return dt;
}


/* Convert time t to a RFC3339 formatted localdate string. Return the number
 * of bytes written to buf sized size, excluding the terminating null byte. */
static int timet_to_localdate(time_t t, char* buf, size_t size) {
    int n = time_to_rfc3339(t, buf, size);
    if (n && buf[n-1] == 'Z') {
        buf[n-1] = '\0';
        n--;
    }
    return n;
}

/* Convert icaltime to a RFC3339 formatted localdate string.
 * The returned string is owned by the caller or NULL on error.
 */
static char* localdate_from_icaltime_r(icaltimetype icaltime) {
    char *s;
    time_t t;

    s = xzmalloc(RFC3339_DATETIME_MAX);
    if (!s) {
        return NULL;
    }

    t = icaltime_as_timet(icaltime);
    if (!timet_to_localdate(t, s, RFC3339_DATETIME_MAX)) {
        return NULL;
    }
    return s;
}

/* Convert icaltime to a RFC3339 formatted string.
 *
 * The returned string is owned by the caller or NULL on error.
 */
static char* utcdate_from_icaltime_r(icaltimetype icaltime) {
    char *s;
    time_t t;
    int n;

    s = xzmalloc(RFC3339_DATETIME_MAX);
    if (!s) {
        return NULL;
    }

    t = icaltime_as_timet(icaltime);

    n = time_to_rfc3339(t, s, RFC3339_DATETIME_MAX);
    if (!n) {
        free(s);
        return NULL;
    }
    return s;
}

/* Compare int in ascending order. */
static int compare_int(const void *aa, const void *bb)
{
    const int *a = aa, *b = bb;
    return (*a < *b) ? -1 : (*a > *b);
}

/* Return the identity of i. This is a helper for recur_byX. */
static int identity_int(int i) {
    return i;
}

/*
 * Conversion from iCalendar to JMAP
 */

typedef struct fromicalctx {
    jmapical_err_t *err;   /* conversion error, if any */
    jmapical_opts_t *opts; /* conversion opetions, if any */
    json_t *props;         /* which properties to fetch */
    icalcomponent *main;   /* the main event of an exception */

    const char *tzid_start; /* Timezone id of DTSTART, or NULL for float */
    int is_allday;
} fromicalctx_t;

static json_t *calendarevent_from_ical(fromicalctx_t *, icalcomponent *);

/* Convert at most nmemb entries in the ical recurrence byDay/Month/etc array
 * named byX using conv. Return a new JSON array, sorted in ascending order. */
static json_t* recurrence_byX_fromical(short byX[], size_t nmemb, int (*conv)(int)) {
    json_t *jbd = json_pack("[]");

    size_t i;
    int tmp[nmemb];
    for (i = 0; i < nmemb && byX[i] != ICAL_RECURRENCE_ARRAY_MAX; i++) {
        tmp[i] = conv(byX[i]);
    }

    size_t n = i;
    qsort(tmp, n, sizeof(int), compare_int);
    for (i = 0; i < n; i++) {
        json_array_append_new(jbd, json_pack("i", tmp[i]));
    }

    return jbd;
}

/* Convert the ical recurrence recur to a JMAP structure encoded in JSON using
 * timezone id tzid for localdate conversions. */
static json_t*
recurrence_from_ical(fromicalctx_t *ctx, struct icalrecurrencetype recur, const char *tzid)
{
    char *s = NULL;
    size_t i;
    json_t *jrecur = json_pack("{}");
    struct buf buf = BUF_INITIALIZER;

    static const char *weekday_names[] = {
        "sunday",
        "monday",
        "tuesday",
        "wednesday",
        "thursday",
        "friday",
        "saturday",
        "sunday"
    };

    /* frequency */
    s = xstrdup(icalrecur_freq_to_string(recur.freq));
    s = lcase(s);
    json_object_set_new(jrecur, "frequency", json_string(s));
    free(s);

    if (recur.interval > 1) {
        json_object_set_new(jrecur, "interval", json_pack("i", recur.interval));
    }

    /* rscale */
    if (recur.rscale) {
        s = xstrdup(recur.rscale);
        s = lcase(s);
        json_object_set_new(jrecur, "rscale", json_string(s));
        free(s);
    }

    /* skip */
    switch (recur.skip) {
        case ICAL_SKIP_BACKWARD:
            s = "backward";
            break;
        case ICAL_SKIP_FORWARD:
            s = "forward";
            break;
        case ICAL_SKIP_OMIT:
            s = "omit";
            break;
        default:
            s = NULL;
    }
    if (s) json_object_set_new(jrecur, "skip", json_string(s));

    /* firstDayOfWeek */
    short weekday = recur.week_start - 1;
    if (weekday >= 0) {
        json_object_set_new(jrecur, "firstDayOfWeek", json_string(weekday_names[weekday]));
    }

    /* byDay */
    json_t *jbd = json_pack("[]");
    for (i = 0; i < ICAL_BY_DAY_SIZE; i++) {
        json_t *jday;
        icalrecurrencetype_weekday weekday;
        int pos;

        if (recur.by_day[i] == ICAL_RECURRENCE_ARRAY_MAX) {
            break;
        }

        jday = json_pack("{}");
        weekday = icalrecurrencetype_day_day_of_week(recur.by_day[i]) - 1;
        if (weekday >= 0) {
            json_object_set_new(jday, "day", json_string(weekday_names[weekday]));
        }
        pos = icalrecurrencetype_day_position(recur.by_day[i]);
        if (pos) {
            json_object_set_new(jday, "nthOfPeriod", json_integer(pos));
        }

        if (json_object_size(jday)) {
            json_array_append_new(jbd, jday);
        } else {
            json_decref(jday);
        }
    }
    if (json_array_size(jbd)) {
        json_object_set_new(jrecur, "byDay", jbd);
    } else {
        json_decref(jbd);
    }

    /* byMonth */
    json_t *jbm = json_pack("[]");
    for (i = 0; i < ICAL_BY_MONTH_SIZE; i++) {
        short bymonth;

        if (recur.by_month[i] == ICAL_RECURRENCE_ARRAY_MAX) {
            break;
        }

        bymonth = recur.by_month[i];
        buf_printf(&buf, "%d", icalrecurrencetype_month_month(bymonth));
        if (icalrecurrencetype_month_is_leap(bymonth)) {
            buf_appendcstr(&buf, "L");
        }
        json_array_append_new(jbm, json_string(buf_cstring(&buf)));
        buf_reset(&buf);

    }
    if (json_array_size(jbm)) {
        json_object_set_new(jrecur, "byMonth", jbm);
    } else {
        json_decref(jbm);
    }

    if (recur.by_month_day[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "byDate",
                recurrence_byX_fromical(recur.by_month_day,
                    ICAL_BY_MONTHDAY_SIZE, &identity_int));
    }
    if (recur.by_year_day[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "byYearDay",
                recurrence_byX_fromical(recur.by_year_day,
                    ICAL_BY_YEARDAY_SIZE, &identity_int));
    }
    if (recur.by_month[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "byWeekNo",
                recurrence_byX_fromical(recur.by_month,
                    ICAL_BY_MONTH_SIZE, &identity_int));
    }
    if (recur.by_hour[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "byHour",
                recurrence_byX_fromical(recur.by_hour,
                    ICAL_BY_HOUR_SIZE, &identity_int));
    }
    if (recur.by_minute[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "byMinute",
                recurrence_byX_fromical(recur.by_minute,
                    ICAL_BY_MINUTE_SIZE, &identity_int));
    }
    if (recur.by_second[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "bySecond",
                recurrence_byX_fromical(recur.by_second,
                    ICAL_BY_SECOND_SIZE, &identity_int));
    }
    if (recur.by_set_pos[0] != ICAL_RECURRENCE_ARRAY_MAX) {
        json_object_set_new(jrecur, "bySetPosition",
                recurrence_byX_fromical(recur.by_set_pos,
                    ICAL_BY_SETPOS_SIZE, &identity_int));
    }

    if (recur.count != 0) {
        /* Recur count takes precedence over until. */
        json_object_set_new(jrecur, "count", json_integer(recur.count));
    } else if (!icaltime_is_null_time(recur.until)) {
        icaltimezone *tz = tz_from_tzid(tzid);
        icaltimetype dtloc = icaltime_convert_to_zone(recur.until, tz);
        char *until = localdate_from_icaltime_r(dtloc);
        if (until == NULL) {
            ctx->err->code = JMAPICAL_ERROR_MEMORY;
            return NULL;
        }
        json_object_set_new(jrecur, "until", json_string(until));
        free(until);
    }

    buf_free(&buf);
    return jrecur;
}

static json_t*
override_rdate_from_ical(fromicalctx_t *ctx, icalproperty *prop)
{
    /* returns a JSON object with a single key value pair */
    json_t *override = json_pack("{}");
    json_t *o = json_pack("{}");
    struct icaldatetimeperiodtype rdate = icalproperty_get_rdate(prop);
    icaltimetype id;

    if (!icaltime_is_null_time(rdate.time)) {

        if (!rdate.time.is_date && !ctx->is_allday) {
            /* DATETIME */
            const char *tzid_rdate = NULL;

            id = rdate.time;
            tzid_rdate = tzid_from_icalprop(prop, 1);

            if (ctx->tzid_start && tzid_rdate && strcmp(ctx->tzid_start, tzid_rdate)) {
                /* Edge case: a RDATE in another timezone */
                icaltimezone *tz_rdate = tz_from_tzid(tzid_rdate);
                icaltimezone *tz_start = tz_from_tzid(ctx->tzid_start);
                if (tz_rdate && tz_start) {
                    char *localdate = localdate_from_icaltime_r(rdate.time);
                    json_object_set_new(o, "start", json_string(localdate));
                    json_object_set_new(o, "timeZone", json_string(tzid_rdate));
                    free(localdate);
                    if (!id.zone) id.zone = tz_rdate;
                    id = icaltime_convert_to_zone(id, tz_start);
                } else {
                    id = icaltime_null_time();
                }
            } else if ((ctx->tzid_start == NULL) != (tzid_rdate == NULL)) {
                id = icaltime_null_time();
            }
        } else {
            /* DATE */
            id = rdate.time;
        }
    } else {
        /* PERIOD */
        struct icaldurationtype dur;
        id = rdate.period.start;

        /* Determine duration */
        if (!icaltime_is_null_time(rdate.period.end)) {
            dur = icaltime_subtract(rdate.period.end, id);
        } else {
            dur = rdate.period.duration;
        }

        /* Convert id from UTC to event timezone */
        if (ctx->tzid_start) {
            icaltimezone *tz = icaltimezone_get_utc_timezone();
            if (!id.zone) id.zone = tz;
            tz = tz_from_tzid(ctx->tzid_start);
            if (tz) {
                id = icaltime_convert_to_zone(id, tz);
            }
        }

        json_object_set_new(o, "duration",
                json_string(icaldurationtype_as_ical_string(dur)));
    }

    if (!icaltime_is_null_time(id)) {
        char *t = localdate_from_icaltime_r(id);
        json_object_set_new(override, t, o);
        free(t);
    }

    if (!json_object_size(override)) {
        json_decref(override);
        json_decref(o);
        override = NULL;
    }
    return override;
}

static json_t*
override_exdate_from_ical(fromicalctx_t *ctx, icalproperty *prop)
{
    /* returns a JSON object with a single key value pair. value is
     * always JSON null */
    json_t *override = json_pack("{}");
    icaltimetype id = icalproperty_get_exdate(prop);
    const char *tzid_xdate;

    tzid_xdate = tzid_from_icalprop(prop, 1);
    if (ctx->tzid_start && tzid_xdate && strcmp(ctx->tzid_start, tzid_xdate)) {
        icaltimezone *tz_xdate = tz_from_tzid(tzid_xdate);
        icaltimezone *tz_start = tz_from_tzid(ctx->tzid_start);
        if (tz_xdate && tz_start) {
            if (id.zone) id.zone = tz_xdate;
            id = icaltime_convert_to_zone(id, tz_start);
        }
    }

    if (!icaltime_is_null_time(id)) {
        char *t = localdate_from_icaltime_r(id);
        json_object_set_new(override, t, json_null());
        free(t);
    }

    if (!json_object_size(override)) {
        json_decref(override);
        override = NULL;
    }

    return override;
}

static char* jsonpointer_encode(const char *src)
{
    struct buf buf = BUF_INITIALIZER;
    const char *base, *top;
    buf_ensure(&buf, strlen(src));

    base = src;
    top = base;
    while (*top) {
        for (top = base; *top && *top != '~' && *top != '/'; top++)
            ;
        buf_appendmap(&buf, base, top-base);
        if (*top == '~') {
            buf_appendmap(&buf, "~0", 2);
            top++;
        } else if (*top == '/') {
            buf_appendmap(&buf, "~1", 2);
            top++;
        }
        base = top;
        top = base;
    }
    buf_appendmap(&buf, base, top-base);
    return buf_release(&buf);
}

static json_t* diff_object(struct buf *buf, json_t *a, json_t *b)
{
    const char *id;
    json_t *o, *diff;

    if (b == NULL)
        return NULL;

    if (json_equal(a, b)) {
        return NULL;
    }

    /* FIXME check if encodes json null properly */
    if (!JNOTNULL(a) || json_typeof(b) != JSON_OBJECT) {
        return json_pack("{s:o}", buf_cstring(buf), b);
    }

    diff = json_pack("{}");
    json_object_foreach(b, id, o) {
        char *encid = jsonpointer_encode(id);
        size_t l = buf_len(buf);
        if (!l) {
            buf_setcstr(buf, encid);
        } else {
            buf_appendcstr(buf, "/");
            buf_appendcstr(buf, encid);
        }
        json_object_update(diff, diff_object(buf, json_object_get(a, id), o));
        buf_truncate(buf, l);
        free(encid);
    }
    if (!json_object_size(diff)) {
        json_decref(diff);
        diff = NULL;
    }

    return diff;
}

static json_t*
overrides_from_ical(fromicalctx_t *ctx, icalcomponent *comp, json_t *event)
{
    icalproperty *prop;
    json_t *overrides = json_pack("{}");

    /* RDATE */
    for (prop = icalcomponent_get_first_property(comp, ICAL_RDATE_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_RDATE_PROPERTY)) {

        json_t *override = override_rdate_from_ical(ctx, prop);
        if (override) {
            json_object_update(overrides, override);
        }
    }

    /* EXDATE */
    for (prop = icalcomponent_get_first_property(comp, ICAL_EXDATE_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_EXDATE_PROPERTY)) {

        json_t *override = override_exdate_from_ical(ctx, prop);
        if (override) {
            json_object_update(overrides, override);
        }
    }

    /* VEVENT exceptions */
    json_t *exceptions = json_pack("{}");
    icalcomponent *excomp, *ical;

    ical = icalcomponent_get_parent(comp);
    for (excomp = icalcomponent_get_first_component(ical, ICAL_VEVENT_COMPONENT);
            excomp;
            excomp = icalcomponent_get_next_component(ical, ICAL_VEVENT_COMPONENT)) {

        if (excomp == comp) continue; /* skip toplevel promoted object */

        struct fromicalctx myctx;
        json_t *ex;

        /* Convert exceptional VEVENT */
        memcpy(&myctx, ctx, sizeof(struct fromicalctx));
        myctx.main = comp;
        ex = calendarevent_from_ical(&myctx, excomp);
        if (!ex) {
            continue;
        }

        /* Add exception */
        struct icaltimetype recurid = icalcomponent_get_recurrenceid(excomp);
        char *s = localdate_from_icaltime_r(recurid);

        struct buf buf = BUF_INITIALIZER;
        json_t *diff = diff_object(&buf, event, ex);
        json_object_set_new(exceptions, s, diff ? diff : json_pack("{}"));
        buf_free(&buf);
        free(s);
    }

    json_object_update(overrides, exceptions);

    if (!json_object_size(overrides)) {
        json_decref(overrides);
        overrides = json_null();
    }

    return overrides;
}

static json_t *alertaction_from_ical(icalcomponent *alarm)
{
    json_t *action = NULL;
    icalproperty* prop;
    icalparameter *param;
    icalvalue* val;
    icalproperty_action icalaction;

    const char *s;

    prop = icalcomponent_get_first_property(alarm, ICAL_ACTION_PROPERTY);
    if (!prop) goto done;

    val = icalproperty_get_value(prop);
    if (!val) goto done;

    icalaction = icalvalue_get_action(val);
    if (icalaction != ICAL_ACTION_EMAIL && icalaction != ICAL_ACTION_DISPLAY)
        goto done;

    if (icalaction == ICAL_ACTION_EMAIL) {
        json_t *to = json_pack("[]");

        for (prop = icalcomponent_get_first_property(alarm, ICAL_ATTENDEE_PROPERTY);
                prop;
                prop = icalcomponent_get_next_property(alarm, ICAL_ATTENDEE_PROPERTY)) {

            const char *name = NULL;
            char *email;

            /* email */
            email = mailaddr_from_uri(icalproperty_get_value_as_string(prop));
            if (!email) {
                continue;
            }

            /* name */
            param = icalproperty_get_first_parameter(prop, ICAL_CN_PARAMETER);
            if (param) {
                name = icalparameter_get_cn(param);
            }

            json_array_append_new(to, json_pack("{s:s s:s}",
                        "name", name ? name : "",
                        "email", email));
        }
        if (!json_array_size(to)) {
            json_decref(to);
            goto done;
        }
        action = json_pack("{s:s s:o}", "type", "email", "to", to);

        /* subject */
        if ((s = icalcomponent_get_summary(alarm))) {
            json_object_set_new(action, "subject", json_string(s));
        }
        /* textBody */
        if ((s = icalcomponent_get_description(alarm))) {
            json_object_set_new(action, "textBody", json_string(s));
        }

    } else {
        /* XXX acknowledgedUntil */
        /* XXX snoozedUntil */
        action = json_pack("{s:s}", "type", "display");
    }

done:
    return action;
}

/* Convert the VALARMS in the VEVENT comp to CalendarEvent alerts. */
static json_t*
alerts_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    json_t* alerts = json_pack("{}");
    icalcomponent* alarm;

    for (alarm = icalcomponent_get_first_component(comp, ICAL_VALARM_COMPONENT);
         alarm;
         alarm = icalcomponent_get_next_component(comp, ICAL_VALARM_COMPONENT)) {

        icalproperty* prop;
        icalparameter *param;
        struct icaltriggertype trigger;
        icalparameter_related related = ICAL_RELATED_START;

        json_t *action, *alert;
        const char *relativeTo, *offset;
        char *id;
        struct icaldurationtype duration;

        relativeTo = offset = id = NULL;

        /* Determine TRIGGER */
        prop = icalcomponent_get_first_property(alarm, ICAL_TRIGGER_PROPERTY);
        if (!prop) {
            continue;
        }
        trigger = icalproperty_get_trigger(prop);

        /* Determine RELATED parameter */
        param = icalproperty_get_first_parameter(prop, ICAL_RELATED_PARAMETER);
        if (param) {
            related = icalparameter_get_related(param);
            if (related != ICAL_RELATED_START && related != ICAL_RELATED_END) {
                continue;
            }
        }

        /* Determine duration between alarm and start/end */
        if (!icaldurationtype_is_null_duration(trigger.duration)) {
            duration = trigger.duration;
        } else {
            icaltimetype ttrg, tref;
            icaltimezone *utc = icaltimezone_get_utc_timezone();

            ttrg = icaltime_convert_to_zone(trigger.time, utc);
            if (related == ICAL_RELATED_START) {
                tref = icaltime_convert_to_zone(dtstart_from_ical(comp), utc);
            } else {
                tref = icaltime_convert_to_zone(dtend_from_ical(comp), utc);
            }
            /* XXX "if the event is in floating time (including all-day events),
             * the server SHOULD use the user’s default time zone when
             * determining the start time." */
            duration = icaltime_subtract(ttrg, tref);
        }

        /* action */
        action = alertaction_from_ical(alarm);
        if (!action) continue;

        /* relativeTo */
        if (duration.is_neg) {
            relativeTo = related == ICAL_RELATED_START ?
                "before-start" : "before-end";
        } else {
            relativeTo = related == ICAL_RELATED_START ?
                "after-start" : "after-end";
        }

        /* offset*/
        duration.is_neg = 0;
        offset = icaldurationtype_as_ical_string_r(duration);

        /* alert id */
        id = (char *) icalcomponent_get_uid(alarm);
        if (!id) {
            id = hexkey(icalcomponent_as_ical_string(alarm));
        } else {
            id = xstrdup(id);
        }

        alert = json_pack("{s:s s:s s:o}",
                "relativeTo", relativeTo,
                "offset", offset,
                "action", action);
        json_object_set_new(alerts, id, alert);

        free(id);
    }

    if (!json_object_size(alerts)) {
        json_decref(alerts);
        alerts = json_null();
    }
    return alerts;
}

static json_t *participant_from_ical(icalproperty *prop, hash_table *hatts)
{
    json_t *p = json_pack("{}");
    icalparameter *param;
    int is_owner = icalproperty_isa(prop) == ICAL_ORGANIZER_PROPERTY;

    /* name */
    const char *name = NULL;
    param = icalproperty_get_first_parameter(prop, ICAL_CN_PARAMETER);
    if (param) {
        name = icalparameter_get_cn(param);
    }
    json_object_set_new(p, "name", json_string(name ? name : ""));

    /* email */
    char *email = mailaddr_from_uri(icalproperty_get_value_as_string(prop));
    if (!email) {
        json_decref(p);
        return NULL;
    }
    json_object_set_new(p, "email", json_string(email));
    free(email);

    /* kind */
    const char *kind = NULL;
    param = icalproperty_get_first_parameter(prop, ICAL_CUTYPE_PARAMETER);
    if (param) {
        icalparameter_cutype cutype = icalparameter_get_cutype(param);
        switch (cutype) {
            case ICAL_CUTYPE_INDIVIDUAL:
                kind = "individual";
                break;
            case ICAL_CUTYPE_GROUP:
                kind = "group";
                break;
            case ICAL_CUTYPE_RESOURCE:
                kind = "resource";
                break;
            case ICAL_CUTYPE_ROOM:
                kind = "location";
                break;
            default:
                kind = "unknown";
        }
    }
    if (kind) {
        json_object_set_new(p, "kind", json_string(kind));
    }

    /* roles */
    json_t *roles = json_pack("[]");
    if (is_owner) {
        json_array_append_new(roles, json_string("owner"));
    } else {
        json_array_append_new(roles, json_string("attendee"));
    }
    param = icalproperty_get_first_parameter(prop, ICAL_ROLE_PARAMETER);
    if (param && (icalparameter_get_role(param) == ICAL_ROLE_CHAIR)) {
        json_array_append_new(roles, json_string("chair"));
    }
    if (json_array_size(roles)) {
        json_object_set_new(p, "roles", roles);
    } else {
        json_decref(roles);
    }

    /* XXX locationId */

    /* scheduleStatus */
    const char *status = NULL;
    short depth = 0;
    while (!status && !is_owner) {
        param = icalproperty_get_first_parameter(prop, ICAL_PARTSTAT_PARAMETER);
        if (!param) {
            status = "needs-action";
            break;
        }
        icalparameter_partstat pst = icalparameter_get_partstat(param);
        switch (pst) {
            case ICAL_PARTSTAT_ACCEPTED:
                status = "accepted";
                break;
            case ICAL_PARTSTAT_DECLINED:
                status = "declined";
                break;
            case ICAL_PARTSTAT_TENTATIVE:
                status = "tentative";
                break;
            case ICAL_PARTSTAT_DELEGATED:
                /* Follow the delegate chain */
                param = icalproperty_get_first_parameter(prop, ICAL_DELEGATEDTO_PARAMETER);
                if (param) {
                    const char *to = icalparameter_get_delegatedto(param);
                    if (!to) continue;
                    prop = hash_lookup(to, hatts);
                    if (prop) {
                        /* Determine PARTSTAT from delegate. */
                        if (++depth > 64) {
                            /* This is a pathological case: libical does
                             * not check for inifite DELEGATE chains, so we
                             * make sure not to fall in an endless loop. */
                            status = "needs-action";
                        }
                        continue;
                    }
                }
                /* fallthrough */
            default:
                status = "needs-action";
        }
    }
    if (status) {
        json_object_set_new(p, "scheduleStatus", json_string(status));
    }

    /* schedulePriority */
    const char *prio = NULL;
    param = icalproperty_get_first_parameter(prop, ICAL_ROLE_PARAMETER);
    if (param) {
        icalparameter_role role = icalparameter_get_role(param);
        switch (role) {
            case ICAL_ROLE_CHAIR:
            case ICAL_ROLE_REQPARTICIPANT:
                prio = "required";
                break;
            case ICAL_ROLE_OPTPARTICIPANT:
                prio = "optional";
                break;
            case ICAL_ROLE_NONPARTICIPANT:
                prio = "non-participant";
                break;
            default:
                prio = "required";
        }
    }
    if (prio) {
        json_object_set_new(p, "schedulePriority", json_string(prio));
    }

    /* scheduleRSVP */
    json_t *rsvp = NULL;
    param = icalproperty_get_first_parameter(prop, ICAL_RSVP_PARAMETER);
    if (param) {
        icalparameter_rsvp val = icalparameter_get_rsvp(param);
        if (val == ICAL_RSVP_TRUE) {
            rsvp = json_true();
        } else if (val == ICAL_RSVP_FALSE) {
            rsvp = json_false();
        }
    }
    if (rsvp) {
        json_object_set_new(p, "scheduleRSVP", rsvp);
    }

    /* scheduleUpdated */
    const char *xdtstamp = get_icalxparam_value(prop, "X-DTSTAMP");
    if (xdtstamp) {
        struct icaltimetype dt = icaltime_from_string(xdtstamp);
        if (icaltime_is_valid_time(dt)) {
            char *t = utcdate_from_icaltime_r(dt);
            if (t) {
                json_object_set_new(p, "scheduleUpdated", json_string(t));
                free(t);
            }
        }
    }

    /* XXX memberOf */

    return p;
}

/* Convert the ical ORGANIZER/ATTENDEEs in comp to CalendarEvent participants */
static json_t*
participants_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    struct hash_table hatts;
    icalproperty *prop;
    json_t *org, *participants = json_pack("{}");
    const char *orgaddr;

    /* Collect all attendees in a map to lookup delegates. */
    construct_hash_table(&hatts, 32, 0);
    for (prop = icalcomponent_get_first_property(comp, ICAL_ATTENDEE_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_ATTENDEE_PROPERTY)) {

        hash_insert(icalproperty_get_value_as_string(prop), prop, &hatts);
    }
    if (!hash_numrecords(&hatts)) {
        goto done;
    }

    /* Add ORGANIZER */
    org = NULL;
    orgaddr = NULL;
    prop = icalcomponent_get_first_property(comp, ICAL_ORGANIZER_PROPERTY);
    if (!prop) {
        goto done;
    }
    if ((org = participant_from_ical(prop, &hatts))) {
        /* XXX X-JMAP-ID */
        char *id;
        orgaddr = icalproperty_get_organizer(prop);
        id = mailaddr_from_uri(orgaddr);
        json_object_set_new(participants, id, org);
        free(id);
    }
    if (!orgaddr || !org) {
        goto done;
    }

    /* Add ATTENDEEs */
    for (prop = icalcomponent_get_first_property(comp, ICAL_ATTENDEE_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_ATTENDEE_PROPERTY)) {
        const char *addr = icalproperty_get_attendee(prop);
        json_t *p;

        p = participant_from_ical(prop, &hatts);
        if (p && strcmp(addr, orgaddr)) {
            /* Add ATTENDEE */
            /* XXX X-JMAP-ID */
            char *id = mailaddr_from_uri(icalproperty_get_attendee(prop));
            if (json_object_get(participants, id)) {
                json_object_update(json_object_get(participants, id), p);
            } else {
                json_object_set_new(participants, id, p);
            }
            free(id);
        } else if (p) {
            /* Merge ORGANIZER and its ATTENDEE */
            json_object_update(org, p);
            json_object_set_new(org, "roles", json_pack("[s]", "owner"));
        }
    }

done:
    if (!json_object_size(participants)) {
        json_decref(participants);
        participants = json_null();
    }
    free_hash_table(&hatts, NULL);
    return participants;
}

static json_t*
links_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    icalproperty* prop;
    json_t *ret = json_pack("{}");

    for (prop = icalcomponent_get_first_property(comp, ICAL_ATTACH_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_ATTACH_PROPERTY)) {

        icalattach *attach = icalproperty_get_attach(prop);
        icalparameter *param = NULL;
        json_t *link = NULL;

        /* Ignore ATTACH properties with value BINARY. */
        /* XXX embed BINARY as data URI? */
        if (!attach || !icalattach_get_is_url(attach)) {
            continue;
        }

        /* href */
        const char *url = icalattach_get_url(attach);
        if (!url || !strlen(url)) {
            continue;
        }

        link = json_pack("{s:s}", "href", url);

        /* type */
        param = icalproperty_get_first_parameter(prop, ICAL_FMTTYPE_PARAMETER);
        if (param) {
            const char *type = icalparameter_get_fmttype(param);
            if (type) {
                json_object_set_new(link, "type", json_string(type));
            }
        }

        /* XXX title */
        /* XXX json_object_set_new(link, "name", json_null()); */

        /* size */
        json_int_t size = -1;
        param = icalproperty_get_first_parameter(prop, ICAL_SIZE_PARAMETER);
        if (param) {
            const char *s = icalparameter_get_size(param);
            if (s) {
                char *ptr;
                size = strtol(s, &ptr, 10);
                json_object_set_new(link, "size",
                        ptr && *ptr == '\0' ? json_integer(size) : json_null());
            }
        }

        /* XXX rel */

        /* XXX use X-JMAP-ID? */
        json_object_set_new(ret, url, link);
    }

    if (!json_object_size(ret)) {
        json_decref(ret);
        ret = json_null();
    }

    return ret;
}

/* Convert a VEVENT ical component to CalendarEvent relatedTo */
static json_t*
relatedto_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    icalproperty* prop;
    json_t *ret = json_pack("[]");

    for (prop = icalcomponent_get_first_property(comp, ICAL_RELATEDTO_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_RELATEDTO_PROPERTY)) {

        const char *uid;

        uid = icalproperty_get_value_as_string(prop);
        if (!uid || !strlen(uid)) continue;

        json_array_append_new(ret, json_string(uid));
    }

    if (!json_array_size(ret)) {
        json_decref(ret);
        ret = json_null();
    }

    return ret;
}

static json_t* location_from_ical(icalproperty *prop)
{
    icalparameter *param;
    const char *val, *uri;
    json_t *loc;
    size_t n;

    /* (X-)LOCATION's value maps to a location with value as "name" */
    val = icalproperty_get_value_as_string(prop);
    loc = json_pack("{s:s}", "name", val ? val : "");

    param = icalproperty_get_first_parameter(prop, ICAL_ALTREP_PARAMETER);
    if (!param) return loc;

    /* Decode JMAP location from ALTREP data URI, if applicable */
    uri = icalparameter_get_altrep(param);
    n = strlen(JMAPICAL_LOCATION_DATAURI_PREFIX);
    if (!strncmp(uri, JMAPICAL_LOCATION_DATAURI_PREFIX, n)) {
        charset_index cs = charset_lookupname("utf8");
        char *dump;

        if ((dump = charset_to_utf8(uri+n, strlen(uri)-n, cs, ENCODING_BASE64))) {
            json_t *t = json_loads(dump, 0, NULL);
            if (t) {
                json_decref(loc);
                loc = t;
            }
            free(dump);
        }
    } else {
        json_object_set_new(loc, "uri", json_string(uri));
    }

    return loc;
}

static json_t *coordinates_from_ical(icalproperty *prop)
{
    /* Use verbatim coordinate string, rather than the parsed ical value */
    const char *p, *val = icalproperty_get_value_as_string(prop);
    struct buf buf = BUF_INITIALIZER;

    p = strchr(val, ';');
    if (!p) return NULL;

    buf_setcstr(&buf, "geo:");
    buf_appendmap(&buf, val, p-val);
    buf_appendcstr(&buf, ",");
    val = p + 1;
    buf_appendcstr(&buf, val);

    return json_string(buf_release(&buf));
}

static json_t*
locations_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    icalproperty* prop;
    json_t *loc, *locations = json_pack("{}");
    char *id;

    /* Handle end locations */
    const char *tzidstart = tzid_from_ical(comp, ICAL_DTSTART_PROPERTY);
    const char *tzidend = tzid_from_ical(comp, ICAL_DTEND_PROPERTY);

    if (tzidstart && tzidend && strcmp(tzidstart, tzidend)) {
        prop = icalcomponent_get_first_property(comp, ICAL_DTEND_PROPERTY);
        id = xjmapid_from_ical(prop);
        loc = json_pack("{s:s s:s}", "timeZone", tzidend, "rel", "end");
        json_object_set_new(locations, id, loc);
        free(id);
    }

    /* LOCATION */
    if ((prop = icalcomponent_get_first_property(comp, ICAL_LOCATION_PROPERTY))) {
        if ((loc = location_from_ical(prop))) {
            id = xjmapid_from_ical(prop);
            json_object_set_new(locations, id, loc);
            free(id);
        }
    }

    /* GEO */
    if ((prop = icalcomponent_get_first_property(comp, ICAL_GEO_PROPERTY))) {
        json_t *coord = coordinates_from_ical(prop);
        if (coord) {
            loc = json_pack("{s:o}", "coordinates", coord);
            id = xjmapid_from_ical(prop);
            json_object_set_new(locations, id, loc);
            free(id);
        }
    }

    /* Lookup X-JMAP locations */
    for (prop = icalcomponent_get_first_property(comp, ICAL_X_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_X_PROPERTY)) {

        const char *name = icalproperty_get_property_name(prop);

        /* X-APPLE-STRUCTURED-LOCATION */
        if (!strcmp(name, "X-APPLE-STRUCTURED-LOCATION")) {
            const char *title, *uri;
            icalvalue *val;

            val = icalproperty_get_value(prop);
            if (icalvalue_isa(val) != ICAL_URI_VALUE) continue;

            uri = icalvalue_as_ical_string(val);
            if (strncmp(uri, "geo:", 4)) continue;

            loc = json_pack("{s:s}", "coordinates", uri);
            if ((title = get_icalxparam_value(prop, "X-TITLE"))) {
                json_object_set_new(loc, "name", json_string(title));
            }

            id = xjmapid_from_ical(prop);
            json_object_set_new(locations, id, loc);
            free(id);
            continue;
        }

        if (strcasecmp(name, JMAPICAL_XPROP_LOCATION))
            continue;

        /* X-JMAP-LOCATION */
        id = (char*) get_icalxparam_value(prop, JMAPICAL_XPARAM_ID);
        if (!id) continue;

        loc = location_from_ical(prop);
        if (!loc) continue;

        json_object_set_new(locations, id, loc);
    }

    if (!json_object_size(locations)) {
        json_decref(locations);
        locations = json_null();
    }

    return locations;
}

static json_t*
translations_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    icalproperty* prop;
    json_t *translations = json_pack("{}");

    /* Lookup translations */
    for (prop = icalcomponent_get_first_property(comp, ICAL_X_PROPERTY);
         prop;
         prop = icalcomponent_get_next_property(comp, ICAL_X_PROPERTY)) {

        const char *id, *field, *text;
        json_t *tr;
        icalparameter *param;

        if (strcasecmp(icalproperty_get_x_name(prop), JMAPICAL_XPROP_TRANSLATION))
            continue;

        /* Lookup translation id */
        param = icalproperty_get_first_parameter(prop, ICAL_LANGUAGE_PARAMETER);
        if (!param) continue;
        id = icalparameter_get_language(param);
        if (!id) continue;

        /* Get or set translation */
        tr = json_object_get(translations, id);
        if (!tr) {
            tr = json_pack("{}");
            json_object_set_new(translations, id, tr);
        }

        /* Determine the JMAP property this translation relates to */
        field = get_icalxparam_value(prop, JMAPICAL_XPARAM_PROP);

        /* Determine the translation text */
        text = icalproperty_get_value_as_string(prop);

        if (field && text && !strncmp(field, "locations.", 10)) {
            const char *locid;

            /* A location translation  */
            field += 10;

            /* Determine the location id */
            locid = get_icalxparam_value(prop, JMAPICAL_XPARAM_ID);
            if (locid && strlen(locid)) {
                json_t *locations, *loctr;

                locations = json_object_get(tr, "locations");
                if (!locations)
                    locations = json_pack("{}");

                loctr = json_object_get(locations, locid);
                if (!loctr)
                    loctr = json_pack("{}");

                json_object_set(loctr, field, json_string(text));
                json_object_set(locations, locid, loctr);
                json_object_set(tr, "locations", locations);
            }
        } else if (field && text && !strncmp(field, "links.", 6)) {
            /* FIXME Yes, this is copy-pasta from locations above and needs to be refactored */
            const char *locid;

            /* A location translation  */
            field += 6;

            /* Determine the location id */
            locid = get_icalxparam_value(prop, JMAPICAL_XPARAM_ID);
            if (locid && strlen(locid)) {
                json_t *links, *loctr;

                links = json_object_get(tr, "links");
                if (!links)
                    links = json_pack("{}");

                loctr = json_object_get(links, locid);
                if (!loctr)
                    loctr = json_pack("{}");

                json_object_set(loctr, field, json_string(text));
                json_object_set(links, locid, loctr);
                json_object_set(tr, "links", links);
            }

        } else if (field && text) {
            /* Some other translation */
            json_object_set_new(tr, field, json_string(text));
        }

        if (!json_object_size(tr))
            json_object_del(translations, id);
    }

    if (!json_object_size(translations)) {
        json_decref(translations);
        translations = json_null();
    }

    return translations;
}

static json_t* duration_from_ical(icalcomponent *comp)
{
    struct icaltimetype dtstart, dtend;
    char *val = NULL;

    dtstart = dtstart_from_ical(comp);
    dtend = dtend_from_ical(comp);

    if (!icaltime_is_null_time(dtend)) {
        time_t tstart, tend;
        struct icaldurationtype dur;

        tstart = icaltime_as_timet_with_zone(dtstart, dtstart.zone);
        tend = icaltime_as_timet_with_zone(dtend, dtend.zone);
        dur = icaldurationtype_from_int((int)(tend - tstart));

        if (!icaldurationtype_is_bad_duration(dur) && !dur.is_neg) {
            val = icaldurationtype_as_ical_string_r(dur);
        }
    }

    json_t *ret = json_string(val ? val : "P0D");
    if (val) free(val);
    return ret;
}

static json_t*
language_from_ical(fromicalctx_t *ctx __attribute__((unused)), icalcomponent *comp)
{
    icalproperty *sum, *dsc;
    icalparameter *param = NULL;
    const char *lang = NULL;

    sum = icalcomponent_get_first_property(comp, ICAL_SUMMARY_PROPERTY);
    dsc = icalcomponent_get_first_property(comp, ICAL_DESCRIPTION_PROPERTY);

    if (sum) {
        param = icalproperty_get_first_parameter(sum, ICAL_LANGUAGE_PARAMETER);
    }
    if (!param && dsc) {
        param = icalproperty_get_first_parameter(dsc, ICAL_LANGUAGE_PARAMETER);
    }
    if (param) {
        lang = icalparameter_get_language(param);
    }

    return lang ? json_string(lang) : json_null();
}

/* Convert the libical VEVENT comp to a CalendarEvent 
 *
 * parent: if not NULL, treat comp as a VEVENT exception
 * props:  if not NULL, only convert properties named as keys
 */
static json_t*
calendarevent_from_ical(fromicalctx_t *ctx, icalcomponent *comp)
{
    icalproperty* prop;
    json_t *obj, *props;
    int is_exc = ctx->main != NULL;

    props = ctx->props;
    obj = json_pack("{}");

    /* Always determine the event's start timezone. */
    ctx->tzid_start = tzid_from_ical(comp, ICAL_DTSTART_PROPERTY);

    /* Always determine isAllDay to set start, end and timezone fields. */
    ctx->is_allday = icaltime_is_date(icalcomponent_get_dtstart(comp));
    if (ctx->is_allday && ctx->tzid_start) {
        /* bogus iCalendar data */
        ctx->tzid_start = NULL;
    }

    /* isAllDay */
    if (_wantprop(props, "isAllDay") && !is_exc) {
        json_object_set_new(obj, "isAllDay", json_boolean(ctx->is_allday));
    }

    /* uid */
    const char *uid = icalcomponent_get_uid(comp);
    if (uid && !is_exc) {
        json_object_set_new(obj, "uid", json_string(uid));
    }

    /* relatedTo */
    if (_wantprop(props, "relatedTo") && !is_exc) {
        json_object_set_new(obj, "relatedTo", relatedto_from_ical(ctx, comp));
    }

    /* prodId */
    if (_wantprop(props, "prodId") && !is_exc) {
        icalcomponent *ical = comp;
        const char *prodid = NULL;
        while (ical) {
            prop = icalcomponent_get_first_property(ical, ICAL_PRODID_PROPERTY);
            if (prop) {
                prodid = icalproperty_get_prodid(prop);
                break;
            }
            ical = icalcomponent_get_parent(ical);
        }
        json_object_set_new(obj, "prodId",
                prodid ? json_string(prodid) : json_null());
    }

    /* created */
    if (_wantprop(props, "created")) {
        json_t *val = json_null();
        prop = icalcomponent_get_first_property(comp, ICAL_CREATED_PROPERTY);
        if (prop) {
            char *t = utcdate_from_icaltime_r(icalproperty_get_created(prop));
            if (t) {
                val = json_string(t);
                free(t);
            }
        }
        json_object_set_new(obj, "created", val);
    }

    /* updated */
    if (_wantprop(props, "updated")) {
        json_t *val = json_null();
        prop = icalcomponent_get_first_property(comp, ICAL_DTSTAMP_PROPERTY);
        if (prop) {
            char *t = utcdate_from_icaltime_r(icalproperty_get_dtstamp(prop));
            if (t) {
                val = json_string(t);
                free(t);
            }
        }
        json_object_set_new(obj, "updated", val);
    }

    /* sequence */
    if (_wantprop(props, "sequence")) {
        json_object_set_new(obj, "sequence",
                json_integer(icalcomponent_get_sequence(comp)));
    }

    /* title */
    if (_wantprop(props, "title")) {
        prop = icalcomponent_get_first_property(comp, ICAL_SUMMARY_PROPERTY);
        json_object_set_new(obj, "title",
                json_string(prop ? icalproperty_get_summary(prop) : ""));
    }

    /* description */
    if (_wantprop(props, "description")) {
        prop = icalcomponent_get_first_property(comp, ICAL_DESCRIPTION_PROPERTY);
        json_object_set_new(obj, "description",
                json_string(prop ? icalproperty_get_description(prop) : ""));
    }

    /* XXX htmlDescription */

    /* links */
    if (_wantprop(props, "links")) {
        json_object_set_new(obj, "links", links_from_ical(ctx, comp));
    }

    /* language */
    if (_wantprop(props, "language")) {
        json_object_set_new(obj, "language", language_from_ical(ctx, comp));
    }

    /* translations */
    if (_wantprop(props, "translations")) {
        json_object_set_new(obj, "translations", translations_from_ical(ctx, comp));
    }

    /* locations */
    if (_wantprop(props, "locations")) {
        json_object_set_new(obj, "locations", locations_from_ical(ctx, comp));
    }

    /* start */
    if (_wantprop(props, "start")) {
        struct icaltimetype dt = icalcomponent_get_dtstart(comp);
        char *s = localdate_from_icaltime_r(dt);
        json_object_set_new(obj, "start", json_string(s));
        free(s);
    }

    /* timeZone */
    if (_wantprop(props, "timeZone")) {
        json_object_set_new(obj, "timeZone",
                ctx->tzid_start && !ctx->is_allday ?
                json_string(ctx->tzid_start) : json_null());
    }

    /* duration */
    if (_wantprop(props, "duration")) {
        json_object_set_new(obj, "duration", duration_from_ical(comp));
    }

    /* recurrenceRule */
    if (_wantprop(props, "recurrenceRule") && !is_exc) {
        json_t *recur = NULL;
        prop = icalcomponent_get_first_property(comp, ICAL_RRULE_PROPERTY);
        if (prop) {
            recur = recurrence_from_ical(ctx, icalproperty_get_rrule(prop), ctx->tzid_start);
        }
        json_object_set_new(obj, "recurrenceRule", recur ? recur : json_null());
    }

    /* status */
    if (_wantprop(props, "status")) {
        const char *status;
        switch (icalcomponent_get_status(comp)) {
            case ICAL_STATUS_TENTATIVE:
                status = "tentative";
                break;
            case ICAL_STATUS_CONFIRMED:
                status = "confirmed";
                break;
            case ICAL_STATUS_CANCELLED:
                status = "cancelled";
                break;
            default:
                status = NULL;
        }
        if (status) json_object_set_new(obj, "status", json_string(status));
    }

    /* showAsFree */
    if (_wantprop(props, "showAsFree")) {
        prop = icalcomponent_get_first_property(comp, ICAL_TRANSP_PROPERTY);
        if (prop) {
            json_object_set_new(obj, "showAsFree",
                    json_boolean(prop &&
                        !strcmp(icalproperty_get_value_as_string(prop), "TRANSPARENT")));
        }
    }

    /* replyTo */
    if (_wantprop(props, "replyTo") && !is_exc) {
        char *replyto = NULL;
        prop = icalcomponent_get_first_property(comp, ICAL_ORGANIZER_PROPERTY);
        if (prop) {
            replyto = mailaddr_from_uri(icalproperty_get_organizer(prop));
        }
        json_object_set_new(obj, "replyTo", replyto ? json_string(replyto) : json_null());
        if (replyto) free(replyto);
    }

    /* participants */
    if (_wantprop(props, "participants")) {
        json_object_set_new(obj, "participants", participants_from_ical(ctx, comp));
    }

    /* XXX participantId */

    /* XXX useDefaultAlerts */

    /* alerts */
    if (_wantprop(props, "alerts")) {
        json_object_set_new(obj, "alerts", alerts_from_ical(ctx, comp));
    }

    /* recurrenceOverrides - must be last to calculate override patches */
    if (_wantprop(props, "recurrenceOverrides") && !is_exc) {
        json_object_set_new(obj, "recurrenceOverrides", overrides_from_ical(ctx, comp, obj));
    }


    return obj;
}

json_t*
jmapical_tojmap(icalcomponent *ical, struct json_t *props,
                jmapical_err_t *err,
                jmapical_opts_t *opts)
{
    icalcomponent* comp;
    json_t *obj = NULL;
    fromicalctx_t ctx;

    memset(&ctx, 0, sizeof(struct fromicalctx));
    if (err) {
        ctx.err = err;
    } else {
        ctx.err = xzmalloc(sizeof(jmapical_err_t));
        if (ctx.err == NULL) return NULL;
    }
    ctx.err->code = 0;
    ctx.err->props = NULL;
    ctx.opts = opts;
    ctx.props = props;

    /* Locate the main VEVENT. */
    icalcomponent *firstcomp = icalcomponent_get_first_component(ical, ICAL_VEVENT_COMPONENT);
    for (comp = firstcomp;
         comp;
         comp = icalcomponent_get_next_component(ical, ICAL_VEVENT_COMPONENT)) {
        if (!icalcomponent_get_first_property(comp, ICAL_RECURRENCEID_PROPERTY)) {
            break;
        }
    }
    /* magic promote to toplevel for the first item */
    if (!comp) comp = firstcomp;
    if (!comp) {
        goto done;
    }

    /* Convert main VEVENT to JMAP. */
    obj = calendarevent_from_ical(&ctx, comp);
    if (!obj) goto done;

done:
    if (ctx.err && !err) free(ctx.err);
    return obj;
}

/*
 * Convert to iCalendar from JMAP
 */

#define JMAPICAL_CREATE_MODE     (1<<0) /* A new component is created. */
#define JMAPICAL_UPDATE_MODE     (1<<1) /* An existing component is updated. */
#define JMAPICAL_EXC_MODE        (1<<8) /* The current component is an exception .*/

typedef struct toicalctx {
    jmapical_err_t *err;
    jmapical_opts_t *opts;

    int mode;                  /* Flags indicating the current context mode. */
    const char *uid;           /* Copy of the iCalendar UID of this event. */
    int isallday;              /* This event is a whole-day event. */

    json_t *invalid;           /* A JSON array of any invalid properties. */
    strarray_t propstr;
    struct buf propbuf;

    icalcomponent *comp;       /* The current main event of an exception. */
    icalcomponent *oldcomp;    /* The former main event of an exception */

    icaltimetype dtstart;      /* The start of this or the main event. */
    icaltimetype dtend;        /* The end of this or the main event. */
    icaltimezone *tzstart_old; /* The former startTimeZone. */
    icaltimezone *tzstart;     /* The current startTimeZone. */
    icaltimezone *tzend_old;   /* The former endTimeZone. */
    icaltimezone *tzend;       /* The current endTimeZone. */

    icaltimezone **tzs;      /* Timezones required as VTIMEZONEs. */
    size_t n_tzs;            /* The count of timezones. */
    size_t s_tzs;            /* The size of the timezone array. */
} toicalctx_t;

/* Add tz to the ctxs timezone cache, only if it doesn't point to a previously
 * cached timezone. Compare by pointers, which works for builtin timezones. */
static void toicalctx_add_tz(toicalctx_t *ctx, icaltimezone *tz) {
    size_t i;
    for (i = 0; i < ctx->n_tzs; i++) {
        if (ctx->tzs[i] == tz) {
            return;
        }
    }
    if (ctx->n_tzs == ctx->s_tzs) {
        ctx->s_tzs = ctx->s_tzs ? ctx->s_tzs * 2 : 1;
        ctx->tzs = xrealloc(ctx->tzs, sizeof(icaltimezone*) * ctx->s_tzs);
        if (ctx->tzs == NULL) {
            ctx->err->code = JMAPICAL_ERROR_MEMORY;
            return;
        }
    }
    ctx->tzs[ctx->n_tzs++] = tz;
}

static void toicalctx_free(toicalctx_t *ctx) {
    strarray_fini(&ctx->propstr);
    buf_free(&ctx->propbuf);
    free(ctx->tzs);
}

static void timezones_to_ical_cb(icalcomponent *comp,
                                         struct icaltime_span *span,
                                         void *rock) {
    struct icalperiodtype *period = (struct icalperiodtype *) rock;
    int is_date = icaltime_is_date(icalcomponent_get_dtstart(comp));
    icaltimezone *utc = icaltimezone_get_utc_timezone();
    struct icaltimetype start =
        icaltime_from_timet_with_zone(span->start, is_date, utc);
    struct icaltimetype end =
        icaltime_from_timet_with_zone(span->end, is_date, utc);

    if (icaltime_compare(start, period->start) < 0)
        memcpy(&period->start, &start, sizeof(struct icaltimetype));

    if (icaltime_compare(end, period->end) > 0)
        memcpy(&period->end, &end, sizeof(struct icaltimetype));
}

/* Determine the UTC time span of all components within ical of type kind. */
static struct icalperiodtype get_utc_timespan(icalcomponent *ical,
                                              icalcomponent_kind kind) {
    struct icalperiodtype span;
    icalcomponent *comp = icalcomponent_get_first_component(ical, kind);
    int recurring = 0;

    /* Initialize span to be nothing */
    span.start = icaltime_from_timet_with_zone(caldav_eternity, 0, NULL);
    span.end = icaltime_from_timet_with_zone(caldav_epoch, 0, NULL);
    span.duration = icaldurationtype_null_duration();

    do {
        struct icalperiodtype period;
        icalproperty *rrule;
        icalproperty *purged_rrule = NULL;

        /* Get base dtstart and dtend */
        caldav_get_period(comp, kind, &period);

        /* See if its a recurring event */
        rrule = icalcomponent_get_first_property(comp, ICAL_RRULE_PROPERTY);
        if (rrule ||
                icalcomponent_get_first_property(comp, ICAL_RDATE_PROPERTY) ||
                icalcomponent_get_first_property(comp, ICAL_EXDATE_PROPERTY)) {
            /* Recurring - find widest time range that includes events */
            int expand = recurring = 1;

            if (rrule) {
                struct icalrecurrencetype recur = icalproperty_get_rrule(rrule);

                if (!icaltime_is_null_time(recur.until)) {
                    /* Recurrence ends - calculate dtend of last recurrence */
                    struct icaldurationtype duration;
                    icaltimezone *utc = icaltimezone_get_utc_timezone();

                    duration = icaltime_subtract(period.end, period.start);
                    period.end =
                        icaltime_add(icaltime_convert_to_zone(recur.until, utc),
                                duration);

                    /* Do RDATE expansion only */
                    /* Temporarily remove RRULE to allow for expansion of
                     * remaining recurrences. */
                    icalcomponent_remove_property(comp, rrule);
                    purged_rrule = rrule;
                }
                else if (!recur.count) {
                    /* Recurrence never ends - set end of span to eternity */
                    span.end =
                        icaltime_from_timet_with_zone(caldav_eternity, 0, NULL);

                    /* Skip RRULE & RDATE expansion */
                    expand = 0;
                }
            }

            /* Expand (remaining) recurrences */
            if (expand) {
                icalcomponent_foreach_recurrence(
                        comp,
                        icaltime_from_timet_with_zone(caldav_epoch, 0, NULL),
                        icaltime_from_timet_with_zone(caldav_eternity, 0, NULL),
                        timezones_to_ical_cb, &span);
            }

            /* Add RRULE again, if we had removed it before. */
            if (purged_rrule) {
                icalcomponent_add_property(comp, purged_rrule);
            }
        }

        /* Check our dtstart and dtend against span */
        if (icaltime_compare(period.start, span.start) < 0)
            memcpy(&span.start, &period.start, sizeof(struct icaltimetype));

        if (icaltime_compare(period.end, span.end) > 0)
            memcpy(&span.end, &period.end, sizeof(struct icaltimetype));

    } while ((comp = icalcomponent_get_next_component(ical, kind)));

    return span;
}

/* Convert the calendar event ctxs timezones to VTIMEZONEs in the
 * VCALENDAR component ical. */
static void toicalctx_timezones_to_ical(toicalctx_t *ctx, icalcomponent *ical)
{
    icalcomponent *tzcomp, *next;
    icalproperty *prop;
    struct icalperiodtype span;

    /* Determine recurrence span. */
    span = get_utc_timespan(ical, ICAL_VEVENT_COMPONENT);

    /* Remove all VTIMEZONE components for known TZIDs. This operation is
     * a bit hairy: we could expunge a timezone which is in use by an ical
     * property that is unknown to us. But since we don't know what to
     * look for, we can't make sure to preserve these timezones. */
    for (tzcomp = icalcomponent_get_first_component(ical, ICAL_VTIMEZONE_COMPONENT);
         tzcomp;
         tzcomp = next) {

        next = icalcomponent_get_next_component(ical,
                ICAL_VTIMEZONE_COMPONENT);

        prop = icalcomponent_get_first_property(tzcomp, ICAL_TZID_PROPERTY);
        if (prop) {
            const char *tzid = icalproperty_get_tzid(prop);
            if (tz_from_tzid(tzid)) {
                icalcomponent_remove_component(ical, tzcomp);
                icalcomponent_free(tzcomp);
            }
        }
    }

    /* Add the start and end timezones to the ctx. */
    if (ctx->tzstart) {
        toicalctx_add_tz(ctx, ctx->tzstart);
    }
    if (ctx->tzend) {
        toicalctx_add_tz(ctx, ctx->tzend);
    }

    /* Now add each timezone in the ctx, truncated by this events span. */
    size_t i;
    for (i = 0; i < ctx->n_tzs; i++) {
        icaltimezone *tz = ctx->tzs[i];

        /* Clone tz to overwrite its TZID property. */
        icalcomponent *tzcomp = icalcomponent_new_clone(icaltimezone_get_component(tz));
        icalproperty *tzprop = icalcomponent_get_first_property(tzcomp, ICAL_TZID_PROPERTY);
        icalproperty_set_tzid(tzprop, icaltimezone_get_location(tz));

        /* Truncate the timezone to the events timespan. */
        icaltimetype tzdtstart = icaltime_convert_to_zone(span.start, tz);
        icaltimetype tzdtend = icaltime_convert_to_zone(span.end, tz);
        tzdist_truncate_vtimezone(tzcomp, &tzdtstart, &tzdtend);

        /* Add the truncated timezone. */
        icalcomponent_add_component(ical, tzcomp);
    }
}

static void beginprop_key(toicalctx_t *ctx, const char *name, const char *key)
{
    struct buf *buf = &ctx->propbuf;
    strarray_t *str = &ctx->propstr;

    buf_setcstr(buf, name);
    buf_appendcstr(buf, "[");
    buf_appendcstr(buf, key);
    buf_appendcstr(buf, "]");
    strarray_push(str, buf_cstring(buf));
    buf_reset(buf);
}

static void beginprop_idx(toicalctx_t *ctx, const char *name, size_t idx)
{
    struct buf *buf = &ctx->propbuf;
    strarray_t *str = &ctx->propstr;

    buf_setcstr(buf, name);
    buf_appendcstr(buf, "[");
    buf_printf(buf, "%ld", idx);
    buf_appendcstr(buf, "]");
    strarray_push(str, buf_cstring(buf));
    buf_reset(buf);
}

static void beginprop(toicalctx_t *ctx, const char *name)
{
    strarray_t *str = &ctx->propstr;
    strarray_push(str, name);
}

static void endprop(toicalctx_t *ctx)
{
    strarray_t *str = &ctx->propstr;
    assert(strarray_size(str));
    strarray_pop(str);
}

static void invalidprop(toicalctx_t *ctx, const char *name)
{
    struct buf *buf = &ctx->propbuf;
    strarray_t *str = &ctx->propstr;
    int i;

    assert(name || strarray_size(str));

    if (name) strarray_push(str, name);

    buf_setcstr(buf, strarray_nth(str, 0));
    for (i = 1; i < strarray_size(str); i++) {
        buf_appendcstr(buf, ".");
        buf_appendcstr(buf, strarray_nth(str, i));
    }

    if (name) strarray_pop(str);

    json_array_append_new(ctx->invalid, json_string(buf_cstring(buf)));
}

static int have_invalid_props(toicalctx_t *ctx)
{
    return json_array_size(ctx->invalid) > 0;
}

static size_t invalid_prop_count(toicalctx_t *ctx)
{
    return json_array_size(ctx->invalid);
}


/* Read the property named name into dst, formatted according to the json
 * unpack format fmt. Report missing or erroneous properties. 
 *
 * Return a negative value for a missing or invalid property.
 * Return a positive value if a property was read, zero otherwise. */
static int readprop(toicalctx_t *ctx,
                    json_t *from,
                    const char *name,
                    int is_mandatory,
                    const char *fmt,
                    void *dst)
/* XXX legacy implementation in http_jmap.c */
{
    int r = 0;
    json_t *jval = json_object_get(from, name);
    if (!jval && is_mandatory) {
        r = -1;
    } else if (jval) {
        json_error_t err;
        if (json_unpack_ex(jval, &err, 0, fmt, dst)) {
            r = -2;
        } else {
            r = 1;
        }
    }
    if (r < 0) {
        invalidprop(ctx, name);
    }
    return r;
}

/* Remove and deallocate any properties of kind in comp. */
static void remove_icalprop(icalcomponent *comp, icalproperty_kind kind)
{
    icalproperty *prop, *next;

    for (prop = icalcomponent_get_first_property(comp, kind);
         prop;
         prop = next) {

        next = icalcomponent_get_next_property(comp, kind);
        icalcomponent_remove_property(comp, prop);
        icalproperty_free(prop);
    }
}

/* Convert the JMAP local datetime in buf to tm time. Return 0 on success. */
static int localdate_to_tm(const char *buf, struct tm *tm) {
    /* Initialize tm. We don't know about daylight savings time here. */
    memset(tm, 0, sizeof(struct tm));
    tm->tm_isdst = -1;

    /* Parse LocalDate. */
    const char *p = strptime(buf, "%Y-%m-%dT%H:%M:%S", tm);
    if (!p || *p) {
        return -1;
    }
    return 0;
}

/* Convert the JMAP local datetime formatted buf into ical datetime dt
 * using timezone tz. Return 0 on success. */
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
    if (r) return r;

    if (is_allday && (tm.tm_sec || tm.tm_min || tm.tm_hour)) {
        return 1;
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
        return -1;
    }
    tmp.zone = tz;
    tmp.is_date = is_allday;
    *dt = tmp;
    return 0;
}

/* Add or overwrite the datetime property kind in comp. If tz is not NULL, set
 * the TZID parameter on the property. Also take care to purge conflicting
 * datetime properties such as DTEND and DURATION. */
static icalproperty *dtprop_to_ical(icalcomponent *comp,
                                    icaltimetype dt,
                                    icaltimezone *tz,
                                    int purge,
                                    enum icalproperty_kind kind) {
    icalproperty *prop;

    /* Purge existing property. */
    if (purge) {
        remove_icalprop(comp, kind);
    }

    /* Resolve DTEND/DURATION conflicts. */
    if (kind == ICAL_DTEND_PROPERTY) {
        remove_icalprop(comp, ICAL_DURATION_PROPERTY);
    } else if (kind == ICAL_DURATION_PROPERTY) {
        remove_icalprop(comp, ICAL_DTEND_PROPERTY);
    }

    /* Set the new property. */
    prop = icalproperty_new(kind);
    icalproperty_set_value(prop, icalvalue_new_datetime(dt));
    if (tz && !dt.is_utc) {
        icalparameter *param = icalproperty_get_first_parameter(prop, ICAL_TZID_PARAMETER);
        const char *tzid = icaltimezone_get_location(tz);
        if (param) {
            icalparameter_set_tzid(param, tzid);
        } else {
            icalproperty_add_parameter(prop,icalparameter_new_tzid(tzid));
        }
    }
    icalcomponent_add_property(comp, prop);
    return prop;
}

static int location_is_endtimezone(json_t *loc)
{
    return (json_object_get(loc, "timeZone") &&
            !strcmp(json_string_value(json_object_get(loc, "rel")), "end"));
}

/* Update the start and end properties of VEVENT comp, as defined by
 * the JMAP calendarevent event. */
static void
startend_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *event)
{
    const char *tzid;
    int pe;
    const char *dur_old, *dur, *val, *endzoneid;
    struct icaltimetype dtstart_old, dtstart;
    int create = ctx->mode & JMAPICAL_CREATE_MODE;
    json_t *locations;
    json_t *duration;

    /* Determine current timezone */
    tzid = tzid_from_ical(comp, ICAL_DTSTART_PROPERTY);
    if (tzid) {
        ctx->tzstart_old = tz_from_tzid(tzid);
    } else {
        ctx->tzstart_old = NULL;
    }

    /* Read new timezone */
    if (json_object_get(event, "timeZone") != json_null()) {
        pe = readprop(ctx, event, "timeZone", create&&!ctx->isallday, "s", &val);
        if (pe > 0) {
            /* Lookup the new timezone. */
            ctx->tzstart = tz_from_tzid(val);
            if (!ctx->tzstart) {
                invalidprop(ctx, "timeZone");
            }
        } else if (!pe) {
            ctx->tzstart = ctx->tzstart_old;
        }
    } else {
        ctx->tzstart = NULL;
    }
    if (create) {
        ctx->tzstart_old = ctx->tzstart;
    }
    if (ctx->isallday && ctx->tzstart) {
        invalidprop(ctx, "timeZone");
    }

    /* Determine current end timezone */
    tzid = tzid_from_ical(comp, ICAL_DTEND_PROPERTY);
    if (tzid) {
        ctx->tzend_old = tz_from_tzid(tzid);
    } else {
        ctx->tzend_old = ctx->tzstart_old;
    }

    /* Read new end timezone */
    endzoneid = NULL;
    locations = json_object_get(event, "locations");
    if (locations && locations != json_null()) {
        json_t *loc;
        const char *id;

        /* Pick the first location with timeZone and rel=end */
        json_object_foreach(json_object_get(event, "locations"), id, loc) {
            json_t *timeZone;

            if (!location_is_endtimezone(loc)) {
                continue;
            }
            endzoneid = id;

            /* Prepare prefix for error reporting */
            beginprop_key(ctx, "locations", id);

            timeZone = json_object_get(loc, "timeZone");
            if (timeZone != json_null()) {
                tzid = json_string_value(json_object_get(loc, "timeZone"));
                if (tzid) {
                    ctx->tzend = tz_from_tzid(tzid);
                } else {
                    invalidprop(ctx, "timeZone");
                }
            } else {
                /* The end timeZone is set to floating time */
                ctx->tzend = NULL;
            }

            /* Make sure that both timezones are either floating time or not */
            if ((ctx->tzstart == NULL) != (ctx->tzend == NULL)) {
                invalidprop(ctx, "timeZone");
            }
            /* allDay requires floating time */
            if (ctx->isallday && ctx->tzend) {
                invalidprop(ctx, "timeZone");
            }

            endprop(ctx);
            break;
        }
    } else if (locations == json_null()) {
        ctx->tzend = NULL;
    } else {
        ctx->tzend = ctx->tzend_old;
    }
    if (create) {
        ctx->tzend_old = endzoneid ? ctx->tzend : ctx->tzstart;
    }
    if (!endzoneid) {
        ctx->tzend = ctx->tzend_old;
    }

    /* Determine current duration */
    if (!create) {
        duration = duration_from_ical(comp);
        dur_old = json_string_value(duration);
    } else {
        duration = NULL;
        dur_old = "P0D";
    }

    /* Read new duration */
    pe = readprop(ctx, event, "duration", 0, "s", &dur);
    if (pe > 0) {
        struct icaldurationtype d = icaldurationtype_from_string(dur);
        if (!icaldurationtype_is_bad_duration(d)) {
            /* Make sure that pointer equality works */
            if (!strcmp(dur_old, dur)) {
                dur = dur_old;
            }
        } else {
            invalidprop(ctx, "duration");
        }
    } else {
        dur = dur_old;
    }
    if (ctx->isallday && strchr(dur, 'T')) {
        invalidprop(ctx, "duration");
    }

    /* Determine current start */
    dtstart_old = dtstart_from_ical(comp);

    /* Read new start */
    pe = readprop(ctx, event, "start", create, "s", &val);
    if (pe > 0) {
        if (localdate_to_icaltime(val, &dtstart, ctx->tzstart, ctx->isallday)) {
            invalidprop(ctx, "start");
        }
    } else {
        dtstart = dtstart_old;
    }
    if (ctx->isallday && !icaltime_is_date(dtstart)) {
        invalidprop(ctx, "start");
    }

    /* Bail out for property errors */
    if (have_invalid_props(ctx))
        return;

    /* Either all timezones float or none */
    assert((ctx->tzstart != NULL) == (ctx->tzend != NULL));

    /* Purge and rebuild start and end */
    remove_icalprop(comp, ICAL_DTSTART_PROPERTY);
    remove_icalprop(comp, ICAL_DTEND_PROPERTY);
    remove_icalprop(comp, ICAL_DURATION_PROPERTY);

    dtprop_to_ical(comp, dtstart, ctx->tzstart, 1, ICAL_DTSTART_PROPERTY);
    if (ctx->tzstart != ctx->tzend) {
        /* Add DTEND */
        icaltimetype dtend;
        icalproperty *prop;

        dtend = icaltime_add(dtstart, icaldurationtype_from_string(dur));
        dtend = icaltime_convert_to_zone(dtend, ctx->tzend);
        prop = dtprop_to_ical(comp, dtend, ctx->tzend, 1, ICAL_DTEND_PROPERTY);
        xjmapid_to_ical(prop, endzoneid);
    } else {
        /* Add DURATION */
        icalcomponent_set_duration(comp, icaldurationtype_from_string(dur));
    }

    json_decref(duration);
}

/* Create or update the ORGANIZER/ATTENDEEs in the VEVENT component comp as
 * defined by the JMAP organizer and attendees. Purge any participants that
 * are not updated. */
static void
participants_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *participants)
{
    const char *id;
    json_t *p;

    /* XXX this is a naive implementation that *rewrites* the ORGANIZER
     * and ATTENDEEs for each update.
     *
     * A sophisticated implementation needs to
     * - preserve delegates (but JMAP lacks delegates)
     * - preserve PARTSTAT for omitted scheduleStatus properties
     * - allow only owners to add/remove attendees
     * - allow participants to only change their own scheduleStatus
     */

    /* Purge existing ORGANIZER and ATTENDEEs */
    remove_icalprop(comp, ICAL_ORGANIZER_PROPERTY);
    remove_icalprop(comp, ICAL_ATTENDEE_PROPERTY);

    if (!JNOTNULL(participants)) {
        return;
    }

    json_object_foreach(participants, id, p) {
        const char *s, *email;
        char *freeme;
        json_t *roles, *role;
        int is_owner, is_attendee, is_chair, pe;
        size_t i;
        icalproperty *prop;
        icalparameter *param;

        if (!strlen(id))
            continue;

        beginprop_key(ctx, "participants", id);

        /* email */
        pe = readprop(ctx, p, "email", 1, "s", &email);
        if (pe <= 0) {
            endprop(ctx);
            continue;
        }

        /* roles */
        roles = NULL;
        is_owner = is_attendee = is_chair = 0;
        pe = readprop(ctx, p, "roles", 1, "o", &roles);
        if (pe >= 0 && !json_array_size(roles)) {
            invalidprop(ctx, "roles");
            endprop(ctx);
            continue;
        }
        json_array_foreach(roles, i, role) {
            beginprop_idx(ctx, "roles", i);
            if ((s = json_string_value(role))) {
                if (!strcasecmp(s, "owner")) {
                    is_owner = 1;
                } else if (!strcasecmp(s, "attendee")) {
                    is_attendee = 1;
                } else if (!strcasecmp(s, "chair")) {
                    is_chair = 1;
                }
            }
            endprop(ctx);
        }
        if (!is_owner && !is_attendee) {
            endprop(ctx);
            continue;
        }

        /* create participant */
        freeme = mailaddr_to_uri(email);
        if (is_owner) {
            prop = icalproperty_new_organizer(freeme);
        } else {
            prop = icalproperty_new_attendee(freeme);
        }
        if (is_chair) {
            param = icalparameter_new_role(ICAL_ROLE_CHAIR);
            icalproperty_add_parameter(prop, param);
        }
        free(freeme);
        /* XXX set participant id as X-JMAP-ID? */

        /* name */
        pe = readprop(ctx, p, "name", 0, "s", &s);
        if (pe > 0) {
            param = icalparameter_new_cn(s);
            icalproperty_add_parameter(prop, param);
        }

        /* kind */
        pe = readprop(ctx, p, "kind", 0, "s", &s);
        if (pe > 0) {
            char *tmp = xstrdup(s);
            tmp = ucase(tmp);
            icalparameter_cutype cu = icalparameter_string_to_enum(tmp);
            switch (cu) {
                case ICAL_CUTYPE_INDIVIDUAL:
                case ICAL_CUTYPE_GROUP:
                case ICAL_CUTYPE_RESOURCE:
                case ICAL_CUTYPE_ROOM:
                    param = icalparameter_new_cutype(cu);
                    icalproperty_add_parameter(prop, param);
                    break;
                default:
                    /* ignore */ ;
            }
            free(tmp);
        }

        /* XXX locationId */

        /* scheduleStatus */
        icalparameter_partstat ps = ICAL_PARTSTAT_NEEDSACTION;
        pe = readprop(ctx, p, "scheduleStatus", 0, "s", &s);
        if (pe > 0) {
            char *tmp = xstrdup(s);
            tmp = ucase(tmp);
            ps = icalparameter_string_to_enum(tmp);
            switch (ps) {
                case ICAL_PARTSTAT_NEEDSACTION:
                case ICAL_PARTSTAT_ACCEPTED:
                case ICAL_PARTSTAT_DECLINED:
                case ICAL_PARTSTAT_TENTATIVE:
                    /* do nothing */
                    break;
                default:
                    ps = ICAL_PARTSTAT_NONE;
                    /* ignore */ ;
            }
            free(tmp);
        }
        if (ps != ICAL_PARTSTAT_NONE) {
            param = icalparameter_new_partstat(ps);
            icalproperty_add_parameter(prop, param);
        }

        /* schedulePriority */
        pe = readprop(ctx, p, "schedulePriority", 0, "s", &s);
        if (pe > 0) {
            icalparameter_role role = ICAL_ROLE_NONE;
            if (!strcasecmp(s, "required") && !is_chair) {
                role = ICAL_ROLE_REQPARTICIPANT;
            } else if (!strcasecmp(s, "optional")) {
                role = ICAL_ROLE_OPTPARTICIPANT;
            } else if (!strcasecmp(s, "non-participant")) {
                role = ICAL_ROLE_NONPARTICIPANT;
            }
            if (role != ICAL_ROLE_NONE) {
                param = icalparameter_new_role(role);
                icalproperty_add_parameter(prop, param);
            }
        }

        /* scheduleRSVP */
        int b;
        pe = readprop(ctx, p, "scheduleRSVP", 0, "b", &b);
        if (pe > 0) {
            param = icalparameter_new_rsvp(b ? ICAL_RSVP_TRUE : ICAL_RSVP_FALSE);
            icalproperty_add_parameter(prop, param);
        }

        /* scheduleUpdated */
        icaltimezone *utc = icaltimezone_get_utc_timezone();
        icaltimetype now = icaltime_current_time_with_zone(utc);
        set_icalxparam(prop, "X-DTSTART", icaltime_as_ical_string(now));

        /* XXX memberOf */

        if (is_owner) {
            /* last owner wins */
            remove_icalprop(comp, ICAL_ORGANIZER_PROPERTY);
        }
        icalcomponent_add_property(comp, prop);
        endprop(ctx);
    }
}

static void
alertaction_to_ical(toicalctx_t *ctx, icalcomponent *alarm, json_t *action, int *is_unknown)
{
    const char *s;
    int pe;
    icalcomponent *comp = icalcomponent_get_parent(alarm);
    icalproperty *prop;
    icalparameter *param;

    beginprop(ctx, "action");

    /* type */
    icalproperty_action type = ICAL_ACTION_NONE;
    pe = readprop(ctx, action, "type", 1, "s", &s);
    if (pe > 0) {
        if (!strcmp(s, "email")) {
            type = ICAL_ACTION_EMAIL;
        } else if (!strcmp(s, "display")) {
            type = ICAL_ACTION_DISPLAY;
        }
    }
    *is_unknown = type == ICAL_ACTION_NONE;
    if (have_invalid_props(ctx) || *is_unknown) {
        endprop(ctx);
        return;
    }

    /* action */
    prop = icalproperty_new_action(type);
    icalcomponent_add_property(alarm, prop);

    /* alert contents */
    if (type == ICAL_ACTION_EMAIL) {
        json_t *to, *t;
        size_t i;

        pe = readprop(ctx, action, "to", 1, "o", &to);
        if (pe > 0 && json_array_size(to)) {
            json_array_foreach(to, i, t) {

                beginprop_idx(ctx, "to", i);

                /* email */
                pe = readprop(ctx, t, "email", 1, "s", &s);
                if (pe > 0) {
                    char *addr = mailaddr_to_uri(s);
                    prop = icalproperty_new_attendee(addr);
                    free(addr);
                }
                pe = readprop(ctx, t, "name", 0, "s", &s);
                if (pe > 0) {
                    param = icalparameter_new_cn(s);
                    icalproperty_add_parameter(prop, param);
                }
                if (!have_invalid_props(ctx)) {
                    icalcomponent_add_property(alarm, prop);
                }
                endprop(ctx);
            }
        } else if (!pe) {
            invalidprop(ctx, "to");
        }

        /* summary */
        s = icalcomponent_get_summary(comp);
        readprop(ctx, action, "subject", 0, "s", &s);
        prop = icalproperty_new_summary(s ? s : "");
        icalcomponent_add_property(alarm, prop);

        /* textBody */
        s = icalcomponent_get_description(comp);
        readprop(ctx, action, "textBody", 0, "s", &s);
        prop = icalproperty_new_description(s ? s : "");
        icalcomponent_add_property(alarm, prop);
    } else {
        s = icalcomponent_get_summary(comp);
        prop = icalproperty_new_description(s ? s : "");
        icalcomponent_add_property(alarm, prop);
    }

    endprop(ctx);
}

/* Create or update the VALARMs in the VEVENT component comp as defined by the
 * JMAP alerts. */
static void
alerts_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *alerts)
{
    const char *id;
    json_t *alert;
    icalcomponent *alarm, *next;
    int pe;

    /* Purge all VALARMs. */
    /* XXX
     * "The client or server SHOULD NOT trigger any type of alert for action
     *  types they do not understand, but MUST preserve them." */
    for (alarm = icalcomponent_get_first_component(comp, ICAL_VALARM_COMPONENT);
         alarm;
         alarm = next) {
        next = icalcomponent_get_next_component(comp, ICAL_VALARM_COMPONENT);
        icalcomponent_remove_component(comp, alarm);
        icalcomponent_free(alarm);
    }

    if (!JNOTNULL(alerts)) {
        return;
    }

    json_object_foreach(alerts, id, alert) {
        const char *s;
        struct icaltriggertype trigger;
        icalparameter_related rel;
        icalproperty *prop;
        icalparameter *param;
        json_t *action;

        alarm = icalcomponent_new_valarm();
        icalcomponent_set_uid(alarm, id);

        beginprop_key(ctx, "alerts", id);

        /* offset */
        trigger.time = icaltime_null_time();
        pe = readprop(ctx, alert, "offset", 1, "s", &s);
        if (pe > 0) {
            trigger.duration = icaldurationtype_from_string(s);
            if (icaldurationtype_is_bad_duration(trigger.duration)) {
                invalidprop(ctx, "offset");
            }
        }

        /* relativeTo */
        rel = ICAL_RELATED_NONE;
        pe = readprop(ctx, alert, "relativeTo", 1, "s", &s);
        if (pe > 0) {
            if (!strcmp(s, "before-start")) {
                rel = ICAL_RELATED_START;
                trigger.duration.is_neg = 1;
            } else if (!strcmp(s, "after-start")) {
                rel = ICAL_RELATED_START;
            } else if (!strcmp(s, "before-end")) {
                rel = ICAL_RELATED_END;
                trigger.duration.is_neg = 1;
            } else if (!strcmp(s, "after-end")) {
                rel = ICAL_RELATED_END;
            } else {
                invalidprop(ctx, "relativeTo");
            }
        }

        /* action */
        int is_unknown;
        readprop(ctx, alert, "action", 1, "o", &action);
        alertaction_to_ical(ctx, alarm, action, &is_unknown);
        if (is_unknown || have_invalid_props(ctx)) {
            icalcomponent_free(alarm);
            endprop(ctx);
            continue;
        }

        /* Add TRIGGER */
        prop = icalproperty_new_trigger(trigger);
        param = icalparameter_new_related(rel);
        icalproperty_add_parameter(prop, param);
        icalcomponent_add_property(alarm, prop);

        icalcomponent_add_component(comp, alarm);
        endprop(ctx);
    }
}

/* Rewrite the UTC-formatted UNTIL dates in the RRULE of VEVENT comp. */
static void
update_rrule_tz(toicalctx_t *ctx, icalcomponent *comp)
{
    icalproperty *prop = icalcomponent_get_first_property(comp, ICAL_RRULE_PROPERTY);
    if (!prop) {
        return;
    }
    struct icalrecurrencetype rrule = icalproperty_get_rrule(prop);
    if (icaltime_is_null_time(rrule.until)) {
        return;
    }
    icaltimezone *utc = icaltimezone_get_utc_timezone();
    icaltimetype dt = icaltime_convert_to_zone(rrule.until, ctx->tzstart_old);
    dt.zone = ctx->tzstart;
    rrule.until = icaltime_convert_to_zone(dt, utc);
    icalproperty_set_rrule(prop, rrule);
}

static void month_to_ical(struct buf *buf, int val) {
    buf_printf(buf, "%d", val+1);
}

static void int_to_ical(struct buf *buf, int val) {
    buf_printf(buf, "%d", val);
}

/* Convert and print the JMAP byX recurrence value to ical into buf, otherwise
 * report the erroneous fieldName as invalid. If lower or upper is not NULL,
 * make sure that every byX value is within these bounds. */
static void recurrence_byX_to_ical(toicalctx_t *ctx,
                                   json_t *byX,
                                   struct buf *buf,
                                   const char *tag,
                                   int *lower,
                                   int *upper,
                                   int allowZero,
                                   const char *fieldName,
                                   void(*conv)(struct buf*, int)) {

    /* Make sure there is at least one entry. */
    if (!json_array_size(byX)) {
        invalidprop(ctx, fieldName);
        return;
    }

    /* Convert the array. */
    buf_printf(buf, ";%s=", tag);
    size_t i;
    for (i = 0; i < json_array_size(byX); i++) {
        int val;
        int err = json_unpack(json_array_get(byX, i), "i", &val);
        if (!err && !allowZero && !val) {
            err = 1;
        }
        if (!err && ((lower && val < *lower) || (upper && val > *upper))) {
            err = 2;
        }
        if (err) {
            beginprop_idx(ctx, fieldName, i);
            invalidprop(ctx, NULL);
            endprop(ctx);
            continue;
        }
        /* Prepend leading comma, if not first parameter value. */
        if (i) {
            buf_printf(buf, "%c", ',');
        }
        /* Convert the byX value to ical. */
        conv(buf, val);
    }
}

static struct wd_map
{
    const char *icalstr;
    const char *str;
} weekday_map[] = {
    { "SU", "sunday"},
    { "MO", "monday"},
    { "TU", "tuesday"},
    { "WE", "wednesday"},
    { "TH", "thursday"},
    { "FR", "friday"},
    { "SA", "saturday"},
    { NULL, NULL}
};

static const char *weekday_to_ical(const char *name)
{
    size_t i;
    const char *wkst = NULL;
    for (i = 0; weekday_map[i].str; i++) {
        if (!strcmp(name, weekday_map[i].str)) {
            wkst = weekday_map[i].icalstr;
            break;
        }
    }
    return wkst;
}

/* Create or overwrite the RRULE in the VEVENT component comp as defined by the
 * JMAP recurrence. */
static void
recurrence_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *recur)
{
    struct buf buf = BUF_INITIALIZER;
    int pe, lower, upper;
    icalproperty *prop, *next;

    /* Purge existing RRULE. */
    for (prop = icalcomponent_get_first_property(comp, ICAL_RRULE_PROPERTY);
         prop;
         prop = next) {
        next = icalcomponent_get_next_property(comp, ICAL_RRULE_PROPERTY);
        icalcomponent_remove_property(comp, prop);
        icalproperty_free(prop);
    }

    if (!JNOTNULL(recur)) {
        return;
    }

    beginprop(ctx, "recurrenceRule");

    /* frequency */
    char *freq;
    pe = readprop(ctx, recur, "frequency", 1, "s", &freq);
    if (pe > 0) {
        char *s = xstrdup(freq);
        s = lcase(s);
        buf_printf(&buf, "FREQ=%s", s);
        free(s);
    }

    /* interval */
    int interval = 1;
    pe = readprop(ctx, recur, "interval", 0, "i", &interval);
    if (pe > 0) {
        if (interval > 1) {
            buf_printf(&buf, ";INTERVAL=%d", interval);
        } else if (interval < 1) {
            invalidprop(ctx, "interval");
        }
    }

    /* skip */
    char *skip = NULL;
    pe = readprop(ctx, recur, "skip", 0, "s", &skip);
    if (pe > 0 && strlen(skip)) {
        skip = xstrdup(skip);
        skip = ucase(skip);
        buf_printf(&buf, ";SKIP=%s", skip);
        free(skip);
    } else if (pe > 0) {
        invalidprop(ctx, "skip");
    }

    /* rscale */
    char *rscale = NULL;
    pe = readprop(ctx, recur, "rscale", skip != NULL, "s", &rscale);
    if (pe > 0 && strlen(rscale)) {
        rscale = xstrdup(rscale);
        rscale = ucase(rscale);
        buf_printf(&buf, ";RSCALE=%s", rscale);
        free(rscale);
    } else if (pe > 0) {
        invalidprop(ctx, "rscale");
    }

    /* firstDayOfWeek */
    char *firstday = NULL;
    pe = readprop(ctx, recur, "firstDayOfWeek", 0, "s", &firstday);
    if (pe > 0) {
        const char *wkst;
        if ((wkst = weekday_to_ical(firstday))) {
            buf_printf(&buf, ";WKST=%s", wkst);
        } else {
            invalidprop(ctx, "firstDayOfWeek");
        }
    }

    /* byDay */
    json_t *byday = json_object_get(recur, "byDay");
    if (json_array_size(byday) > 0) {
        size_t i;
        json_t *bd;

        buf_appendcstr(&buf, ";BYDAY=");

        json_array_foreach(byday, i, bd) {
            const char *icalday, *day;
            json_int_t nth;

            beginprop_idx(ctx, "byDay", i);

            /* day */
            icalday = day = NULL;
            pe = readprop(ctx, bd, "day", 1, "s", &day);
            if (pe > 0) {
                icalday = weekday_to_ical(day);
                if (!icalday) {
                    invalidprop(ctx, "day");
                }
            }

            /* nthOfPeriod */
            nth = 0;
            pe = readprop(ctx, bd, "nthOfPeriod", 0, "i", &nth);
            if (pe > 0 && !nth) {
                invalidprop(ctx, "nthOfPeriod");
                endprop(ctx);
                continue;
            }

            /* Bail out for property errors */
            if (!icalday) {
                endprop(ctx);
                continue;
            }

            /* Append day */
            if (i > 0) {
                buf_appendcstr(&buf, ",");
            }
            if (nth) {
                buf_printf(&buf, "%+lld", nth);
            }
            buf_appendcstr(&buf, icalday);
            endprop(ctx);
        }
    } else if (byday) {
        invalidprop(ctx, "byDay");
    }

    /* byDate */
    json_t *bydate = NULL;
    lower = -31;
    upper = 31;
    pe = readprop(ctx, recur, "byDate", 0, "o", &bydate);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, bydate, &buf, "BYDATE",
                &lower, &upper, 0 /* allowZero */,
                "byDate", int_to_ical);
    }

    /* byMonth */
    json_t *bymonth = NULL;
    lower = 0;
    upper = 11;
    pe = readprop(ctx, recur, "byMonth", 0, "o", &bymonth);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, bymonth, &buf, "BYMONTH",
                &lower, &upper, 0 /* allowZero */,
                "byMonth", month_to_ical);
    }

    /* byYearDay */
    json_t *byyearday = NULL;
    lower = -366;
    upper = 366;
    pe = readprop(ctx, recur, "byYearDay", 0, "o", &byyearday);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, byyearday, &buf, "BYYEARDAY",
                &lower, &upper, 0 /* allowZero */,
                "byYearDay", int_to_ical);
    }


    /* byWeekNo */
    json_t *byweekno = NULL;
    lower = -53;
    upper = 53;
    pe = readprop(ctx, recur, "byWeekNo", 0, "o", &byweekno);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, byweekno, &buf, "BYWEEKNO",
                &lower, &upper, 0 /* allowZero */,
                "byWeekNo", int_to_ical);
    }

    /* byHour */
    json_t *byhour = NULL;
    lower = 0;
    upper = 23;
    pe = readprop(ctx, recur, "byHour", 0, "o", &byhour);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, byhour, &buf, "BYHOUR",
                &lower, &upper, 1 /* allowZero */,
                "byHour", int_to_ical);
    }

    /* byMinute */
    json_t *byminute = NULL;
    lower = 0;
    upper = 59;
    pe = readprop(ctx, recur, "byMinute", 0, "o", &byminute);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, byminute, &buf, "BYMINUTE",
                &lower, &upper, 1 /* allowZero */,
                "byMinute", int_to_ical);
    }

    /* bySecond */
    json_t *bysecond = NULL;
    lower = 0;
    upper = 59;
    pe = readprop(ctx, recur, "bySecond", 0, "o", &bysecond);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, bysecond, &buf, "BYSECOND",
                &lower, &upper, 1 /* allowZero */,
                "bySecond", int_to_ical);
    }

    /* bySetPosition */
    json_t *bysetpos = NULL;
    lower = 0;
    upper = 59;
    pe = readprop(ctx, recur, "bySetPosition", 0, "o", &bysetpos);
    if (pe > 0) {
        recurrence_byX_to_ical(ctx, bysetpos, &buf, "BYSETPOS",
                &lower, &upper, 1 /* allowZero */,
                "bySetPos", int_to_ical);
    }

    if (json_object_get(recur, "count") && json_object_get(recur, "until")) {
        invalidprop(ctx, "count");
        invalidprop(ctx, "until");
    }

    /* count */
    int count;
    pe = readprop(ctx, recur, "count", 0, "i", &count);
    if (pe > 0) {
        if (count > 0 && !json_object_get(recur, "until")) {
            buf_printf(&buf, ";COUNT=%d", count);
        } else {
            invalidprop(ctx, "count");
        }
    }

    /* until */
    const char *until;
    pe = readprop(ctx, recur, "until", 0, "s", &until);
    if (pe > 0) {
        icaltimetype dtloc;

        if (!localdate_to_icaltime(until, &dtloc, ctx->tzstart, ctx->isallday)) {
            icaltimezone *utc = icaltimezone_get_utc_timezone();
            icaltimetype dt = icaltime_convert_to_zone(dtloc, utc);
            buf_printf(&buf, ";UNTIL=%s", icaltime_as_ical_string(dt));
        } else {
            invalidprop(ctx, "until");
        }
    }

    if (!have_invalid_props(ctx)) {
        /* Add RRULE to component */
        struct icalrecurrencetype rt = icalrecurrencetype_from_string(buf_cstring(&buf));
        if (rt.freq != ICAL_NO_RECURRENCE) {
            icalcomponent_add_property(comp, icalproperty_new_rrule(rt));
        } else {
            /* Messed up the RRULE value. That's an error. */
            ctx->err->code = JMAPICAL_ERROR_UNKNOWN;
            invalidprop(ctx, NULL);
        }
    }

    endprop(ctx);
    buf_free(&buf);
}

static void
links_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *links)
{
    icalproperty *prop;
    struct buf buf = BUF_INITIALIZER;

    const char *id;
    json_t *link;
    json_object_foreach(links, id, link) {
        int pe;
        const char *href = NULL;
        const char *type = NULL;
        const char *name = NULL;
        json_int_t size = -1;

        beginprop_key(ctx, "links", id);

        pe = readprop(ctx, link, "href", 1, "s", &href);
        if (pe > 0) {
            if (!strlen(href)) {
                invalidprop(ctx, "href");
                href = NULL;
            }
        }
        if (JNOTNULL(json_object_get(link, "type"))) {
            readprop(ctx, link, "type", 0, "s", &type);
        }
        if (JNOTNULL(json_object_get(link, "name"))) {
            readprop(ctx, link, "name", 0, "s", &name);
        }
        if (JNOTNULL(json_object_get(link, "size"))) {
            pe = readprop(ctx, link, "size", 0, "I", &size);
            if (pe > 0 && size < 0) {
                invalidprop(ctx, "size");
            }
        }

        if (href && !have_invalid_props(ctx)) {
            /* href */
            icalattach *icalatt = icalattach_new_from_url(href);
            prop = icalproperty_new_attach(icalatt);

            /* type */
            if (type) {
                icalproperty_add_parameter(prop, icalparameter_new_fmttype(type));
            }

            /* title */
            /* XXX Could use Microsoft's X-FILENAME parameter to store ,
             * but that's only for binary attachments. For now, ignore name. */

            /* size */
            if (size >= 0) {
                buf_printf(&buf, "%lld", (long long) size);
                icalproperty_add_parameter(prop, icalparameter_new_size(buf_cstring(&buf)));
                buf_reset(&buf);
            }

            /* Add ATTACH property. */
            icalcomponent_add_property(comp, prop);
        }
        endprop(ctx);
        buf_free(&buf);
    }
}

/* Create or overwrite JMAP relatedTo in comp */
static void
relatedto_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *related)
{
    icalproperty *prop, *next;
    json_t *to;
    size_t i;

    /* Purge existing relatedTo properties from component */
    for (prop = icalcomponent_get_first_property(comp, ICAL_RELATEDTO_PROPERTY);
         prop;
         prop = next) {

        next = icalcomponent_get_next_property(comp, ICAL_RELATEDTO_PROPERTY);
        icalcomponent_remove_property(comp, prop);
        icalproperty_free(prop);
    }

    /* Add relatedTo */
    json_array_foreach(related, i, to) {
        const char *uid = json_string_value(to);

        beginprop_idx(ctx, "relatedTo", i);

        /* Validate uid */
        if (uid && strlen(uid)) {
            /* XXX check if UID exists? */
            /* XXX default relationship is PARENT, but should it be SIBLING? */
            icalcomponent_add_property(comp, icalproperty_new_relatedto(uid));
        } else {
            invalidprop(ctx, NULL);
        }
        endprop(ctx);
    }
}

static int
validate_location(toicalctx_t *ctx, json_t *loc)
{
    const char *val = NULL;
    json_t *address = NULL;
    size_t invalid_cnt = invalid_prop_count(ctx);
    short isempty = 1;
    int pe;

    /* name */
    pe = readprop(ctx, loc, "name", 0, "s", &val);
    if (pe > 0) {
        isempty = 0;
    }
    pe = readprop(ctx, loc, "rel", 0, "s", &val);
    if (pe > 0) {
        isempty = 0;
    }
    pe = readprop(ctx, loc, "accessInstruction", 0, "s", &val);
    if (pe > 0) {
        isempty = 0;
    }
    pe = readprop(ctx, loc, "timeZone", 0, "s", &val);
    if (pe > 0) {
        if (tz_from_tzid(val)) {
            isempty = 0;
        } else {
            invalidprop(ctx, "timeZone");
        }
    }
    /* address */
    pe = readprop(ctx, loc, "address", 0, "o", &address);
    if (pe > 0) {
        beginprop(ctx, "address");
        readprop(ctx, loc, "street", 0, "s", &val);
        readprop(ctx, loc, "locality", 0, "s", &val);
        readprop(ctx, loc, "region", 0, "s", &val);
        readprop(ctx, loc, "postcode", 0, "s", &val);
        readprop(ctx, loc, "country", 0, "s", &val);
        endprop(ctx);
        isempty = 0;
    }
    /* coordinates */
    pe = readprop(ctx, loc, "coordinates", 0, "s", &val);
    if (pe > 0) {
        isempty = 0;
    }
    /* uri */
    pe = readprop(ctx, loc, "uri", 0, "s", &val);
    if (pe > 0) {
        isempty = 0;
    }

    /* At least one property MUST be set */
    if ((invalid_prop_count(ctx) == invalid_cnt) && isempty) {
        invalidprop(ctx, NULL);
    }

    /* Location is invalid, if any invalid property has been added */
    return invalid_prop_count(ctx) == invalid_cnt;
}

static void
location_to_ical(icalcomponent *comp, const char *id, json_t *loc)
{
    /* XXX map GEO */
    /* XXX map X-STRUCTURED-LOCATION? */
    /* XXX map best pick to LOCATION: name, name/uri */

    /* Create a LOCATION or X-LOCATION property with "name" as value */
    icalproperty *prop;
    icalvalue *val;
    icalparameter *param;
    const char *name = NULL;
    struct buf buf = BUF_INITIALIZER;

    if (json_object_get(loc, "name")) {
        name = json_string_value(json_object_get(loc, "name"));
    }

    prop = icalproperty_new(ICAL_X_PROPERTY);
    icalproperty_set_x_name(prop, JMAPICAL_XPROP_LOCATION);

    /* XXX libical requires X-properties to have a value */
    val = icalvalue_new_from_string(ICAL_TEXT_VALUE, name ? name : "_");
    icalproperty_set_value(prop, val);

    /* Keep user-supplied location id */
    buf_reset(&buf);
    buf_setcstr(&buf, JMAPICAL_XPARAM_ID);
    buf_appendcstr(&buf, "=");
    /* XXX libical doesn't quote-escape param values? */
    buf_appendcstr(&buf, id);
    param = icalparameter_new_from_string(buf_cstring(&buf));
    icalproperty_add_parameter(prop, param);

    if (json_object_size(loc) >= 1) {
        /* Store the JSON represented location as ALTREP */
        char *buf64, *dump;
        size_t len, len64;

        /* Dump location as JSON and base64 encode*/
        dump = json_dumps(loc, JSON_COMPACT);
        len = strlen(dump);
        len64 = (4 * ((size_t) ceil(len / 3.0))) + 1;
        buf64 = xzmalloc(len64);
        sasl_encode64(dump, len, buf64, len64, NULL);

        /* Store parameter value */
        buf_reset(&buf);
        buf_setcstr(&buf, JMAPICAL_LOCATION_DATAURI_PREFIX);
        buf_appendcstr(&buf, buf64);

        /* Add ALTREP parameter */
        param = icalparameter_new_altrep(buf_cstring(&buf));
        icalproperty_add_parameter(prop, param);
        free(buf64);
        free(dump);
    }

    icalcomponent_add_property(comp, prop);
    buf_free(&buf);
}

/* Create or overwrite the JMAP locations in comp */
static void
locations_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *locations)
{
    json_t *loc;
    const char *id;

    /* Purge existing locations */
    remove_icalprop(comp, ICAL_LOCATION_PROPERTY);
    remove_icalprop(comp, ICAL_GEO_PROPERTY);
    remove_icalxprop(comp, JMAPICAL_XPROP_LOCATION);
    remove_icalxprop(comp, "X-APPLE-STRUCTURED-LOCATION");

    /* Bail out if no location needs to be set */
    if (!JNOTNULL(locations)) {
        return;
    }

    /* Add locations */
    json_object_foreach(locations, id, loc) {
        beginprop_key(ctx, "locations", id);

        /* Validate the location id */
        if (!strlen(id)) {
            invalidprop(ctx, NULL);
            endprop(ctx);
            continue;
        }

        /* Ignore end timeZone locations */
        if (location_is_endtimezone(loc)) {
            endprop(ctx);
            continue;
        }

        /* Validate location */
        if (!validate_location(ctx, loc)) {
            endprop(ctx);
            continue;
        }

        /* Add location */
        location_to_ical(comp, id, loc);
        endprop(ctx);
    }
}

/* Generate a X-JMAP-LOCATION iCalendar property.
 *
 * Translations look like:
 *
 *     X-JMAP-TRANSLATION;LANGUAGE=de;X-JMAP-PROP=title:Test
 *
 * where `LANGUAGE` denotes the translation id and `X-JMAP-PROP`
 * specifies the field to translate.
 *
 * Location translations also specify the location-id in `X-JMAP-ID`
 * and start the value of `X-JMAP-PROP` with `locations.`
 */
static void
translation_to_ical(icalcomponent *comp, const char *id,
                    const char *object, const char *field,
                    const char *text, const char *objectid)
{
    icalproperty *prop;
    icalvalue *val;
    icalparameter *param;

    /* Create X-JMAP-TRANSLATION property */
    prop = icalproperty_new(ICAL_X_PROPERTY);
    icalproperty_set_x_name(prop, JMAPICAL_XPROP_TRANSLATION);

    /* Set LANGUAGE parameter */
    param = icalparameter_new_language(id);
    icalproperty_add_parameter(prop, param);

    /* Set X-JMAP-PROP parameter */
    param = icalparameter_new(ICAL_X_PARAMETER);
    icalparameter_set_xname(param, JMAPICAL_XPARAM_PROP);
    if (object) {
        struct buf buf = BUF_INITIALIZER;
        buf_setcstr(&buf, object);
        buf_appendcstr(&buf, ".");
        buf_appendcstr(&buf, field);
        icalparameter_set_xvalue(param, buf_cstring(&buf));
        buf_free(&buf);
    } else {
        icalparameter_set_xvalue(param, field);
    }
    icalproperty_add_parameter(prop, param);

    if (objectid) {
        /* Set X-JMAP-ID parameter */
        xjmapid_to_ical(prop, objectid);
    }

    /* Set value */
    val = icalvalue_new_from_string(ICAL_TEXT_VALUE, text);
    icalproperty_set_value(prop, val);
    icalcomponent_add_property(comp, prop);
}

/* Create or overwrite the JMAP translations in comp */
static void
translations_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *translations)
{
    json_t *tr;
    const char *id;

    /* Purge existing translations */
    remove_icalxprop(comp, JMAPICAL_XPROP_TRANSLATION);

    /* Bail out if no translations need to be set */
    if (!JNOTNULL(translations)) {
        return;
    }

    /* Add translations */
    json_object_foreach(translations, id, tr) {
        const char *locid, *s;
        json_t *loctr;

        beginprop_key(ctx, "translations", id);

        /* Validate the location id */
        if (!strlen(id)) {
            invalidprop(ctx, NULL);
            endprop(ctx);
            continue;
        }

        /* Create a translation for each title and description */
        s = json_string_value(json_object_get(tr, "title"));
        if (s) translation_to_ical(comp, id, NULL, "title", s, NULL);

        s = json_string_value(json_object_get(tr, "description"));
        if (s) translation_to_ical(comp, id, NULL, "description", s, NULL);

        /* location translations */
        json_object_foreach(json_object_get(tr, "locations"), locid, loctr) {
            s = json_string_value(json_object_get(loctr, "name"));
            if (s) translation_to_ical(comp, id, "locations", "name", s, locid);

            s = json_string_value(json_object_get(loctr, "accessInstructions"));
            if (s) translation_to_ical(comp, id, "locations", "accessInstructions", s, locid);
        }

        /* link translations */
        json_object_foreach(json_object_get(tr, "links"), locid, loctr) {
            s = json_string_value(json_object_get(loctr, "title"));
            if (s) translation_to_ical(comp, id, "links", "title", s, locid);
        }

        endprop(ctx);
    }
}

static void set_language_icalprop(icalcomponent *comp, icalproperty_kind kind,
                                  const char *lang)
{
    icalproperty *prop;
    icalparameter *param;

    prop = icalcomponent_get_first_property(comp, kind);
    if (!prop) return;

    icalproperty_remove_parameter(prop, ICAL_LANGUAGE_PARAMETER);
    if (!lang) return;

    param = icalparameter_new(ICAL_LANGUAGE_PARAMETER);
    icalparameter_set_language(param, lang);
    icalproperty_add_parameter(prop, param);
}

static void
replyto_to_ical(toicalctx_t *ctx, icalcomponent *comp, const char *replyto)
{
    icalproperty *prop;
    char *addr = mailaddr_to_uri(replyto);
    if (!addr) {
        invalidprop(ctx, "replyTo");
        return;
    }

    remove_icalprop(comp, ICAL_ORGANIZER_PROPERTY);
    prop = icalproperty_new_organizer(addr);
    icalcomponent_add_property(comp, prop);

    free(addr);
}

/* Create or overwrite the iCalendar properties in VEVENT comp based on the
 * properties the JMAP calendar event.
 *
 * Collect all required timezone ids in ctx. 
 */
static void
calendarevent_to_ical(toicalctx_t *ctx, icalcomponent *comp, json_t *event) {
    int pe, seq; /* parse error */
    const char *val = NULL;
    int showAsFree = 0;
    icalproperty *prop = NULL;
    int create = ctx->mode & JMAPICAL_CREATE_MODE;

    icaltimezone *utc = icaltimezone_get_utc_timezone();
    icaltimetype now = icaltime_current_time_with_zone(utc);

    /* uid */
    icalcomponent_set_uid(comp, ctx->uid);

    /* isAllDay */
    readprop(ctx, event, "isAllDay", create, "b", &ctx->isallday);

    /* start, duration, timeZone */
    startend_to_ical(ctx, comp, event);

    /* relatedTo */
    json_t *relatedTo = NULL;
    pe = readprop(ctx, event, "relatedTo", 0, "o", &relatedTo);
    if (pe > 0) {
        if (relatedTo == json_null() || json_array_size(relatedTo)) {
            relatedto_to_ical(ctx, comp, relatedTo);
        } else {
            invalidprop(ctx, "relatedTo");
        }
    }

    /* prodId */
    val = NULL;
    pe = readprop(ctx, event, "prodId", 0, "s", &val);
    if (pe > 0 || create) {
        /* XXX always use Cyrus as prodId? */
        struct buf buf = BUF_INITIALIZER;
        if (!val) {
            /* XXX might want to not expose minor version? */
            buf_setcstr(&buf, "-//CyrusJMAP/");
            buf_appendcstr(&buf, cyrus_version());
            val = buf_cstring(&buf);
        }
        remove_icalprop(comp, ICAL_PRODID_PROPERTY);
        prop = icalproperty_new_prodid(val);
        icalcomponent_add_property(comp, prop);
        buf_free(&buf);
    }

    /* created */
    if (create) {
        dtprop_to_ical(comp, now, utc, 1, ICAL_CREATED_PROPERTY);
    }

    /* updated */
    dtprop_to_ical(comp, now, utc, 1, ICAL_DTSTAMP_PROPERTY);

    /* sequence */
    seq = create ? 0 : -1;
    if (readprop(ctx, event, "sequence", 0, "i", &seq) > 0 || seq >= 0) {
        icalcomponent_set_sequence(comp, seq);
    }

    /* title */
    pe = readprop(ctx, event, "title", create, "s", &val);
    if (pe > 0) {
        icalcomponent_set_summary(comp, val);
    }

    /* description */
    pe = readprop(ctx, event, "description", create, "s", &val);
    if (pe > 0) {
        icalcomponent_set_description(comp, val);
    }

    /* XXX htmlDescription */

    /* links */
    json_t *links = NULL;
    pe = readprop(ctx, event, "links", 0, "o", &links);
    if (pe > 0) {
        if (links == json_null() || json_object_size(links)) {
            links_to_ical(ctx, comp, links);
        } else {
            invalidprop(ctx, "links");
        }
    }

    /* language */
    if (json_object_get(event, "language") != json_null()) {
        pe = readprop(ctx, event, "language", 0, "s", &val);
        if (pe > 0 && strlen(val)) {
            if (json_object_get(event, "title")) {
                set_language_icalprop(comp, ICAL_SUMMARY_PROPERTY, val);
            }
            if (json_object_get(event, "description")) {
                set_language_icalprop(comp, ICAL_DESCRIPTION_PROPERTY, val);
            }
        }
    } else {
        set_language_icalprop(comp, ICAL_SUMMARY_PROPERTY, NULL);
        set_language_icalprop(comp, ICAL_DESCRIPTION_PROPERTY, NULL);
    }

    /* translations */
    json_t *translations = NULL;
    pe = readprop(ctx, event, "translations", 0, "o", &translations);
    if (pe > 0) {
        if (translations == json_null() || json_object_size(translations)) {
            translations_to_ical(ctx, comp, translations);
        } else {
            invalidprop(ctx, "translations");
        }
    }

    /* locations */
    json_t *locations = NULL;
    pe = readprop(ctx, event, "locations", 0, "o", &locations);
    if (pe > 0) {
        if (locations == json_null() || json_object_size(locations)) {
            locations_to_ical(ctx, comp, locations);
        } else {
            invalidprop(ctx, "locations");
        }
    }

    /* recurrenceRule */
    json_t *recurrence = NULL;
    pe = readprop(ctx, event, "recurrenceRule", 0, "o", &recurrence);
    if (pe > 0) {
        recurrence_to_ical(ctx, comp, recurrence);
    } else if (!pe && !create && ctx->tzstart_old != ctx->tzstart) {
        /* The start timezone has changed but none of the recurrences. */
        update_rrule_tz(ctx, comp);
    }

    /* XXX recurrenceOverrides */

    /* status */
    enum icalproperty_status status = ICAL_STATUS_NONE;
    pe = readprop(ctx, event, "status", 0, "s", &val);
    if (pe > 0) {
        if (!strcmp(val, "confirmed")) {
            status = ICAL_STATUS_CONFIRMED;
        } else if (!strcmp(val, "cancelled")) {
            status = ICAL_STATUS_CANCELLED;
        } else if (!strcmp(val, "tentative")) {
            status = ICAL_STATUS_TENTATIVE;
        } else {
            invalidprop(ctx, "status");
        }
    } else if (!pe && create) {
        status = ICAL_STATUS_CONFIRMED;
    }
    if (status != ICAL_STATUS_NONE) {
        remove_icalprop(comp, ICAL_STATUS_PROPERTY);
        icalcomponent_set_status(comp, status);
    }

    /* showAsFree */
    pe = readprop(ctx, event, "showAsFree", create, "b", &showAsFree);
    if (pe > 0) {
        enum icalproperty_transp v = showAsFree ? ICAL_TRANSP_TRANSPARENT : ICAL_TRANSP_OPAQUE;
        prop = icalcomponent_get_first_property(comp, ICAL_TRANSP_PROPERTY);
        if (prop) {
            icalproperty_set_transp(prop, v);
        } else {
            icalcomponent_add_property(comp, icalproperty_new_transp(v));
        }
    }

    /* participants */
    json_t *participants = NULL;
    pe = readprop(ctx, event, "participants", 0, "o", &participants);
    if (pe > 0) {
        if (participants == json_null() || json_object_size(participants)) {
            participants_to_ical(ctx, comp, participants);
        } else {
            invalidprop(ctx, "participants");
        }
    }

    /* replyTo */
    if (json_object_get(event, "replyTo") != json_null()) {
        pe = readprop(ctx, event, "replyTo", 0, "s", &val);
        if (pe > 0) {
            replyto_to_ical(ctx, comp, val);
        }
    } else {
        remove_icalprop(comp, ICAL_ORGANIZER_PROPERTY);
    }

    /* participantId: readonly */

    /* XXX useDefaultAlerts */

    /* alerts */
    json_t *alerts = NULL;
    pe = readprop(ctx, event, "alerts", 0, "o", &alerts);
    if (pe > 0) {
        if (alerts == json_null() || json_object_size(alerts)) {
            alerts_to_ical(ctx, comp, alerts);
        } else {
            invalidprop(ctx, "alerts");
        }
    } else if (!pe && !create && ctx->tzstart_old != ctx->tzstart) {
        /* The start timezone has changed but none of the alerts. */
        /* This is where we would like to update the timezones of any VALARMs
         * that have a TRIGGER value type of DATETIME (instead of the usual
         * DURATION type). Unfortunately, these DATETIMEs are stored in UTC.
         * Hence we can't tell if the event owner really wants to wake up
         * at e.g. 1am UTC or if it just was close to a local datetime during
         * creation of the iCalendar file. For now, do nothing about that. */
    }

    /* Bail out for property errors */
    if (have_invalid_props(ctx)) {
        return;
    }

    /* XXX
     * "If isAllDay is true, then the following restrictions apply:
     * the start property MUST have a time component of T00:00:00.
     * the timeZone property MUST be null.
     * the duration MUST only include a day component."
     */

    /* Check JMAP specification conditions on the generated iCalendar file, so 
     * this also doubles as a sanity check. Note that we *could* report a
     * property here as invalid, which had only been set by the client in a
     * previous request. */

    /* Either both organizer and attendees are null, or neither are. */
    if ((icalcomponent_get_first_property(comp, ICAL_ORGANIZER_PROPERTY) == NULL) !=
        (icalcomponent_get_first_property(comp, ICAL_ATTENDEE_PROPERTY) == NULL)) {
        invalidprop(ctx, "replyTo");
        invalidprop(ctx, "participants");
    }
}

icalcomponent*
jmapical_toical(json_t *obj, icalcomponent *src, const char *uid,
                jmapical_err_t *err, jmapical_opts_t *opts)
{
    icalcomponent *ical = NULL;
    icalcomponent *comp = NULL;
    struct toicalctx ctx;
    jmapical_err_t myerr;

    if (src) {
        ical = icalcomponent_new_clone(src);
        /* Locate the main VEVENT. */
        for (comp = icalcomponent_get_first_component(ical, ICAL_VEVENT_COMPONENT);
             comp;
             comp = icalcomponent_get_next_component(ical, ICAL_VEVENT_COMPONENT)) {
            if (!icalcomponent_get_first_property(comp, ICAL_RECURRENCEID_PROPERTY)) {
                break;
            }
        }
        if (!comp) {
            if (err) err->code = JMAPICAL_ERROR_ICAL;
            goto done;
        }
    } else {
        /* Create a new VCALENDAR. */
        ical = icalcomponent_new_vcalendar();
        icalcomponent_add_property(ical, icalproperty_new_version("2.0"));
        icalcomponent_add_property(ical, icalproperty_new_calscale("GREGORIAN"));

        /* Create a new VEVENT. */
        icaltimezone *utc = icaltimezone_get_utc_timezone();
        struct icaltimetype now = icaltime_from_timet_with_zone(time(NULL), 0, utc);
        comp = icalcomponent_new_vevent();
        icalcomponent_set_sequence(comp, 0);
        icalcomponent_set_dtstamp(comp, now);
        icalcomponent_add_property(comp, icalproperty_new_created(now));
        icalcomponent_add_component(ical, comp);
    }

    /* Convert the JMAP calendar event to ical. */

    /* Initialize context */
    memset(&ctx, 0, sizeof(struct toicalctx));
    ctx.mode = src ? JMAPICAL_UPDATE_MODE : JMAPICAL_CREATE_MODE;
    ctx.err = err ? err : &myerr;
    ctx.err->code = 0;
    ctx.err->props = NULL;
    ctx.opts = opts;
    ctx.invalid = json_pack("[]");
    ctx.comp = comp;
    /* Determine UID from any existing iCalendar data */
    if (src) {
        /* Get UID of first real component. */
        ctx.uid = icalcomponent_get_uid(comp);
        if (!ctx.uid) {
            err->code = JMAPICAL_ERROR_ICAL;
            goto done;
        }
        ctx.oldcomp = icalcomponent_new_clone(comp);
    }
    /* Parameter uid always overwrites any existing UID */
    if (uid) {
        ctx.uid = uid;
    }
    if (!ctx.uid) {
        err->code = JMAPICAL_ERROR_UID;
        goto done;
    }

    calendarevent_to_ical(&ctx, comp, obj);
    toicalctx_timezones_to_ical(&ctx, ical);
    if (ctx.oldcomp) {
        icalcomponent_free(ctx.oldcomp);
    }

    /* Bubble up any property errors. */
    if (json_array_size(ctx.invalid) && err) {
        err->code = JMAPICAL_ERROR_PROPS;
        err->props = ctx.invalid;
    } else {
        json_decref(ctx.invalid);
    }

    /* Free erroneous ical data */
    if (ctx.err->code) {
        icalcomponent_free(ical);
        ical = NULL;
    }

done:
    toicalctx_free(&ctx);
    return ical;
}

const char *
jmapical_strerror(int errno)
{
    switch (errno) {
        case 0:
            return "jmapical: success";
        case JMAPICAL_ERROR_CALLBACK:
            return "jmapical: callback error";
        case JMAPICAL_ERROR_MEMORY:
            return "jmapical: no memory";
        case JMAPICAL_ERROR_ICAL:
            return "jmapical: iCalendar error";
        case JMAPICAL_ERROR_PROPS:
            return "jmapical: property error";
        case JMAPICAL_ERROR_UID:
            return "jmapical: iCalendar uid error";
        default:
            return "jmapical: unknown error";
    }
}

/*
 * Construct a jevent string for an iCalendar component.
 */
EXPORTED struct buf *icalcomponent_as_jevent_string(icalcomponent *ical)
{
    struct buf *ret;
    json_t *jcal;
    size_t flags = JSON_PRESERVE_ORDER;
    char *buf;

    if (!ical) return NULL;

    jcal = jmapical_tojmap(ical, NULL, NULL, NULL);

    flags |= (config_httpprettytelemetry ? JSON_INDENT(2) : JSON_COMPACT);
    buf = json_dumps(jcal, flags);

    json_decref(jcal);

    ret = buf_new();
    buf_initm(ret, buf, strlen(buf));

    return ret;
}

EXPORTED icalcomponent *jevent_string_as_icalcomponent(const struct buf *buf)
{
    json_t *obj;
    json_error_t jerr;
    icalcomponent *ical;
    const char *str = buf_cstring(buf);

    if (!str) return NULL;

    obj = json_loads(str, 0, &jerr);
    if (!obj) {
        syslog(LOG_WARNING, "json parse error: '%s'", jerr.text);
        return NULL;
    }

    ical = jmapical_toical(obj, NULL, NULL, NULL, NULL);

    json_decref(obj);

    return ical;
}

