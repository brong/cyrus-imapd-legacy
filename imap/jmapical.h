/* jmapical.h --Routines to convert JMAP calendar events and iCalendar
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

#ifndef JMAPICAL_H
#define JMAPICAL_H

#ifdef __cplusplus
extern "C" {
#endif

#include <jansson.h>
#include <libical/ical.h>

#define JMAPICAL_ERROR_UNKNOWN  -1
#define JMAPICAL_ERROR_CALLBACK 1
#define JMAPICAL_ERROR_MEMORY   2
#define JMAPICAL_ERROR_ICAL     3
#define JMAPICAL_ERROR_PROPS    4
#define JMAPICAL_ERROR_UID      5

const char*
jmapical_strerror(int errno);

typedef struct {
    int code;      /* one of the predefined jmapical error codes, or zero */
    json_t *props; /* erroneous JMAP properties, if any. */
} jmapical_err_t;

typedef struct {
    /* determines the value of the JMAP CalendarEvent isYou field
     *
     * Any value greater than 0 set isYou to true for addr, false if 0.
     * Any value less than 0 indicates an error. */
    short (*is_you)(const char *addr, void *data);

    /* user-defined data passed to callback functions */
    void *data;
} jmapical_opts_t;

/* Converts the iCalendar component ical to JMAP.
 *
 * Does not set the id, calendarId or any extension proprties.
 *
 * ical:  must contain one VEVENT, and any number of recurrences
 * props: optional JSON object whose keys name the properties to be converted
 * err:   optional error receiver
 * opts:  optional conversion options
 */
json_t*
jmapical_tojmap(icalcomponent *ical, struct json_t *props,
                jmapical_err_t *err, jmapical_opts_t *opts);

/* Convert the JMAP object obj to iCalendar.
 *
 * ojb:  must contain a JMAP calendar event
 * ical: optional iCalendar VEVENT to mix obj into
 * uid:  optional if ical is set. Used as iCalendar UID.
 * err:  optional error receiver
 * opts: optional conversion options
 */

/* FIXME uid is not necessary, always source from obj */
icalcomponent*
jmapical_toical(json_t *obj, icalcomponent *ical, const char *uid,
                jmapical_err_t *err, jmapical_opts_t *opts);

#ifdef __cplusplus
}
#endif

#endif 
