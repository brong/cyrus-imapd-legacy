/* masterconfig.c -- Configuration routines for master process
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
 * $Id: masterconf.c,v 1.16 2010/01/06 17:01:53 murch Exp $
 */

#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sysexits.h>

#include "libconfig.c"

#if HAVE_UNISTD_H
# include <unistd.h>
#endif

#include "masterconf.h"

extern const char *MASTER_CONFIG_FILENAME;

struct configlist {
    char *key;
    char *value;
};

extern void fatal(const char *buf, int code);

int masterconf_init(const char *ident, const char *alt_config)
{
    char *buf;
    const char *prefix;

    /* Open the log file with the appropriate facility so we 
     * correctly log any config errors */
    openlog(ident, LOG_PID, SYSLOG_FACILITY);

    config_ident = ident;
    config_read(alt_config);

    prefix = config_getstring(IMAPOPT_SYSLOG_PREFIX);
    
    if(prefix) {
	int size = strlen(prefix) + 1 + strlen(ident) + 1;
	buf = xmalloc(size);
	strlcpy(buf, prefix, size);
	strlcat(buf, "/", size);
	strlcat(buf, ident, size);

	/* Reopen the log with the new prefix */
	closelog();
	openlog(buf, LOG_PID, SYSLOG_FACILITY);

        /* don't free the openlog() string! */
    }

    return 0;
}

struct entry {
    char *line;
    int lineno;
};

const char *masterconf_getstring(struct entry *e, const char *key, 
				 const char *def)
{
    char k[256];
    static char v[256];
    int i;
    char *p;

    strcpy(k, key);
    strcat(k, "=");

    p = strstr(e->line, k);
    if (p) {
	p += strlen(k);
	if (*p == '"') {
	    p++;
	    for (i = 0; i < 255; i++) {
		if (*p == '"') break;
		v[i] = *p++;
	    }
	    if (*p != '"') {
		sprintf(k, "configuration file %s: missing \" on line %d",
			MASTER_CONFIG_FILENAME, e->lineno);
		fatal(k, EX_CONFIG);
	    }
	} else {
	    /* one word */
	    for (i = 0; i < 255; i++) {
		if (Uisspace(*p)) break;
		v[i] = *p++;
	    }
	}
	v[i] = '\0';
	return v;
    } else {
	return def;
    }
}

int masterconf_getint(struct entry *e, 
		      const char *key, int def)
{
    const char *val = masterconf_getstring(e, key, NULL);

    if (!val) return def;
    if (!Uisdigit(*val) && 
	(*val != '-' || !Uisdigit(val[1]))) return def;
    return atoi(val);
}

int masterconf_getswitch(struct entry *e, const char *key, int def)
{
    const char *val = masterconf_getstring(e, key, NULL);

    if (!val) return def;

    if (val[0] == '0' || val[0] == 'n' ||
	(val[0] == 'o' && val[1] == 'f') || val[0] == 'f') {
	return 0;
    }
    else if (val[0] == '1' || val[0] == 'y' ||
	     (val[0] == 'o' && val[1] == 'n') || val[0] == 't') {
	return 1;
    }
    return def;
}

static void process_section(FILE *f, int *lnptr, 
			    masterconf_process *func, void *rock)
{
    struct entry e;
    char buf[4096];
    int lineno = *lnptr;

    while (fgets(buf, sizeof(buf), f)) {
	char *p, *q;

	lineno++;

	/* remove EOL character */
	if (buf[strlen(buf)-1] == '\n') buf[strlen(buf)-1] = '\0';
	/* remove starting whitespace */
	for (p = buf; *p && Uisspace(*p); p++);
	
	/* remove comments */
	q = strchr(p, '#');
	if (q) *q = '\0';

	/* skip empty lines or all comment lines */
	if (!*p) continue;
	if (*p == '}') break;

	for (q = p; Uisalnum(*q); q++) ;
	if (*q) { *q = '\0'; q++; }
	
	if (q - p > 0) {
	    /* there's a value on this line */
	    e.line = q;
	    e.lineno = lineno;
	    func(p, &e, rock);
	}

	/* end of section? */
	if (strchr(q, '}')) break;
    }

    *lnptr = lineno;
}

void masterconf_getsection(const char *section, masterconf_process *f,
			   void *rock)
{
    FILE *infile;
    int seclen = strlen(section);
    int level = 0;
    int lineno = 0;
    char buf[4096];

    infile = fopen(MASTER_CONFIG_FILENAME, "r");
    if (!infile) {
	snprintf(buf, sizeof(buf), "can't open configuration file %s: %s",
		MASTER_CONFIG_FILENAME, strerror(errno));
	fatal(buf, EX_CONFIG);
    }

    while (fgets(buf, sizeof(buf), infile)) {
	char *p, *q;

	lineno++;

	if (buf[strlen(buf)-1] == '\n') buf[strlen(buf)-1] = '\0';
	for (p = buf; *p && Uisspace(*p); p++);
	
	/* remove comments */
	q = strchr(p, '#');
	if (q) *q = '\0';

	/* skip empty lines or all comment lines */
	if (!*p) continue;
	
	if (level == 0 &&
	    *p == *section && !strncasecmp(p, section, seclen) &&
	    !Uisalnum(p[seclen])) {
	    for (p += seclen; *p; p++) {
		if (*p == '{') level++;
		if (*p == '}') level--;
	    }

	    /* valid opening; process the section */
	    if (level == 1) process_section(infile, &lineno, f, rock);

	    continue;
	}

	for (; *p; p++) {
	    if (*p == '{') level++;
	    if (*p == '}') level--;
	}
    }

    fclose(infile);
}


