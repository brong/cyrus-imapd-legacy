/* dlist.h - list protocol for dump and sync
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
 * $Id: sync_support.h,v 1.12 2010/01/06 17:01:42 murch Exp $
 *
 * Original version written by David Carter <dpc22@cam.ac.uk>
 * Rewritten and integrated into Cyrus by Ken Murchison <ken@oceana.com>
 */

#ifndef INCLUDED_DLIST_H
#define INCLUDED_DLIST_H

#include "util.h"
#include "prot.h"
#include "mailbox.h"

struct dlist {
    char *name;
    struct dlist *head;
    struct dlist *tail;
    struct dlist *next;
    int type;
    char *sval;
    modseq_t nval; /* biggest type we need, more or less */
    struct message_guid gval; /* guid if any */
    char *part; /* so what if we're big! */
};

const char *dlist_reserve_path(const char *part, struct message_guid *guid);

struct dlist *dlist_atom(struct dlist *dl, const char *name, const char *val);
struct dlist *dlist_flag(struct dlist *dl, const char *name, const char *val);
struct dlist *dlist_num(struct dlist *dl, const char *name, unsigned long val);
struct dlist *dlist_date(struct dlist *dl, const char *name, time_t val);
struct dlist *dlist_modseq(struct dlist *dl, const char *name, modseq_t val);
struct dlist *dlist_buf(struct dlist *dl,
			const char *name, char *val, size_t len);
struct dlist *dlist_list(struct dlist *dl, const char *name);
struct dlist *dlist_kvlist(struct dlist *dl, const char *name);
struct dlist *dlist_guid(struct dlist *dl,
			 const char *name, struct message_guid *guid);
struct dlist *dlist_file(struct dlist *dl,
			 const char *name, const char *part,
			 struct message_guid *guid,
			 unsigned long size, const char *fname);
struct dlist *dlist_new(const char *name);
void dlist_free(struct dlist **dlp);

void dlist_print(struct dlist *dl, int printkeys, struct protstream *out);
char dlist_parse(struct dlist **dlp, int parsekeys, struct protstream *in);

void dlist_stitch(struct dlist *dl, struct dlist *child);
int dlist_getatom(struct dlist *dl, const char *name, const char **val);
int dlist_getbuf(struct dlist *dl,
		 const char *name, const char **val, size_t *len);
int dlist_getnum(struct dlist *dl, const char *name, unsigned long *val);
int dlist_getdate(struct dlist *dl, const char *name, time_t *val);
int dlist_getmodseq(struct dlist *dl, const char *name, modseq_t *val);
int dlist_getlist(struct dlist *dl, const char *name, struct dlist **val);
int dlist_getguid(struct dlist *dl,
		  const char *name, struct message_guid **guid);
int dlist_getfile(struct dlist *dl,
		  const char *name, const char **part,
		  struct message_guid **guid,
		  unsigned long *size, const char **fname);

const char *dlist_lastkey();

#endif /* INCLUDED_DLIST_H */
