/* util.c -- general utility functions
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
 * $Id: util.c,v 1.40 2010/06/28 12:06:43 brong Exp $
 */

#include <config.h>

#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <grp.h>
#include <limits.h>
#include <pwd.h>
#include <string.h>
#include <stdlib.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include <sys/socket.h>
#include <errno.h>

#include "exitcodes.h"
#include "util.h"
#include "xmalloc.h"

#define BEAUTYBUFSIZE 4096

const unsigned char convert_to_lowercase[256] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
    0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
    0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40, 'a', 'b', 'c', 'd', 'e', 'f', 'g',
    'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o',
    'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
    'x', 'y', 'z', 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
    0x60, 'a', 'b', 'c', 'd', 'e', 'f', 'g',
    'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o',
    'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
    'x', 'y', 'z', 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,
    0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f,
    0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
    0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
    0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7,
    0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
    0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
    0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf,
    0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7,
    0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf,
    0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7,
    0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
    0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
    0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff
};

const unsigned char convert_to_uppercase[256] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
    0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
    0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40, 'A', 'B', 'C', 'D', 'E', 'F', 'G',
    'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O',
    'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W',
    'X', 'Y', 'Z', 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
    0x60, 'A', 'B', 'C', 'D', 'E', 'F', 'G',
    'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O',
    'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W',
    'X', 'Y', 'Z', 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,
    0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f,
    0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
    0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
    0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7,
    0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
    0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
    0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf,
    0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7,
    0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf,
    0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7,
    0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
    0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
    0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff
};

/* convert string to all lower case
 */
char *lcase(char* str)
{
    char *scan = str;
    
    while (*scan) {
	*scan = TOLOWER(*scan);
	scan++;
    }

    return (str);
}

/* convert string to all upper case
 */
char *ucase(char* str)
{
    char *scan = str;
    
    while (*scan) {
	*scan = convert_to_uppercase[(unsigned char)(*scan)];
	scan++;
    }

    return (str);
}

/* clean up control characters in a string while copying it
 *  returns pointer to end of dst string.
 *  dst must have twice the length of source
 */
char *beautify_copy(char* dst, const char* src)
{
    unsigned char c;

    while (*src) {
	c = *src++ & 0x7F;
	if (!isprint(c)) {
	    *dst++ = '^';
	    if (c > ' ') {
		c = '?';
	    } else {
		c += '@';
	    }
	}
	*dst++ = c;
    }
    *dst = '\0';

    return (dst);
}


/* clean up control characters in a string while copying it
 *  returns pointer to a static buffer containing the cleaned-up version
 *  returns NULL on malloc() error
 */
char *beautify_string(const char* src)
{
    static char *beautybuf = NULL;
    static int beautysize = 0;
    int len;

    len = strlen(src) * 2 + 1;
    if (beautysize < len) {
	if (!beautysize) {
	    beautysize = len > BEAUTYBUFSIZE ? len : BEAUTYBUFSIZE;
	    beautybuf = xmalloc(beautysize);
	} else {
	    beautysize *= 2;
	    if (len > beautysize) beautysize = len;
	    beautybuf = xrealloc(beautybuf, beautysize);
	}
	if (!beautybuf) {
	    beautysize = 0;
	    return "";
	}
    }
    (void) beautify_copy(beautybuf, src);

    return (beautybuf);
}

/* do a binary search in a keyvalue array
 *  nelem is the number of keyvalue elements in the kv array
 *  cmpf is the comparison function (strcmp, strcasecmp, etc).
 *  returns NULL if not found, or key/value pair if found.
 */
keyvalue *kv_bsearch(const char* key, keyvalue* kv, int nelem,
		     int (*cmpf) (const char *s1, const char *s2))
{
    int top, mid = 0, bot, cmp = 0;

    cmp = 1;
    bot = 0;
    top = nelem - 1;
    while (top >= bot && (cmp = (*cmpf)(key, kv[mid = (bot + top) >> 1].key)))
	if (cmp < 0) {
	    top = mid - 1;
	} else {
	    bot = mid + 1;
	}

    return (cmp ? NULL : kv + mid);
}

/* Examine the name of a file, and return a single character
 *  (as an int) that can be used as the name of a hash
 *  directory.  Stop before the first dot.  Caller is responsible
 *  for skipping any prefix of the name.
 */
int dir_hash_c(const char *name, int full)
{
    int c;

    if (full) {
	unsigned char *pt;
	unsigned int n;
	enum {
	    DIR_X = 3,
	    DIR_Y = 5,
	    DIR_P = 23,
	    DIR_A = 'A'
	};

	n = 0;
	pt = (unsigned char *)name;
	while (*pt && *pt != '.') {
	    n = ((n << DIR_X) ^ (n >> DIR_Y)) ^ *pt;
	    ++pt;
	}
	c = DIR_A + (n % DIR_P);
    }
    else {
	c = tolower(*name);
	if (!Uisascii(c) || !Uislower(c)) c = 'q';
    }

    return c;
}

int cyrus_close_sock(int fd) 
{
    shutdown(fd, SHUT_RD);
    return close(fd);
}

void cyrus_reset_stdio()
{
    int devnull = open("/dev/null", O_RDWR, 0);
    
    if (devnull == -1) {
        fatal("open() on /dev/null failed", EC_TEMPFAIL);
    }
    
    /* stdin */
    shutdown(0, SHUT_RD);
    dup2(devnull, 0);
    
    /* stdout */
    shutdown(1, SHUT_RD);
    dup2(devnull, 1);
    
    /* stderr */
    shutdown(2, SHUT_RD);
    dup2(devnull, 2);

    if (devnull > 2) close(devnull);
}

/* Given a mkstemp(3) pattern for a filename,
 * create the file and return the file descriptor.
 *
 * This routine also unlinks the file so it won't appear in the
 * directory listing (but you won't have to worry about cleaning up
 * after it)
 */
int create_tempfile(const char *path) 
{
    int fd;
    char pattern[2048];

    if(snprintf(pattern, sizeof(pattern), "%s/cyrus_tmpfile_XXXXXX",
		path) >= (int) sizeof(pattern)){
	fatal("temporary file pathname is too long in prot_flush",
	      EC_TEMPFAIL);
    }

    fd = mkstemp(pattern);
    if(fd == -1) {
	return -1;
    } else if(unlink(pattern) == -1) {
	close(fd);
	return -1;
    }

    return fd;
}

/* Create all parent directories for the given path,
 * up to but not including the basename.
 */
int cyrus_mkdir(const char *path, mode_t mode __attribute__((unused)))
{
    char *p = (char *) path;
    int save_errno;
    struct stat sbuf;

    while ((p = strchr(p+1, '/'))) {
	*p = '\0';
	if (mkdir(path, 0755) == -1 && errno != EEXIST) {
	    save_errno = errno;
	    if (stat(path, &sbuf) == -1) {
		errno = save_errno;
		syslog(LOG_ERR, "IOERROR: creating directory %s: %m", path);
		return -1;
	    }
	}
	*p = '/';
    }

    return 0;
}

int become_cyrus(void)
{
    struct passwd *p;
    int newuid, newgid;
    int result;
    static int uid = 0;

    if (uid) return setuid(uid);

    p = getpwnam(CYRUS_USER);
    if (p == NULL) {
	syslog(LOG_ERR, "no entry in /etc/passwd for user %s", CYRUS_USER);
	return -1;
    }

    /* Save these in case initgroups does a getpw*() */
    newuid = p->pw_uid;
    newgid = p->pw_gid;

    if (initgroups(CYRUS_USER, newgid)) {
        syslog(LOG_ERR, "unable to initialize groups for user %s: %s",
	       CYRUS_USER, strerror(errno));
        return -1;
    }

    if (setgid(newgid)) {
        syslog(LOG_ERR, "unable to set group id to %d for user %s: %s",
              newgid, CYRUS_USER, strerror(errno));
        return -1;
    }

    result = setuid(newuid);

    /* Only set static uid if successful, else future calls won't reset gid */
    if (result == 0)
        uid = newuid;
    return result;
}

static int cmdtime_enabled = 0;
static struct timeval cmdtime_start, cmdtime_end, nettime_start, nettime_end;
static double totaltime, cmdtime, nettime;

double timesub(struct timeval * start, struct timeval * end) {
  return (double)(end->tv_sec - start->tv_sec) +
    (double)(end->tv_usec - start->tv_usec)/1000000.0;
}

void cmdtime_settimer(int enable) {
  cmdtime_enabled = enable;
}

void cmdtime_starttimer() {
  if (!cmdtime_enabled) { return; }
  gettimeofday(&cmdtime_start, 0);
  totaltime = cmdtime = nettime = 0.0;
}

void cmdtime_endtimer(double * pcmdtime, double * pnettime) {
  if (!cmdtime_enabled) { return; }
  gettimeofday(&cmdtime_end, 0);
  totaltime = timesub(&cmdtime_start, &cmdtime_end);
  cmdtime = totaltime - nettime;
  *pcmdtime = cmdtime;
  *pnettime = nettime;
}

void cmdtime_netstart() {
  if (!cmdtime_enabled) { return; }
  gettimeofday(&nettime_start, 0);
}

void cmdtime_netend() {
  if (!cmdtime_enabled) { return; }
  gettimeofday(&nettime_end, 0);
  nettime += timesub(&nettime_start, &nettime_end);
}

int parseint32(const char *p, const char **ptr, int32_t *res)
{
    int32_t result = 0;
    int gotchar = 0;

    if (!p) return -1;

    /* INT_MAX == 2147483647 */
    while (cyrus_isdigit(*p)) {
	if (result > 214748364 || (result == 214748364 && (*p > '7')))
	    fatal("num too big", EC_IOERR);
	result = result * 10 + *p++ - '0';
	gotchar = 1;
    }

    if (!gotchar) return -1;

    if (ptr) *ptr = p;
    if (res) *res = result;

    return 0;
}

int parseuint32(const char *p, const char **ptr, uint32_t *res)
{
    uint32_t result = 0;
    int gotchar = 0;

    if (!p) return -1;

    /* UINT_MAX == 4294967295U */
    while (cyrus_isdigit(*p)) {
	if (result > 429496729 || (result == 429496729 && (*p > '5')))
	    fatal("num too big", EC_IOERR);
	result = result * 10 + *p++ - '0';
	gotchar = 1;
    }

    if (!gotchar) return -1;

    if (ptr) *ptr = p;
    if (res) *res = result;

    return 0;
}

/* buffer handling functions */

#define BUF_GROW 1024
void buf_ensure(struct buf *buf, int n)
{
    int newlen = (buf->len + n + BUF_GROW);  /* XXX - size mod logic? */

    if (buf->alloc >= (buf->len + n))
	return;

    if (buf->alloc) {
	buf->s = xrealloc(buf->s, newlen);
    }
    else {
	char *s = xmalloc(newlen);
	if (buf->len) /* copy on write */
	    memcpy(s, buf->s, buf->len);
	buf->s = s;
    }

    buf->alloc = newlen;
}

const char *buf_cstring(struct buf *buf)
{
    if (!(buf->flags & BUF_CSTRING)) {
	buf_ensure(buf, 1);
	buf->s[buf->len] = '\0';
	buf->flags |= BUF_CSTRING;
    }

    return buf->s;
}

void buf_getmap(struct buf *buf, const char **base, int *len)
{
    *base = buf->s;
    *len = buf->len;
}

int buf_len(struct buf *buf)
{
    return buf->len;
}

void buf_reset(struct buf *buf)
{
    buf->len = 0;
    buf->flags &= ~BUF_CSTRING;
}

void buf_setcstr(struct buf *buf, char *str)
{
    buf_setmap(buf, str, strlen(str));
}

void buf_setmap(struct buf *buf, char *base, int len)
{
    buf_reset(buf);
    if (len) {
	buf_ensure(buf, len);
	memcpy(buf->s, base, len);
	buf->len = len;
    }
}

void buf_copy(struct buf *dst, struct buf *src)
{
    buf_setmap(dst, src->s, src->len);
}

void buf_append(struct buf *dst, struct buf *src)
{
    buf_appendmap(dst, src->s, src->len);
}

void buf_appendcstr(struct buf *buf, char *str)
{
    buf_appendmap(buf, str, strlen(str));
}

void buf_appendbit32(struct buf *buf, bit32 num)
{
    char item[4];
    *((bit32 *)item) = htonl(num);
    buf_appendmap(buf, item, 4);
}

void buf_appendmap(struct buf *buf, char *base, int len)
{
    if (len) {
	buf_ensure(buf, len);
	memcpy(buf->s + buf->len, base, len);
	buf->len += len;
	buf->flags &= ~BUF_CSTRING;
    }
}

void buf_putc(struct buf *buf, char c)
{
    buf_ensure(buf, 1);
    buf->s[buf->len++] = c;
    buf->flags &= ~BUF_CSTRING;
}

void buf_free(struct buf *buf)
{
    if (buf->alloc)
	free(buf->s);
    buf->alloc = 0;
    buf->s = NULL;
    buf->len = 0;
    buf->flags = 0;
}

