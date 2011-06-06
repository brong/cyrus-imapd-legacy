#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/socket.h>
#include <pcre.h>
#include <syslog.h>

#include "Pusher.pb-c.h"
#include "mailbox.h"

#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))

int
send_push_notification(struct mailbox *mailbox)
{
    ModSeqUpdate	msu;
    uint8_t		*buf;
    int			len, s, ret;
    struct sockaddr_un	sun;

    char		*user;
    const char		*folders[2];
    uint64_t		modseq;

    pcre		*re;
    const char		*error;
    int			erroffset;
    int			ovector[12];
    const char		**listptr;

    re = pcre_compile("^user\\.(.*?)\\.([^@]+)(@.*)$", 0, &error, &erroffset,
								NULL);
    if (erroffset) {
	syslog(LOG_ERR, "PUSHER: pcre_compile failed at %d: %s", erroffset,
									error);
	return EINVAL;
    }

    ret = pcre_exec(re, NULL, mailbox->name, strlen(mailbox->name), 0, 0,
						ovector, ARRAY_SIZE(ovector));
    if (!ret) {
	syslog(LOG_ERR, "PUSHER: no match");
	return EINVAL;
    }

    pcre_get_substring_list(mailbox->name, ovector, ret, &listptr);

    user = malloc(strlen(listptr[1]) + strlen(listptr[3]) + 1);
    sprintf(user, "%s%s", listptr[1], listptr[3]);

    folders[0] = listptr[2];
    folders[1] = NULL;

    modseq = mailbox->i.highestmodseq;

    /* create the ModSeqUpdate message */
    mod_seq_update__init(&msu);
    msu.user		= user;
    msu.n_folders	= 1;
    msu.folders		= (char **)folders;
    msu.modseq		= modseq;

    /* Allocate a buffer for the packed output */
    len = mod_seq_update__get_packed_size(&msu);
    buf = malloc(len);
    if (!buf) {
	ret = errno;
	goto out_free_listptr;
    }

    /* Pack the data */
    mod_seq_update__pack(&msu, buf);

    /* Create UNIX domain socket */
    s = socket(PF_UNIX, SOCK_DGRAM, 0);
    if (s == -1) {
	ret = errno;
	goto out_free_buf;
    }

    /* Connect UNIX domain socket */
    sun.sun_family = AF_UNIX;
    strcpy(sun.sun_path, "/var/run/pusher/pusher.sock");
    ret = connect(s, (struct sockaddr *)&sun, sizeof(sun));
    if (ret) {
	ret = errno;
	goto out_close;
    }

    /* send the data, set the return code to the errno or 0 */
    ret = send(s, buf, len, 0) == -1 ? errno : 0;

    /* And we're done, cleanup */
out_close:
    close(s);
out_free_buf:
    free(buf);
out_free_listptr:
    pcre_free_substring_list(listptr);
    return ret;
}
