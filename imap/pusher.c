#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/socket.h>
#include <syslog.h>

#include <config.h>
#include <imapopts.h>
#include <libconfig.h>

#include "Pusher.pb-c.h"
#include "mailbox.h"
#include "mboxname.h"

#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))

int
send_push_notification(struct mailbox *mailbox)
{
    ModSeqUpdate	msu;
    uint8_t		*buf;
    int			len, s, ret;
    struct sockaddr_un	sun;

    char		*user;
    char		*folders[2];
    char		*named_socket;
    struct mboxname_parts mboxname_parts;

    named_socket = config_getstring(IMAPOPT_MODSEQ_NOTIFY_SOCKET);
    if (!named_socket)
	return 0;

    ret = mboxname_to_parts(mailbox->name, &mboxname_parts);
    if (ret) {
	syslog(LOG_ERR, "PUSHER: mboxname_to_parts failed");
	return EINVAL;
    }

    user = malloc(strlen(mboxname_parts.userid) + strlen(mboxname_parts.domain)
									+ 1);
    if (!user) {
        ret = ENOMEM;
	syslog(LOG_ERR, "PUSHER: out of memory");
        goto out_free_parts;
	return ENOMEM;
    }
    sprintf(user, "%s@%s", mboxname_parts.userid, mboxname_parts.domain);

    folders[0] = mboxname_parts.box;
    folders[1] = NULL;

    /* create the ModSeqUpdate message */
    mod_seq_update__init(&msu);
    msu.user		= user;
    msu.n_folders	= 1;
    msu.folders		= (char **)folders;
    msu.modseq		= mailbox->i.highestmodseq;
    msu.uidnext		= mailbox->i.last_uid + 1;
    msu.uidvalidity	= mailbox->i.uidvalidity;
    msu.service		= config_ident;

    /* Allocate a buffer for the packed output */
    len = mod_seq_update__get_packed_size(&msu);
    buf = malloc(len);
    if (!buf) {
	ret = errno;
	goto out_free_user;
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
    strcpy(sun.sun_path, named_socket);
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
out_free_user:
    free(user);
out_free_parts:
    mboxname_free_parts(&mboxname_parts);
    return ret;
}
