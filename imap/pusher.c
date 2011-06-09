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
#include "global.h"

#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))

void
send_push_notification(struct mailbox *mailbox)
{
    ModSeqUpdate	msu;
    uint8_t		*buf;
    int			len, ret;
    struct sockaddr_un	sun;
    static int          s;

    char		*user;
    const char		*folders[2];
    const char		*named_socket;
    struct mboxname_parts mboxname_parts;

    /* double check this option is enabled */
    named_socket = config_getstring(IMAPOPT_MODSEQ_NOTIFY_SOCKET);
    if (!named_socket)
	return;

    /* deconstruct the mailbox name */
    ret = mboxname_to_parts(mailbox->name, &mboxname_parts);
    if (ret) {
	syslog(LOG_ERR, "PUSHER: mboxname_to_parts failed");
	return;
    }

    /* provision space and construct the username */
    user = malloc(strlen(mboxname_parts.userid) + strlen(mboxname_parts.domain)
									+ 2);
    if (!user) {
	syslog(LOG_ERR, "PUSHER: malloc failed: %m");
	goto out_free_parts;
    }
    sprintf(user, "%s@%s", mboxname_parts.userid, mboxname_parts.domain);

    /* setup the folders array */
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
    msu.service		= (char *)config_ident;
    msu.session		= session_id();

    /* Allocate a buffer for the packed output */
    len = mod_seq_update__get_packed_size(&msu);
    buf = calloc(len, 1);
    if (!buf) {
	syslog(LOG_ERR, "PUSHER: calloc failed: %m");
	goto out_free_user;
    }

    /* Pack the data */
    mod_seq_update__pack(&msu, buf);

    /* Create UNIX domain socket */
    if (!s) {
	s = socket(PF_UNIX, SOCK_DGRAM, 0);
	if (s == -1) {
	    s = 0;
	    syslog(LOG_ERR, "PUSHER: socket failed: %m");
	    goto out_free_buf;
	}
    }

    /* Create UNIX address */
    sun.sun_family = AF_UNIX;
    strcpy(sun.sun_path, named_socket);

    /* send the data, set the return code to the errno or 0 */
    ret = sendto(s, buf, len, 0, (struct sockaddr *)&sun, sizeof(sun));
    if (ret == -1)
	syslog(LOG_ERR, "PUSHER: sendto failed: %m");
    else if (ret != len)
	syslog(LOG_INFO, "PUSHER: sendto short write: %d < %d", ret, len);

    /* And we're done, cleanup */
out_free_buf:
    free(buf);
out_free_user:
    free(user);
out_free_parts:
    mboxname_free_parts(&mboxname_parts);
    return;
}
