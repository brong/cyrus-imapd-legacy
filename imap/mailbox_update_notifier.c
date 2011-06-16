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

#include "mailbox_update_notifier.pb-c.h"
#include "mailbox.h"
#include "mboxname.h"
#include "global.h"
#include "xmalloc.h"

#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))

void
send_push_notification(struct mailbox *mailbox)
{
    MailboxUpdate	mu;
    uint8_t		*buf;
    int			len, ret;
    struct sockaddr_un	sun;
    static int          s;

    const char		*named_socket;

    MailboxUpdate__Mailbox mu_mailbox;
    MailboxUpdate__Mailbox *mu_mailboxes[2];
    struct mboxname_parts mboxname_parts;

    /* double check this option is enabled */
    named_socket = config_getstring(IMAPOPT_MAILBOX_UPDATE_NOTIFIER_SOCKET);
    if (!named_socket)
	return;

    /* deconstruct the mailbox name */
    ret = mboxname_to_parts(mailbox->name, &mboxname_parts);
    if (ret) {
	syslog(LOG_ERR, "MAILBOX_UPDATE_NOTIFIER: mboxname_to_parts failed");
	return;
    }

    /* create the MailboxUpdate message */
    mailbox_update__init(&mu);
    mu.user		= (char *)mboxname_to_userid(mailbox->name);
    mu.service		= (char *)config_ident;
    mu.session		= (char *)session_id();

    mailbox_update__mailbox__init(&mu_mailbox);
    mu_mailbox.modseq      = mailbox->i.highestmodseq;
    mu_mailbox.uidnext     = mailbox->i.last_uid + 1;
    mu_mailbox.uidvalidity = mailbox->i.uidvalidity;
    mu_mailbox.mailboxname =
		(char *)(mboxname_parts.box ? mboxname_parts.box : "INBOX");

    mu_mailboxes[0] = &mu_mailbox;
    mu_mailboxes[1] = NULL;

    mu.n_mailboxes	= 1;
    mu.mailboxes	= mu_mailboxes;

    /* Allocate a buffer for the packed output */
    len = mailbox_update__get_packed_size(&mu);
    buf = xmalloc(len);

    /* Pack the data */
    mailbox_update__pack(&mu, buf);

    /* Create UNIX domain socket if not earlier created*/
    if (!s) {
	s = socket(PF_UNIX, SOCK_DGRAM, 0);
	if (s == -1) {
	    s = 0;
	    syslog(LOG_ERR, "MAILBOX_UPDATE_NOTIFIER: socket failed: %m");
	    goto out_free;
	}
    }

    /* Create UNIX address */
    sun.sun_family = AF_UNIX;
    strcpy(sun.sun_path, named_socket);

    /* send the data, set the return code to the errno or 0 */
    ret = sendto(s, buf, len, 0, (struct sockaddr *)&sun, sizeof(sun));
    if (ret == -1)
	syslog(LOG_ERR, "MAILBOX_UPDATE_NOTIFIER: sendto failed: %m");
    else if (ret != len)
	syslog(LOG_INFO, "MAILBOX_UPDATE_NOTIFIER: sendto short write: %d < %d",
								    ret, len);

    /* And we're done, cleanup */
out_free:
    free(buf);
    mboxname_free_parts(&mboxname_parts);
    return;
}
