#ifndef PUSHER_H
#define PUSHER_H

#include <stdint.h>
#include "mailbox.h"

int send_push_notification(struct mailbox *);

#endif /* PUSHER_H */
