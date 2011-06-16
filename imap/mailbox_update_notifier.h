#ifndef PUSHER_H
#define PUSHER_H

#include <stdint.h>
#include "mailbox.h"

void send_push_notification(struct mailbox *);

#endif /* PUSHER_H */
