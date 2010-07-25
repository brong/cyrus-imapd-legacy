/* Messagingengine.com generic functions */

#ifndef ME_H
#define ME_H

/* rated support */

#define ME_RATE_SOCK "/var/state/rated/rated"

extern int me_send_rate(char * username, char *resource, int count);

/* sasl_enc support */

extern char * me_create_sasl_enc(char *username);

#endif
