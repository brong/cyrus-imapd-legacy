/* message.h -- Message parsing
 $Id: message.h,v 1.3.6.1 2000/07/06 18:46:26 ken3 Exp $
 
 # Copyright 1998 Carnegie Mellon University
 # 
 # No warranties, either expressed or implied, are made regarding the
 # operation, use, or results of the software.
 #
 # Permission to use, copy, modify and distribute this software and its
 # documentation is hereby granted for non-commercial purposes only
 # provided that this copyright notice appears in all copies and in
 # supporting documentation.
 #
 # Permission is also granted to Internet Service Providers and others
 # entities to use the software for internal purposes.
 #
 # The distribution, modification or sale of a product which uses or is
 # based on the software, in whole or in part, for commercial purposes or
 # benefits requires specific, additional permission from:
 #
 #  Office of Technology Transfer
 #  Carnegie Mellon University
 #  5000 Forbes Avenue
 #  Pittsburgh, PA  15213-3890
 #  (412) 268-4387, fax: (412) 268-7395
 #  tech-transfer@andrew.cmu.edu
 *
 */
#ifndef INCLUDED_MESSAGE_H
#define INCLUDED_MESSAGE_H

#ifndef P
#ifdef __STDC__
#define P(x) x
#else
#define P(x) ()
#endif
#endif

#include <stdio.h>

#include "prot.h"
#include "mailbox.h"

extern int message_copy_strict P((struct protstream *from, FILE *to,
				  unsigned size));

/* Flags for parsing message date/time - to be bitwise OR'd */
#define PARSE_DATE	(1<<0)
#define PARSE_TIME	(1<<1)
#define PARSE_ZONE	(1<<2)

extern time_t message_parse_date P((char *hdr, unsigned flags));
extern int message_parse_file P((FILE *infile, struct mailbox *mailbox,
				 struct index_record *message_index));
extern int message_parse_mapped P((const char *msg_base, unsigned long msg_len,
				   struct mailbox *mailbox,
				   struct index_record *message_index));

#endif /* INCLUDED_MESSAGE_H */
