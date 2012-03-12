#if HAVE_CONFIG_H
#include <config.h>
#endif
#include "cunit/cunit.h"
#include "parseaddr.h"
#include "imap/message.h"

static void test_parse_trivial(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Wed, 27 Oct 2010 18:37:26 +1100\r\n"
"Subject: Trivial testing email\r\n"
"Message-ID: <fake800@fastmail.fm>\r\n"
"X-Mailer: Norman\r\n"
"\r\n"
"Hello, World\n";
    int r;
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* From: Fred Bloggs <fbloggs@fastmail.fm> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.from);
    CU_ASSERT_STRING_EQUAL(body.from->name, "Fred Bloggs");
    CU_ASSERT_STRING_EQUAL(body.from->mailbox, "fbloggs");
    CU_ASSERT_STRING_EQUAL(body.from->domain, "fastmail.fm");
    CU_ASSERT_PTR_NULL(body.from->next);

    CU_ASSERT_PTR_NULL(body.reply_to);

    /* To: Sarah Jane Smith <sjsmith@gmail.com> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.to);
    CU_ASSERT_STRING_EQUAL(body.to->name, "Sarah Jane Smith");
    CU_ASSERT_STRING_EQUAL(body.to->mailbox, "sjsmith");
    CU_ASSERT_STRING_EQUAL(body.to->domain, "gmail.com");
    CU_ASSERT_PTR_NULL(body.to->next);

    CU_ASSERT_PTR_NULL(body.cc);

    CU_ASSERT_PTR_NULL(body.bcc);

    /* Date: Wed, 27 Oct 2010 18:37:26 +1100 */
    CU_ASSERT_STRING_EQUAL(body.date, "Wed, 27 Oct 2010 18:37:26 +1100");

    /* Subject: Trivial testing email */
    CU_ASSERT_STRING_EQUAL(body.subject, "Trivial testing email");

    /* Content-Type not specified, this is the default */
    CU_ASSERT_STRING_EQUAL(body.type, "TEXT");
    CU_ASSERT_STRING_EQUAL(body.subtype, "PLAIN");
    CU_ASSERT_PTR_NOT_NULL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "CHARSET");
    CU_ASSERT_STRING_EQUAL(body.params->value, "us-ascii");
    CU_ASSERT_PTR_NULL(body.params->next);

    CU_ASSERT_PTR_NULL(body.language);

    /* Message-ID: <fake800@fastmail.fm> */
    CU_ASSERT_STRING_EQUAL(body.message_id, "<fake800@fastmail.fm>");

    CU_ASSERT_PTR_NULL(body.in_reply_to);

    CU_ASSERT_PTR_NULL(body.references);

    CU_ASSERT_PTR_NULL(body.received_date);

    /* simple body */
    CU_ASSERT_EQUAL(body.numparts, 0);
    CU_ASSERT_PTR_NULL(body.subpart);

    /* check cacheheaders */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.cacheheaders.s);
    CU_ASSERT(strstr(body.cacheheaders.s, "Norman") != NULL);

    message_free_body(&body);
}


static void test_parse_simple(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"Reply-To: <bounce.me.harder@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Cc: Al Capone <al@speakeasy.com>\r\n"
"Bcc: Bugsy Moran <bugsy@garage.com>\r\n"
"Date: Thu, 28 Oct 2010 18:37:26 +1100\r\n"
"Subject: Simple testing email\r\n"
"Content-Type: text/plain; charset=\"utf-8\"\r\n"
"Content-Language: en\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"X-Mailer: Norman\r\n"
"In-Reply-To: <fake999@gmail.com>\r\n"
"Received: from foo.fastmail.fm (foo.fastmail.fm [10.0.0.1])\r\n"
"\tby bar.gmail.com (Software); Thu, 28 Oct 2010 18:55:54 +1100\r\n"
"\r\n"
"Hello, World\n";
    int r;
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* From: Fred Bloggs <fbloggs@fastmail.fm> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.from);
    CU_ASSERT_STRING_EQUAL(body.from->name, "Fred Bloggs");
    CU_ASSERT_STRING_EQUAL(body.from->mailbox, "fbloggs");
    CU_ASSERT_STRING_EQUAL(body.from->domain, "fastmail.fm");
    CU_ASSERT_PTR_NULL(body.from->next);

    /* Reply-To: <bounce.me.harder@fastmail.fm> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.reply_to);
    CU_ASSERT_PTR_NULL(body.reply_to->name);
    CU_ASSERT_STRING_EQUAL(body.reply_to->mailbox, "bounce.me.harder");
    CU_ASSERT_STRING_EQUAL(body.reply_to->domain, "fastmail.fm");
    CU_ASSERT_PTR_NULL(body.reply_to->next);

    /* To: Sarah Jane Smith <sjsmith@gmail.com> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.to);
    CU_ASSERT_STRING_EQUAL(body.to->name, "Sarah Jane Smith");
    CU_ASSERT_STRING_EQUAL(body.to->mailbox, "sjsmith");
    CU_ASSERT_STRING_EQUAL(body.to->domain, "gmail.com");
    CU_ASSERT_PTR_NULL(body.to->next);

    /* Cc: Al Capone <al@speakeasy.com> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.cc);
    CU_ASSERT_STRING_EQUAL(body.cc->name, "Al Capone");
    CU_ASSERT_STRING_EQUAL(body.cc->mailbox, "al");
    CU_ASSERT_STRING_EQUAL(body.cc->domain, "speakeasy.com");
    CU_ASSERT_PTR_NULL(body.cc->next);

    /* Bcc: Bugsy Moran <bugsy@garage.com> */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.bcc);
    CU_ASSERT_STRING_EQUAL(body.bcc->name, "Bugsy Moran");
    CU_ASSERT_STRING_EQUAL(body.bcc->mailbox, "bugsy");
    CU_ASSERT_STRING_EQUAL(body.bcc->domain, "garage.com");
    CU_ASSERT_PTR_NULL(body.bcc->next);

    /* Date: Thu, 28 Oct 2010 18:37:26 +1100 */
    CU_ASSERT_STRING_EQUAL(body.date, "Thu, 28 Oct 2010 18:37:26 +1100");

    /* Subject: Simple testing email */
    CU_ASSERT_STRING_EQUAL(body.subject, "Simple testing email");

    /* Content-Type: text/plain; charset="utf-8" */
    CU_ASSERT_STRING_EQUAL(body.type, "TEXT");
    CU_ASSERT_STRING_EQUAL(body.subtype, "PLAIN");
    CU_ASSERT_PTR_NOT_NULL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "CHARSET");
    CU_ASSERT_STRING_EQUAL(body.params->value, "utf-8");
    CU_ASSERT_PTR_NULL(body.params->next);

    /* Content-Language: en */
    CU_ASSERT_PTR_NOT_NULL(body.language);
    CU_ASSERT_PTR_NULL(body.language->attribute);
    CU_ASSERT_STRING_EQUAL(body.language->value, "EN");
    CU_ASSERT_PTR_NULL(body.language->next);

    /* Message-ID: <fake1000@fastmail.fm> */
    CU_ASSERT_STRING_EQUAL(body.message_id, "<fake1000@fastmail.fm>");

    /* In-Reply-To: <fake999@gmail.com> */
    CU_ASSERT_STRING_EQUAL(body.in_reply_to, "<fake999@gmail.com>");

    CU_ASSERT_PTR_NULL(body.references);

    /* Received: from foo.fastmail.fm (foo.fastmail.fm [10.0.0.1]) ... */
    CU_ASSERT_STRING_EQUAL(body.received_date, "Thu, 28 Oct 2010 18:55:54 +1100");

    /* simple body */
    CU_ASSERT_EQUAL(body.numparts, 0);
    CU_ASSERT_PTR_NULL(body.subpart);

    /* check cacheheaders */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.cacheheaders.s);
    CU_ASSERT(strstr(body.cacheheaders.s, "Norman") != NULL);

    message_free_body(&body);
}


/*
 * There are two different headers from which we can extract
 * the body.received_date field.  Test that the rules for
 * choosing which date are correctly applied.
 */
static void test_parse_rxdate(void)
{
#define DELIVERED   "Fri, 29 Oct 2010 13:07:07 +1100"
#define FIRST_RX    "Fri, 29 Oct 2010 13:05:01 +1100"
#define SECOND_RX   "Fri, 29 Oct 2010 13:03:03 +1100"
#define THIRD_RX    "Fri, 29 Oct 2010 13:01:01 +1100"
#define SENT	    "Thu, 28 Oct 2010 18:37:26 +1100"

    /* Message has neither Received: nor X-DeliveredInternalDate headers. */
    static const char msg_neither[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: " SENT "\r\n"
"Subject: Simple testing email\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"\r\n"
"Hello, World\n";

    /* Message has only Received: headers. */
    static const char msg_only_received[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: " SENT "\r\n"
"Subject: Simple testing email\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"Received: from mail.quux.com (mail.quux.com [10.0.0.1])\r\n"
"\tby mail.gmail.com (Software); " FIRST_RX "\r\n"
"Received: from mail.bar.com (mail.bar.com [10.0.0.1])\r\n"
"\tby mail.quux.com (Software); " SECOND_RX "\r\n"
"Received: from mail.fastmail.fm (mail.fastmail.fm [10.0.0.1])\r\n"
"\tby mail.bar.com (Software); " THIRD_RX "\r\n"
"\r\n"
"Hello, World\n";

    /* Message has only X-DeliveredInternalDate (weird!) */
    static const char msg_only_xdid[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: " SENT "\r\n"
"Subject: Simple testing email\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"X-Deliveredinternaldate: " DELIVERED "\r\n"
"\r\n"
"Hello, World\n";

    /* Message has both Received and X-DeliveredInternalDate in that order */
    static const char msg_received_then_xdid[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: " SENT "\r\n"
"Subject: Simple testing email\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"Received: from mail.quux.com (mail.quux.com [10.0.0.1])\r\n"
"\tby mail.gmail.com (Software); " FIRST_RX "\r\n"
"Received: from mail.bar.com (mail.bar.com [10.0.0.1])\r\n"
"\tby mail.quux.com (Software); " SECOND_RX "\r\n"
"Received: from mail.fastmail.fm (mail.fastmail.fm [10.0.0.1])\r\n"
"\tby mail.bar.com (Software); " THIRD_RX "\r\n"
"X-Deliveredinternaldate: " DELIVERED "\r\n"
"\r\n"
"Hello, World\n";

    /* Message has both X-DeliveredInternalDate and Received in that order */
    static const char msg_xdid_then_received[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: " SENT "\r\n"
"Subject: Simple testing email\r\n"
"Message-ID: <fake1000@fastmail.fm>\r\n"
"X-Deliveredinternaldate: " DELIVERED "\r\n"
"Received: from mail.quux.com (mail.quux.com [10.0.0.1])\r\n"
"\tby mail.gmail.com (Software); " FIRST_RX "\r\n"
"Received: from mail.bar.com (mail.bar.com [10.0.0.1])\r\n"
"\tby mail.quux.com (Software); " SECOND_RX "\r\n"
"Received: from mail.fastmail.fm (mail.fastmail.fm [10.0.0.1])\r\n"
"\tby mail.bar.com (Software); " THIRD_RX "\r\n"
"\r\n"
"Hello, World\n";

    int r;
    struct body body;

    /* Neither: no received_date */
    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg_neither, sizeof(msg_neither)-1, &body);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NULL(body.received_date);
    message_free_body(&body);

    /* Received only: first seen Received */
    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg_only_received,
			     sizeof(msg_only_received)-1, &body);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(body.received_date, FIRST_RX);
    message_free_body(&body);

    /* X-DeliveredInternalDate only: use that */
    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg_only_xdid,
			     sizeof(msg_only_xdid)-1, &body);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(body.received_date, DELIVERED);
    message_free_body(&body);

    /* both, Received first: use X-DeliveredInternalDate */
    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg_received_then_xdid,
			     sizeof(msg_received_then_xdid)-1, &body);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(body.received_date, DELIVERED);
    message_free_body(&body);

    /* both, X-DeliveredInternalDate first: use X-DeliveredInternalDate */
    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg_xdid_then_received,
			     sizeof(msg_xdid_then_received)-1, &body);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(body.received_date, DELIVERED);
    message_free_body(&body);
}


static void test_mime_trivial(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"Reply-To: <bounce.me.harder@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Thu, 28 Oct 2010 18:37:26 +1100\r\n"
"Subject: MIME testing email\r\n"
"X-Mailer: Norman\r\n"
"MIME-Version: 1.0\r\n"
"Content-Type: multipart/mixed; boundary=\"2b47bc7b64285b8be25dcdca86fbc501b048eab1\"\r\n"
"Content-Language: en\r\n"
"Message-ID: <fake1001@fastmail.fm>\r\n"
"\r\n"
"--2b47bc7b64285b8be25dcdca86fbc501b048eab1\r\n"
"\r\n"
"Hello, World\n"
"\r\n--2b47bc7b64285b8be25dcdca86fbc501b048eab1--\r\n";
    int r;
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Content-Type: */
    CU_ASSERT_STRING_EQUAL(body.type, "MULTIPART");
    CU_ASSERT_STRING_EQUAL(body.subtype, "MIXED");
    CU_ASSERT_PTR_NOT_NULL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "BOUNDARY");
    CU_ASSERT_STRING_EQUAL(body.params->value, "2b47bc7b64285b8be25dcdca86fbc501b048eab1");
    CU_ASSERT_PTR_NULL(body.params->next);

    /*
     * RFC2046 says that all headers and in particular the Content-Type:
     * header may be missing in an entity, and if so the default
     * Content-Type is text/plain;charset="us-ascii"
     */

    /* simple body */
    CU_ASSERT_EQUAL(body.numparts, 1);
    CU_ASSERT_PTR_NOT_NULL(body.subpart);
    CU_ASSERT_STRING_EQUAL(body.subpart[0].type, "TEXT");
    CU_ASSERT_STRING_EQUAL(body.subpart[0].subtype, "PLAIN");
    CU_ASSERT_PTR_NOT_NULL(body.subpart[0].params);
    CU_ASSERT_STRING_EQUAL(body.subpart[0].params->attribute, "CHARSET");
    CU_ASSERT_STRING_EQUAL(body.subpart[0].params->value, "us-ascii");
    CU_ASSERT_PTR_NULL(body.subpart[0].params->next);

    /* check cacheheaders */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.cacheheaders.s);
    CU_ASSERT(strstr(body.cacheheaders.s, "Norman") != NULL);
    CU_ASSERT_PTR_NULL(body.subpart[0].cacheheaders.s);

    message_free_body(&body);
}

static void test_mime_multiple(void)
{
#define TEXT_PART \
    "Hello, World"
#define HTML_PART \
    "<html><head><title>Hello, World</title></head>\r\n" \
    "<body>\r\n" \
    "<p>Hello, World</p>\r\n" \
    "<body></html>"

    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"Reply-To: <bounce.me.harder@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Thu, 28 Oct 2010 18:37:26 +1100\r\n"
"Subject: MIME testing email\r\n"
"X-Mailer: Norman\r\n"
"MIME-Version: 1.0\r\n"
"Content-Type: multipart/mixed; boundary=\"7225e50d962de81173be22223f706458743c3a9a\"\r\n"
"Content-Language: en\r\n"
"Message-ID: <fake1003@fastmail.fm>\r\n"
"\r\n"
"--7225e50d962de81173be22223f706458743c3a9a\r\n"
"Content-Type: text/plain; charset=\"us-ascii\"\r\n"
"\r\n"
TEXT_PART "\r\n"
"--7225e50d962de81173be22223f706458743c3a9a\r\n"
"Content-Type: text/html; charset=\"us-ascii\"\r\n"
"\r\n"
HTML_PART "\r\n"
"--7225e50d962de81173be22223f706458743c3a9a\r\n"
"Content-Type: image/png\r\n"
"Content-Disposition: attachment; filename=cyrus-favicon.png\r\n"
"Content-Transfer-Encoding: base64\r\n"
"\r\n"
"iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAAAXNSR0IArs4c6QAAAAZiS0dEAP8A\r\n"
"/wD/oL2nkwAAAAlwSFlzAAALEwAACxMBAJqcGAAAAAd0SU1FB9sBEQEMHNieJnIAAAIsSURBVDjL\r\n"
"tZNPSNNhGMc/r+xSUY4hbHO1LYyRSXRw4iaSRVFCiNBf8BA/mwWVB1sQFGgdgqjfph6i0EEUXaxJ\r\n"
"3tTmkA6zQxieVlR0GP0xy7n9Ftipng6/NZMM6dBzenmf5/083+d53gf+l42Njkm1zychTZPZ2Vn5\r\n"
"p8dRPSIuu0NcdodsdDgl4K+TqVRqRYj6dZhKpaQv2kuhYJBOp0GKXgGlzLBAMAjAdV2nakuVWka6\r\n"
"3N0tyYkJWc2G43GJ6vpyNbGBQXHZHZJMJFYFJBMJqfb55MHQkABYQpomV3p6QKmSVIC+SATD+AqA\r\n"
"x7OJ9o6OYtGKglEg3HWOkKYJle7N0hgIynA8LtlsdlUF2WxWkomENAYbxGV3iGXR6SHl38ePWwN4\r\n"
"vV5sNhsA/dEo+byBUgq3e0lBPpej55rOU38L5d/HwVrfJDx8JegjUrHdL726/tfsd2Ix8TTsFvQR\r\n"
"If5arPW7pAwUKAWebcyfv0144hnHDh0hl8uV+rGwsMDJ9hOcvT9C5tQN8NaAmIMoE5HizBWsK4e2\r\n"
"Czx+/4U9O5uYTCZ5Pj1N64EWRief8O1o2IwpNlNEsJS+kwhkXlAe78eo2sHM1lraOrsAmOu4CpmX\r\n"
"VAxeZL75ONTtL6kzAQKM34UPbzHOREpZ5i7dM8FrN4C3hvmmw/DoJryZgdbTvwEyaajdC82aWYoU\r\n"
"qWvWL//xAhzshMUCfH5neqp9PvlodS4tR7G2P5ZmhfvK/Cd+At3OXF7AwYF1AAAAAElFTkSuQmCC\r\n"
"\r\n--7225e50d962de81173be22223f706458743c3a9a--\r\n";
    int r;
    struct body body;
    struct body *part;
    struct message_content mcontent;
    const char *types[2] = { NULL, NULL };
    struct bodypart **parts = NULL;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Content-Type: */
    CU_ASSERT_STRING_EQUAL(body.type, "MULTIPART");
    CU_ASSERT_STRING_EQUAL(body.subtype, "MIXED");
    CU_ASSERT_PTR_NOT_NULL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "BOUNDARY");
    CU_ASSERT_STRING_EQUAL(body.params->value, "7225e50d962de81173be22223f706458743c3a9a");
    CU_ASSERT_PTR_NULL(body.params->next);

    CU_ASSERT_EQUAL(body.numparts, 3);
    CU_ASSERT_PTR_NOT_NULL(body.subpart);

    part = &body.subpart[0];
    CU_ASSERT_PTR_NOT_NULL(part);
    CU_ASSERT_STRING_EQUAL(part->type, "TEXT");
    CU_ASSERT_STRING_EQUAL(part->subtype, "PLAIN");
    CU_ASSERT_PTR_NOT_NULL(part->params);
    CU_ASSERT_STRING_EQUAL(part->params->attribute, "CHARSET");
    CU_ASSERT_STRING_EQUAL(part->params->value, "us-ascii");
    CU_ASSERT_PTR_NULL(part->params->next);
    CU_ASSERT_PTR_NULL(part->disposition);
    CU_ASSERT_PTR_NULL(part->encoding);

    part = &body.subpart[1];
    CU_ASSERT_PTR_NOT_NULL(part);
    CU_ASSERT_STRING_EQUAL(part->type, "TEXT");
    CU_ASSERT_STRING_EQUAL(part->subtype, "HTML");
    CU_ASSERT_PTR_NOT_NULL(part->params);
    CU_ASSERT_STRING_EQUAL(part->params->attribute, "CHARSET");
    CU_ASSERT_STRING_EQUAL(part->params->value, "us-ascii");
    CU_ASSERT_PTR_NULL(part->params->next);
    CU_ASSERT_PTR_NULL(part->disposition);
    CU_ASSERT_PTR_NULL(part->encoding);

    part = &body.subpart[2];
    CU_ASSERT_PTR_NOT_NULL(part);
    CU_ASSERT_STRING_EQUAL(part->type, "IMAGE");
    CU_ASSERT_STRING_EQUAL(part->subtype, "PNG");
    CU_ASSERT_PTR_NULL(part->params);
    CU_ASSERT_STRING_EQUAL(part->disposition, "ATTACHMENT");
    CU_ASSERT_STRING_EQUAL(part->encoding, "BASE64");

    mcontent.base = msg;
    mcontent.len = sizeof(msg)-1;
    mcontent.body = &body;

    types[0] = "TEXT/PLAIN";
    parts = NULL;
    message_fetch_part(&mcontent, types, &parts);
    CU_ASSERT_PTR_NOT_NULL(parts);
    if (parts) {
	CU_ASSERT_PTR_NOT_NULL(parts[0]);
	CU_ASSERT_PTR_NULL(parts[1]);
	CU_ASSERT_STRING_EQUAL(parts[0]->decoded_body, TEXT_PART);
	free(parts[0]);
	free(parts);
	parts = NULL;
    }

    types[0] = "TEXT/HTML";
    parts = NULL;
    message_fetch_part(&mcontent, types, &parts);
    CU_ASSERT_PTR_NOT_NULL(parts);
    if (parts) {
	CU_ASSERT_PTR_NOT_NULL(parts[0]);
	CU_ASSERT_PTR_NULL(parts[1]);
	CU_ASSERT_STRING_EQUAL(parts[0]->decoded_body, HTML_PART);
	free(parts[0]);
	free(parts);
	parts = NULL;
    }

    /* check cacheheaders */
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.cacheheaders.s);
    CU_ASSERT(strstr(body.cacheheaders.s, "Norman") != NULL);
    CU_ASSERT_PTR_NULL(body.subpart[0].cacheheaders.s);
    CU_ASSERT_PTR_NULL(body.subpart[1].cacheheaders.s);
    CU_ASSERT_PTR_NULL(body.subpart[2].cacheheaders.s);

    message_free_body(&body);
#undef TEXT_PART
#undef HTML_PART
}

/*
 * RFC2231 specifies, amongst other things, a method for
 * breaking up across multiple lines, long parameter values
 * which cannot have whitespace inserted into them.
 */
static void test_rfc2231_continuations(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Wed, 27 Oct 2010 18:37:26 +1100\r\n"
/* This example based on one in RFC2231 */
"Content-Type: message/external-body; access-type=URL;\r\n"
"\tURL*0=\"ftp://\";\r\n"
"\tURL*1=\"cs.utk.edu/pub/moore/\";\r\n"
"\tURL*2=\"bulk-mailer/bulk-mailer.tar\"\r\n"
"Subject: RFC2231 continuation testing email\r\n"
"Message-ID: <fake1002@fastmail.fm>\r\n"
"\r\n"
"Hello, World\n";
    int r;
    static const char URL[] = "ftp://cs.utk.edu/pub/moore/bulk-mailer/bulk-mailer.tar";
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Date: Wed, 27 Oct 2010 18:37:26 +1100 */
    CU_ASSERT_STRING_EQUAL(body.date, "Wed, 27 Oct 2010 18:37:26 +1100");

    /* Subject: Trivial testing email */
    CU_ASSERT_STRING_EQUAL(body.subject, "RFC2231 continuation testing email");

    CU_ASSERT_STRING_EQUAL(body.type, "MESSAGE");
    CU_ASSERT_STRING_EQUAL(body.subtype, "EXTERNAL-BODY");
    CU_ASSERT_PTR_NOT_NULL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "ACCESS-TYPE");
    CU_ASSERT_STRING_EQUAL(body.params->value, "URL");
    CU_ASSERT_PTR_NOT_NULL(body.params->next);
    CU_ASSERT_STRING_EQUAL(body.params->next->attribute, "URL");
    CU_ASSERT_STRING_EQUAL(body.params->next->value, URL);
    CU_ASSERT_PTR_NULL(body.params->next->next);

    message_free_body(&body);
}

/*
 * RFC2231 has a second syntax for continuations, which
 * indicates the language & charset info may be encoded
 * in the value and allows for %xx encoded chars.
 */
static void test_rfc2231_extended_continuations(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Wed, 27 Oct 2010 18:37:26 +1100\r\n"
/* This example also loosely based on one in RFC2231 */
"Content-Type: application/x-stuff;\r\n"
"\ttitle*0*=us-ascii'en'This%20is%20even%20more%20;\r\n"
"\ttitle*1*=%2A%2A%2Afun%2A%2A%2A%20;\r\n"
"\ttitle*2=\"isn't it!\"\r\n"
"Subject: RFC2231 extended continuation testing email\r\n"
"Message-ID: <fake1002@fastmail.fm>\r\n"
"\r\n"
"Hello, World\n";
    int r;
    static const char TITLE[] =
		"us-ascii'en'This%20is%20even%20more%20%2A%2A%2Afun%2A%2A%2A%20isn%27t%20it!";
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Date: Wed, 27 Oct 2010 18:37:26 +1100 */
    CU_ASSERT_STRING_EQUAL(body.date, "Wed, 27 Oct 2010 18:37:26 +1100");

    /* Subject: Trivial testing email */
    CU_ASSERT_STRING_EQUAL(body.subject, "RFC2231 extended continuation testing email");

    CU_ASSERT_STRING_EQUAL(body.type, "APPLICATION");
    CU_ASSERT_STRING_EQUAL(body.subtype, "X-STUFF");
    CU_ASSERT_PTR_NOT_NULL_FATAL(body.params);
    CU_ASSERT_STRING_EQUAL(body.params->attribute, "TITLE*");
    CU_ASSERT_STRING_EQUAL(body.params->value, TITLE);
    CU_ASSERT_PTR_NULL(body.params->next);

    message_free_body(&body);
}

static void test_references(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Wed, 27 Oct 2010 18:37:26 +1100\r\n"
"Subject: Trivial testing email\r\n"
"Message-ID: <fake800@fastmail.fm>\r\n"
"In-Reply-To: <fake701@fastmail.fm>\r\n"
"References: <fake332@gmail.com> <fake437@garage.com>\r\n"
"\t<fake589@speakeasy.com>\t(Hey ignore me I'm a comment) <fake679@gmail.com>\r\n"
"\t<fake701@fastmail.fm>\r\n"
"\r\n"
"Hello, World\n";
    int r;
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Message-ID: <fake800@fastmail.fm> */
    CU_ASSERT_STRING_EQUAL(body.message_id, "<fake800@fastmail.fm>");

    /* In_Reply-To: <fake701@fastmail.fm> */
    CU_ASSERT_STRING_EQUAL(body.in_reply_to, "<fake701@fastmail.fm>");

    CU_ASSERT_PTR_NOT_NULL(strstr(body.references, "<fake332@gmail.com>"));
    CU_ASSERT_PTR_NOT_NULL(strstr(body.references, "<fake437@garage.com>"));
    CU_ASSERT_PTR_NOT_NULL(strstr(body.references, "<fake589@speakeasy.com>"));
    CU_ASSERT_PTR_NOT_NULL(strstr(body.references, "<fake679@gmail.com>"));
    CU_ASSERT_PTR_NOT_NULL(strstr(body.references, "<fake701@fastmail.fm>"));

    message_free_body(&body);
}

static void test_x_me_message_id(void)
{
    static const char msg[] =
"From: Fred Bloggs <fbloggs@fastmail.fm>\r\n"
"To: Sarah Jane Smith <sjsmith@gmail.com>\r\n"
"Date: Wed, 27 Oct 2010 18:37:26 +1100\r\n"
"Subject: Trivial testing email\r\n"
"X-ME-Message-ID: <fake1700@fastmail.fm>\r\n"
"\r\n"
"Hello, World\n";
    int r;
    struct body body;

    memset(&body, 0x45, sizeof(body));
    r = message_parse_mapped(msg, sizeof(msg)-1, &body);

    CU_ASSERT_EQUAL(r, 0);

    /* Message-ID: <fake1700@fastmail.fm> */
    CU_ASSERT_PTR_NULL(body.message_id);
    CU_ASSERT_STRING_EQUAL(body.x_me_message_id, "<fake1700@fastmail.fm>");
    CU_ASSERT_PTR_NULL(body.in_reply_to);
    CU_ASSERT_PTR_NULL(body.references);

    message_free_body(&body);
}

#undef TESTCASE
#define TESTCASE(input, explen, expout) \
    buf_reset(&b); \
    message_write_nstring(&b, input); \
    buf_cstring(&b); \
    CU_ASSERT_EQUAL(b.len, explen); \
    CU_ASSERT(!strcmp(b.s, expout))

static void test_write_nstring(void)
{
    struct buf b = BUF_INITIALIZER;

    /* NULL string */
    TESTCASE(0, 3, "NIL");

    /* Zero length string */
    TESTCASE("", 2, "\"\"");

    /* Boring string */
    TESTCASE("Hello", 7, "\"Hello\"");

    /* String with non-dangerous whitespace */
    TESTCASE("Hello World\tagain", 19, "\"Hello World\tagain\"");

    /* String with dangerous whitespace */
    TESTCASE("Good\rBye\nEarth", 20, "{14}\r\nGood\rBye\nEarth");

    /* String with embedded dquote */
    TESTCASE("Quot\"able", 14, "{9}\r\nQuot\"able");

    /* String with embedded percent */
    TESTCASE("per%ent", 12, "{7}\r\nper%ent");

    /* String with embedded backslash */
    TESTCASE("slash\\dot", 14, "{9}\r\nslash\\dot");

    /* String with embedded 8-bit chars */
    TESTCASE("Hi I'm \330l\345f", 17, "{11}\r\nHi I'm \330l\345f");

    /* Boring but overly long string */
    {
	struct buf llb = BUF_INITIALIZER;
	int i;

	for (i = 0 ; i<500 ; i++)
	    buf_appendcstr(&llb, "blah ");
	buf_cstring(&llb);

	buf_reset(&b);
	message_write_nstring(&b, llb.s);
	buf_cstring(&b);
	CU_ASSERT_EQUAL(b.len, llb.len+8); \
	CU_ASSERT_STRING_EQUAL(b.s+8, llb.s);
	b.s[8] = '\0';
	CU_ASSERT_STRING_EQUAL(b.s, "{2500}\r\n");
	buf_free(&llb);
    }

    /* embedded NULs not handled in message_write_nstring */
    TESTCASE("Hello\0World", 7, "\"Hello\"");

    /* embedded NULs in message_write_nstring_map */
    buf_reset(&b);
    message_write_nstring_map(&b, "Hello\0World", 11);
    buf_cstring(&b);
    CU_ASSERT_EQUAL(b.len, 17);
    CU_ASSERT(!memcmp(b.s, "{11}\r\nHello\0World", 17));

    buf_free(&b);
}

#undef TESTPARSE
#define TESTPARSE(expout, explen, input) \
    buf_setcstr(&b, input); \
    buf_putc(&b, ')'); \
    ptr = b.s; \
    output = parse_nstring(&ptr); \
    CU_ASSERT(!memcmp(output, expout, explen))

static void test_parse_nstring(void)
{
    struct buf b = BUF_INITIALIZER;
    char *output;
    char *ptr;

    /* NULL string */
    buf_setcstr(&b, "NIL)");
    ptr = b.s;
    output = parse_nstring(&ptr);
    CU_ASSERT_PTR_NULL(output);

    /* Zero length string */
    TESTPARSE("", 0, "\"\"");

    /* Boring string */
    TESTPARSE("Hello", 5, "\"Hello\"");

    /* String with non-dangerous whitespace */
    TESTPARSE("Hello World\tagain", 17, "\"Hello World\tagain\"");

    /* String with dangerous whitespace */
    TESTPARSE("Good\rBye\nEarth", 14, "{14}\r\nGood\rBye\nEarth");

    /* String with embedded dquote */
    TESTPARSE("Quot\"able", 9, "{9}\r\nQuot\"able");

    /* String with embedded percent */
    TESTPARSE("per%ent", 7, "{7}\r\nper%ent");

    /* String with embedded backslash */
    TESTPARSE("slash\\dot", 9, "{9}\r\nslash\\dot");

    /* String with embedded 8-bit chars */
    TESTPARSE("Hi I'm \330l\345f", 11, "{11}\r\nHi I'm \330l\345f");

    /* And some stuff seen in the wild */
    TESTPARSE("Lloyd Burns\\\"", 13, "\"Lloyd Burns\\\"\" NIL \"MariogenoaRobertson\" \"fiftyfoureleven.com\")");

    buf_free(&b);
}

#undef TESTCASE

#define TESTCASE(input, expout) \
    buf_reset(&b); \
    buf_init_ro(&s, input, sizeof(input)-1); \
    message_write_xdrstring(&b, &s); \
    CU_ASSERT_EQUAL(b.len, sizeof(expout)-1); \
    CU_ASSERT(!memcmp(b.s, expout, sizeof(expout)-1))

static void test_write_xdrstring(void)
{
    struct buf b = BUF_INITIALIZER;
    struct buf s = BUF_INITIALIZER;

    /* Zero length string */
    TESTCASE("", "\0\0\0\0");

    /* 1-length string */
    TESTCASE("H", "\0\0\0\001H\0\0\0");

    /* 2-length string */
    TESTCASE("He", "\0\0\0\002He\0\0");

    /* 3-length string */
    TESTCASE("Hel", "\0\0\0\003Hel\0");

    /* 4-length string */
    TESTCASE("Hell", "\0\0\0\004Hell");

    /* 5-length string */
    TESTCASE("Hello", "\0\0\0\005Hello\0\0\0");

    buf_free(&b);
    buf_free(&s);
}

#undef TESTCASE
