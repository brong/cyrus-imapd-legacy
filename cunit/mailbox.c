#include "config.h"
#include "cunit/cunit.h"
#include "xmalloc.h"
#include "global.h"
#include "retry.h"
#include "cyrusdb.h"
#include "libcyr_cfg.h"
#include "mailbox.h"
#include "mboxlist.h"

#define DBDIR	    "test-mb-dbdir"
#define MBOXNAME1   "user.smurf"
#define MBOXNAME2   "user.smurfette"
#define PARTITION   "default"
#define ACL	    "anyone lrswipkxtecda"


static void test_actions(void)
{
    struct mailbox *mailbox = NULL;
    int r;

    r = mailbox_create(MBOXNAME1, PARTITION, /*acl*/ACL,
		       /*uniqueid*/NULL, /*specialuse*/NULL,
		       /*options*/0, /*uidvalidity*/0,
		       /*highestmodseq*/0, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);

    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);

    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0xdeadbeef);
    CU_ASSERT_EQUAL(r, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0x00c0ffee);
    CU_ASSERT_EQUAL(r, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0xcafebabe);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);

    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 3);
    CU_ASSERT_EQUAL(mailbox_nop_action_tag, 0xcafebabe);

    mailbox_nop_action_count = 0;
    mailbox_nop_action_tag = 0;
    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);
    CU_ASSERT_EQUAL(mailbox_nop_action_tag, 0);
}

static void test_actions_rename_race(void)
{
    struct mailbox *mailbox = NULL;
    int r;

    r = mailbox_create(MBOXNAME1, PARTITION, /*acl*/ACL,
		       /*uniqueid*/NULL, /*specialuse*/NULL,
		       /*options*/0, /*uidvalidity*/0,
		       /*highestmodseq*/0, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);

    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);

    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0xdeadbeef);
    CU_ASSERT_EQUAL(r, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0x00c0ffee);
    CU_ASSERT_EQUAL(r, 0);
    r = mailbox_post_nop_action(MBOXNAME1, 0xcafebabe);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);

    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 3);
    CU_ASSERT_EQUAL(mailbox_nop_action_tag, 0xcafebabe);

    mailbox_nop_action_count = 0;
    mailbox_nop_action_tag = 0;
    r = mailbox_open_iwl(MBOXNAME1, &mailbox);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(mailbox);
    mailbox_close(&mailbox);
    CU_ASSERT_EQUAL(mailbox_nop_action_count, 0);
    CU_ASSERT_EQUAL(mailbox_nop_action_tag, 0);
}

static void config_read_string(const char *s)
{
    char *fname = xstrdup("/tmp/cyrus-cunit-configXXXXXX");
    int fd = mkstemp(fname);
    retry_write(fd, s, strlen(s));
    config_reset();
    config_read(fname);
    unlink(fname);
    free(fname);
    close(fd);
}

static int set_up(void)
{
    int r;
    struct mboxlist_entry mbentry;
    const char * const *d;
    static const char * const dirs[] = {
	DBDIR,
	DBDIR"/db",
	DBDIR"/conf",
	DBDIR"/conf/lock/",
	DBDIR"/conf/lock/user",
	DBDIR"/data",
	DBDIR"/data/user",
	DBDIR"/data/user/smurf",
	NULL
    };

    r = system("rm -rf " DBDIR);
    if (r)
	return r;

    for (d = dirs ; *d ; d++) {
	r = mkdir(*d, 0777);
	if (r < 0) {
	    int e = errno;
	    perror(*d);
	    return e;
	}
    }

    libcyrus_config_setstring(CYRUSOPT_CONFIG_DIR, DBDIR);
    config_read_string(
	"configdirectory: "DBDIR"/conf\n"
	"defaultpartition: "PARTITION"\n"
	"partition-"PARTITION": "DBDIR"/data\n"
    );

    cyrusdb_init();
    config_mboxlist_db = "skiplist";
    config_subscription_db = "berkeley";
    config_quota_db = "skiplist";

    quotadb_init(0);
    quotadb_open(NULL);

    mboxlist_init(0);
    mboxlist_open(NULL);

    memset(&mbentry, 0, sizeof(mbentry));
    mbentry.name = MBOXNAME1;
    mbentry.mbtype = 0;
    mbentry.partition = PARTITION;
    mbentry.acl = "";
    r = mboxlist_update(&mbentry, /*localonly*/1);

    return 0;
}

static int tear_down(void)
{
    int r;

    mboxlist_close();
    mboxlist_done();

    quotadb_close();
    quotadb_done();

    cyrusdb_done();
    config_mboxlist_db = NULL;
    config_subscription_db = NULL;
    config_quota_db = NULL;

    r = system("rm -rf " DBDIR);
    /* I'm ignoring you */

    return 0;
}
