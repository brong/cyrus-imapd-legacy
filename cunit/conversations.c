#if HAVE_CONFIG_H
#include <config.h>
#endif
#include "cunit/cunit.h"
#include "conversations.h"
#include "global.h"
#include "cyrusdb.h"
#include "libcyr_cfg.h"
#include "xmalloc.h"

#define DBDIR	"test-dbdir"
#define DBNAME	"conversations.db"
#define DBNAME2	"conversations2.db"

static void test_open(void)
{
    int r;
    struct conversations_state state;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

static void test_getset(void)
{
    int r;
    struct conversations_state state;
    static const char C_MSGID[] = "<0001.1288854309@example.com>";
    static const conversation_id_t C_CID = 0x12345689abcdef0;
    conversation_id_t cid;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* Database is empty, so get should succeed and report no results */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_cid(&state, C_MSGID, C_CID);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* get should still succeed after the transaction is over */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* get should still succeed after the db is closed & reopened */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

static void test_abort(void)
{
    int r;
    struct conversations_state state;
    static const char C_MSGID[] = "<0002.1288854309@example.com>";
    static const conversation_id_t C_CID = 0x10345689abcdef2;
    conversation_id_t cid;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* Database is empty, so get should succeed and report no results */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_cid(&state, C_MSGID, C_CID);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    /* closing without a commit aborts the txn */
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* open the db again */
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* the set vanished with the txn abort, so get should
     * succeed and report no results */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

static void test_prune(void)
{
    int r;
    struct conversations_state state;
    static const char C_MSGID1[] = "<0003.1288854309@example.com>";
    static const conversation_id_t C_CID1 = 0x1045689abcdef23;
    time_t stamp1;
    static const char C_MSGID2[] = "<0004.1288854309@example.com>";
    static const conversation_id_t C_CID2 = 0x105689abcdef234;
    time_t stamp2;
    static const char C_MSGID3[] = "<0005.1288854309@example.com>";
    static const conversation_id_t C_CID3 = 0x10689abcdef2345;
    time_t stamp3;
    conversation_id_t cid;
    unsigned int nseen = 0, ndeleted = 0;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* Add keys, with delays in between */
    /* TODO: CUnit needs a time warping system */

    r = conversations_set_cid(&state, C_MSGID1, C_CID1);
    CU_ASSERT_EQUAL(r, 0);
    stamp1 = time(NULL);

    sleep(4);

    r = conversations_set_cid(&state, C_MSGID2, C_CID2);
    CU_ASSERT_EQUAL(r, 0);
    stamp2 = time(NULL);

    sleep(4);

    r = conversations_set_cid(&state, C_MSGID3, C_CID3);
    CU_ASSERT_EQUAL(r, 0);
    stamp3 = time(NULL);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* Should be able to get all 3 msgids */

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID1);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID3, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID3);

    /* Prune out the oldest two.  Note we try to make this test
     * stable with respect to timing artifacts, such as clock
     * granularity, by careful choice of sleep times. */
    r = conversations_prune(&state, stamp2+(stamp3-stamp2)/2,
			    &nseen, &ndeleted);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT(nseen >= 3);
    CU_ASSERT(ndeleted >= 2);
    CU_ASSERT(nseen - ndeleted >= 1);

    /* gets of the oldest two records should succeed
     * but report no record, and a get of the newest
     * record should succeed */

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state, C_MSGID3, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID3);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

/* Test whether it is possible to open two databases at
 * the same time. */
static void test_two(void)
{
    int r;
    struct conversations_state state1;
    struct conversations_state state2;
    static const char C_MSGID1[] = "<0006.1288854309@example.com>";
    static const conversation_id_t C_CID1 = 0x1089abcdef23456;
    static const char C_MSGID2[] = "<0007.1288854309@example.com>";
    static const conversation_id_t C_CID2 = 0x109abcdef234567;
    conversation_id_t cid;

    memset(&state1, 0, sizeof(state1));
    memset(&state2, 0, sizeof(state2));

    r = conversations_open(&state1, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_open(&state2, DBNAME2);
    CU_ASSERT_EQUAL(r, 0);

    /* Databases are empty, so gets of either msgid from either db
     * should succeed and report no results */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state1, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state1, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state2, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state2, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_cid(&state1, C_MSGID1, C_CID1);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_set_cid(&state2, C_MSGID2, C_CID2);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it
     * and not the value in the other db */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state1, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID1);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state1, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state2, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_cid(&state2, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    r = conversations_close(&state1);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_close(&state2);
    CU_ASSERT_EQUAL(r, 0);
}

/* test CID encoding */
static void test_cid_encode(void)
{
    static const conversation_id_t CID1 = 0x01089abcdef23456;
    static const char STR1[] = "01089abcdef23456";
    static const conversation_id_t CID2 = NULLCONVERSATION;
    static const char STR2[] = "NIL";
    const char *r;

    r = conversation_id_encode(CID1);
    CU_ASSERT_STRING_EQUAL(r, STR1);

    r = conversation_id_encode(CID2);
    CU_ASSERT_STRING_EQUAL(r, STR2);
}

/* test CID decoding */
static void test_cid_decode(void)
{
    static const char STR1[] = "01089abcdef23456";
    static const conversation_id_t CID1 = 0x01089abcdef23456;
    static const char STR2[] = "NIL";
    static const conversation_id_t CID2 = NULLCONVERSATION;
    conversation_id_t cid;
    int r;

    memset(&cid, 0x45, sizeof(cid));
    r = conversation_id_decode(&cid, STR1);
    CU_ASSERT_EQUAL(r, 1);
    CU_ASSERT_EQUAL(cid, CID1);

    memset(&cid, 0x45, sizeof(cid));
    r = conversation_id_decode(&cid, STR2);
    CU_ASSERT_EQUAL(r, 1);
    CU_ASSERT_EQUAL(cid, CID2);
}


static int init(void)
{
    int r;

    r = system("rm -rf " DBDIR);
    if (r)
	return r;

    r = mkdir(DBDIR, 0777);
    if (r < 0) {
	int e = errno;
	perror(DBDIR);
	return e;
    }

    r = mkdir(DBDIR "/db", 0777);
    if (r < 0) {
	int e = errno;
	perror(DBDIR "/db");
	return e;
    }

    libcyrus_config_setstring(CYRUSOPT_CONFIG_DIR, DBDIR);
    cyrusdb_init();
    config_conversations_db = cyrusdb_fromname("berkeley");

    return 0;
}

static int cleanup(void)
{
    int r;

    cyrusdb_done();
    config_conversations_db = NULL;

    r = system("rm -rf " DBDIR);
    /* I'm ignoring you */

    return 0;
}
