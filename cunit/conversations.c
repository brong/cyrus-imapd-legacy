#if HAVE_CONFIG_H
#include <config.h>
#endif
#include "cunit/cunit.h"
#include "conversations.h"
#include "global.h"
#include "strarray.h"
#include "cyrusdb.h"
#include "libcyr_cfg.h"
#include "message.h"	    /* for VECTOR_SIZE */
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
    r = conversations_get_msgid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_msgid(&state, C_MSGID, C_CID);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* get should still succeed after the transaction is over */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* get should still succeed after the db is closed & reopened */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID, &cid);
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
    r = conversations_get_msgid(&state, C_MSGID, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_msgid(&state, C_MSGID, C_CID);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID, &cid);
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
    r = conversations_get_msgid(&state, C_MSGID, &cid);
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

    r = conversations_set_msgid(&state, C_MSGID1, C_CID1);
    CU_ASSERT_EQUAL(r, 0);
    stamp1 = time(NULL);

    sleep(4);

    r = conversations_set_msgid(&state, C_MSGID2, C_CID2);
    CU_ASSERT_EQUAL(r, 0);
    stamp2 = time(NULL);

    sleep(4);

    r = conversations_set_msgid(&state, C_MSGID3, C_CID3);
    CU_ASSERT_EQUAL(r, 0);
    stamp3 = time(NULL);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* Should be able to get all 3 msgids */

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID1);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID3, &cid);
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
    r = conversations_get_msgid(&state, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID3, &cid);
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
    r = conversations_get_msgid(&state1, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state1, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state2, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state2, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    /* set should succeed */
    r = conversations_set_msgid(&state1, C_MSGID1, C_CID1);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_set_msgid(&state2, C_MSGID2, C_CID2);
    CU_ASSERT_EQUAL(r, 0);

    /* get should now succeed and report the value we gave it
     * and not the value in the other db */
    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state1, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID1);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state1, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state2, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, NULLCONVERSATION);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state2, C_MSGID2, &cid);
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

static void rename_cb(const char *mboxname,
		      conversation_id_t from_cid,
		      conversation_id_t to_cid,
		      void *rock)
{
    strarray_t *notifies = (strarray_t *)rock;

    strarray_append(notifies, mboxname);
    strarray_append(notifies, conversation_id_encode(from_cid));
    strarray_append(notifies, conversation_id_encode(to_cid));
}

static int num_folders(conversation_t *conv)
{
    int n = 0;
    conv_folder_t *folder;

    if (!conv) return 0;

    for (folder = conv->folders ; folder ; folder = folder->next)
	n++;

    return n;
}

static int find_folder(conversation_t *conv, const char *name)
{
    conv_folder_t *folder;

    if (!conv) return 0;

    for (folder = conv->folders ; folder ; folder = folder->next) {
	if (!strcmp(name, folder->mboxname))
	    return 1;
    }

    return 0;
}

static void test_cid_rename(void)
{
    int r;
    struct conversations_state state;
    static const char FOLDER1[] = "fnarp.com!user.smurf";
    static const char FOLDER2[] = "fnarp.com!user.smurf.foo bar";
    static const char FOLDER3[] = "fnarp.com!user.smurf.quux.foonly";
    static const char C_MSGID1[] = "<0008.1288854309@example.com>";
    static const char C_MSGID2[] = "<0009.1288854309@example.com>";
    static const char C_MSGID3[] = "<0010.1288854309@example.com>";
    static const conversation_id_t C_CID1 = 0x10bcdef23456789a;
    static const conversation_id_t C_CID2 = 0x10cdef23456789ab;
    strarray_t notifies = STRARRAY_INITIALIZER;
    conversation_id_t cid;
    conversation_t *conv;
    conv_folder_t *folder;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* setup the records we expect */
    r = conversations_set_msgid(&state, C_MSGID1, C_CID1);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_set_msgid(&state, C_MSGID2, C_CID1);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_set_msgid(&state, C_MSGID3, C_CID1);
    CU_ASSERT_EQUAL(r, 0);

    conv = conversation_new();
    CU_ASSERT_PTR_NOT_NULL(conv);

    folder = NULL;
    conversation_add_folder(conv, FOLDER1, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 1;

    folder = NULL;
    conversation_add_folder(conv, FOLDER2, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 8;

    folder = NULL;
    conversation_add_folder(conv, FOLDER3, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 5;

    conv->modseq = 8;
    r = conversations_set_data(&state, C_CID1, conv);
    CU_ASSERT_EQUAL(r, 0);

    /* commit & close */
    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
    conversation_free(conv);
    conv = NULL;

    /* open the db again */
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* do a rename */
    r = conversations_rename_cid(&state, C_CID1, C_CID2,
				 rename_cb, (void *)&notifies);
    CU_ASSERT_EQUAL(r, 0);
    /* check that the rename callback was called with the right data */
    CU_ASSERT_EQUAL(notifies.count, 9);
    CU_ASSERT_STRING_EQUAL(notifies.data[1], conversation_id_encode(C_CID1));
    CU_ASSERT_STRING_EQUAL(notifies.data[2], conversation_id_encode(C_CID2));
    CU_ASSERT_STRING_EQUAL(notifies.data[4], conversation_id_encode(C_CID1));
    CU_ASSERT_STRING_EQUAL(notifies.data[5], conversation_id_encode(C_CID2));
    CU_ASSERT_STRING_EQUAL(notifies.data[7], conversation_id_encode(C_CID1));
    CU_ASSERT_STRING_EQUAL(notifies.data[8], conversation_id_encode(C_CID2));
    r = strarray_find(&notifies, FOLDER1, 0);
    CU_ASSERT(r >= 0 && (r % 3) == 0);
    r = strarray_find(&notifies, FOLDER2, 0);
    CU_ASSERT(r >= 0 && (r % 3) == 0);
    r = strarray_find(&notifies, FOLDER3, 0);
    CU_ASSERT(r >= 0 && (r % 3) == 0);
    strarray_fini(&notifies);


    /* commit & close */
    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* open the db again */
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* check the data got renamed */
    r = conversations_get_data(&state, C_CID1, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NULL(conv);

    conv = NULL;
    r = conversations_get_data(&state, C_CID2, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(conv);
    CU_ASSERT_EQUAL(conv->modseq, 8);
    CU_ASSERT_EQUAL(num_folders(conv), 3);
    CU_ASSERT(find_folder(conv, FOLDER1));
    CU_ASSERT(find_folder(conv, FOLDER2));
    CU_ASSERT(find_folder(conv, FOLDER3));
    conversation_free(conv);
    conv = NULL;

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID1, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID2, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    memset(&cid, 0x45, sizeof(cid));
    r = conversations_get_msgid(&state, C_MSGID3, &cid);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_EQUAL(cid, C_CID2);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

static void test_folders(void)
{
    int r;
    struct conversations_state state;
    static const char FOLDER1[] = "foobar.com!user.smurf";
    static const char FOLDER2[] = "foobar.com!user.smurf.foo bar";
    static const char FOLDER3[] = "foobar.com!user.smurf.quux.foonly";
    static const conversation_id_t C_CID = 0x10abcdef23456789;
    conversation_t *conv;
    conv_folder_t *folder;

    memset(&state, 0, sizeof(state));

    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* Database is empty, so get should succeed and report no results */
    conv = NULL;
    r = conversations_get_data(&state, C_CID, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NULL(conv);

    /* add should succeed */
    conv = conversation_new();
    CU_ASSERT_PTR_NOT_NULL(conv);
    conv->modseq = 4;

    folder = NULL;
    conversation_add_folder(conv, FOLDER1, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 4;

    r = conversations_set_data(&state, C_CID, conv);
    CU_ASSERT_EQUAL(r, 0);
    conversation_free(conv);
    conv = NULL;

    /* get should now succeed and report the value we gave it */
    conv = NULL;
    r = conversations_get_data(&state, C_CID, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(conv);
    CU_ASSERT_EQUAL(conv->modseq, 4);
    CU_ASSERT_EQUAL(num_folders(conv), 1);
    CU_ASSERT(find_folder(conv, FOLDER1));

    /* some more adds should succeed */
    folder = NULL;
    conversation_add_folder(conv, FOLDER2, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 7;

    folder = NULL;
    conversation_add_folder(conv, FOLDER3, &folder);
    CU_ASSERT_PTR_NOT_NULL(folder);
    folder->modseq = 55;

    conv->modseq = 55;

    r = conversations_set_data(&state, C_CID, conv);
    CU_ASSERT_EQUAL(r, 0);
    conversation_free(conv);
    conv = NULL;

    /* get should now succeed and report all values we gave it */
    conv = NULL;
    r = conversations_get_data(&state, C_CID, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(conv);
    CU_ASSERT_EQUAL(conv->modseq, 55);
    CU_ASSERT_EQUAL(num_folders(conv), 3);
    CU_ASSERT(find_folder(conv, FOLDER1));
    CU_ASSERT(find_folder(conv, FOLDER2));
    CU_ASSERT(find_folder(conv, FOLDER3));
    conversation_free(conv);
    conv = NULL;

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* open the db again */
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    /* get should still succeed and report all values we gave it */
    conv = NULL;
    r = conversations_get_data(&state, C_CID, &conv);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NOT_NULL(conv);
    CU_ASSERT_EQUAL(conv->modseq, 55);
    CU_ASSERT_EQUAL(num_folders(conv), 3);
    CU_ASSERT(find_folder(conv, FOLDER1));
    CU_ASSERT(find_folder(conv, FOLDER2));
    CU_ASSERT(find_folder(conv, FOLDER3));
    conversation_free(conv);
    conv = NULL;

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);
}

static void gen_msgid_cid(int i, char *msgid, int msgidlen,
			  conversation_id_t *cidp)
{
    static const char * const domains[] = {
	"fastmail.fm",
	"example.com",
	"gmail.com",
	"yahoo.com",
	"hotmail.com"
    };
    snprintf(msgid, msgidlen, "<%04d.1298269537@%s>",
	    i, domains[i % VECTOR_SIZE(domains)]);

    *cidp = 0xfeeddeadbeef0000ULL | (unsigned int)i;
}

static void gen_cid_folder(int i, conversation_id_t *cidp,
			   strarray_t *mboxnames)
{
    int n;
    int j;
    static const char * const folders[] = {
	"user.foo.INBOX",
	"user.foo.Manilla",
	"user.foo.VanillaGorilla",
	"user.foo.SarsparillaGorilla"
    };

    *cidp = 0xfeeddeadbeef0000ULL | (unsigned int)i;

    strarray_truncate(mboxnames, 0);
    n = 1 + (17 - i) % (VECTOR_SIZE(folders)-1);
    CU_ASSERT(n > 0);
    for (j = 0 ; j < n ; j++)
	strarray_append(mboxnames,
			folders[(j + i/2) % VECTOR_SIZE(folders)]);
}

static void test_dump(void)
{
    int r;
    struct conversations_state state;
    int fd;
    FILE *fp;
    char filename[64];
    char msgid[40];
    strarray_t mboxnames = STRARRAY_INITIALIZER;
    conversation_id_t cid, cid2;
    conversation_t *conv;
    conv_folder_t *folder;
    int i;
    int j;
#define N_MSGID_TO_CID	500
#define N_CID_TO_FOLDER	333
    struct stat sb;

    strcpy(filename, "/tmp/cyrus-conv.datXXXXXX");
    fd = mkstemp(filename);
    CU_ASSERT_FATAL(fd >= 0);
    fp = fdopen(fd, "r+");
    CU_ASSERT_PTR_NOT_NULL_FATAL(fp);

    memset(&state, 0, sizeof(state));

    /* generate some data in the database */
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    for (i = 0 ; i < N_MSGID_TO_CID ; i++) {
	gen_msgid_cid(i, msgid, sizeof(msgid), &cid);
	r = conversations_set_msgid(&state, msgid, cid);
	CU_ASSERT_EQUAL(r, 0);
    }
    for (i = 0 ; i < N_CID_TO_FOLDER ; i++) {
	gen_cid_folder(i, &cid, &mboxnames);
	conv = conversation_new();
	CU_ASSERT_PTR_NOT_NULL(conv);
	conv->modseq = 100;
	for (j = 0 ; j < mboxnames.count ; j++) {
	    folder = NULL;
	    conversation_add_folder(conv, mboxnames.data[j], &folder);
	    CU_ASSERT_PTR_NOT_NULL(folder);
	    folder->modseq = 100;


	}
	r = conversations_set_data(&state, cid, conv);
	CU_ASSERT_EQUAL(r, 0);
	conversation_free(conv);
	conv = NULL;
    }

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* open and dump the database */
    memset(&state, 0, sizeof(state));
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    conversations_dump(&state, fp);

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* do some basic checks on the output file */
    fflush(fp);

    r = fstat(fd, &sb);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT(sb.st_size > 40*N_MSGID_TO_CID + 40*N_CID_TO_FOLDER);

    r = (int)fseek(fp, 0L, SEEK_SET);
    CU_ASSERT_EQUAL(r, 0);

    /* open and truncate the database */
    memset(&state, 0, sizeof(state));
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_truncate(&state);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* check we can no longer find any of the data */
    memset(&state, 0, sizeof(state));
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    for (i = 0 ; i < N_MSGID_TO_CID ; i++) {
	gen_msgid_cid(i, msgid, sizeof(msgid), &cid);
	r = conversations_get_msgid(&state, msgid, &cid2);
	CU_ASSERT_EQUAL(r, 0);
	CU_ASSERT_EQUAL(cid2, NULLCONVERSATION);
    }
    for (i = 0 ; i < N_CID_TO_FOLDER ; i++) {
	gen_cid_folder(i, &cid, &mboxnames);
	conv = NULL;
	r = conversations_get_data(&state, cid, &conv);
	CU_ASSERT_EQUAL(r, 0);
	CU_ASSERT_PTR_NULL(conv);
    }

    /* now undump */
    r = conversations_undump(&state, fp);
    CU_ASSERT_EQUAL(r, 0);

    r = conversations_commit(&state);
    CU_ASSERT_EQUAL(r, 0);
    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    /* finally check that we got all the data back */
    memset(&state, 0, sizeof(state));
    r = conversations_open(&state, DBNAME);
    CU_ASSERT_EQUAL(r, 0);

    for (i = 0 ; i < N_MSGID_TO_CID ; i++) {
	gen_msgid_cid(i, msgid, sizeof(msgid), &cid);
	r = conversations_get_msgid(&state, msgid, &cid2);
	CU_ASSERT_EQUAL(r, 0);
	CU_ASSERT_EQUAL(cid, cid2);
    }
    for (i = 0 ; i < N_CID_TO_FOLDER ; i++) {
	gen_cid_folder(i, &cid, &mboxnames);
	conv = NULL;
	r = conversations_get_data(&state, cid, &conv);
	CU_ASSERT_EQUAL(r, 0);
	CU_ASSERT_PTR_NOT_NULL(conv);
	CU_ASSERT_EQUAL(conv->modseq, 100);
	CU_ASSERT_EQUAL(mboxnames.count, num_folders(conv));
	for (j = 0 ; j < mboxnames.count ; j++)
	    CU_ASSERT(find_folder(conv, mboxnames.data[j]));
	conversation_free(conv);
	conv = NULL;
    }

    r = conversations_close(&state);
    CU_ASSERT_EQUAL(r, 0);

    fclose(fp);
    unlink(filename);
    strarray_fini(&mboxnames);
#undef N_MSGID_TO_CID
#undef N_CID_TO_FOLDER
}


static int set_up(void)
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

static int tear_down(void)
{
    int r;

    cyrusdb_done();
    config_conversations_db = NULL;

    r = system("rm -rf " DBDIR);
    /* I'm ignoring you */

    return 0;
}
