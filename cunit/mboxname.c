#if HAVE_CONFIG_H
#include <config.h>
#endif
#include <assert.h>
#include "cunit/cunit.h"
#include "libconfig.h"
#include "mboxname.h"
#include "global.h"

static void test_to_parts(void)
{
    static const char FRED_DRAFTS[] = "user.fred.Drafts";
    static const char JANEAT_SENT[] = "bloggs.com!user.jane.Sent";
    static const char SHARED[] = "shared.Gossip";
    static const char SHAREDAT[] = "foonly.com!shared.Tattle";
    struct mboxname_parts parts;
    int r;

    r = mboxname_to_parts(FRED_DRAFTS, &parts);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NULL(parts.domain);
    CU_ASSERT_STRING_EQUAL(parts.userid, "fred");
    CU_ASSERT_STRING_EQUAL(parts.box, "Drafts");
    mboxname_free_parts(&parts);

    r = mboxname_to_parts(JANEAT_SENT, &parts);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(parts.domain, "bloggs.com");
    CU_ASSERT_STRING_EQUAL(parts.userid, "jane");
    CU_ASSERT_STRING_EQUAL(parts.box, "Sent");
    mboxname_free_parts(&parts);

    r = mboxname_to_parts(SHARED, &parts);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_PTR_NULL(parts.domain);
    CU_ASSERT_PTR_NULL(parts.userid);
    CU_ASSERT_STRING_EQUAL(parts.box, "shared.Gossip");
    mboxname_free_parts(&parts);

    r = mboxname_to_parts(SHAREDAT, &parts);
    CU_ASSERT_EQUAL(r, 0);
    CU_ASSERT_STRING_EQUAL(parts.domain, "foonly.com");
    CU_ASSERT_PTR_NULL(parts.userid);
    CU_ASSERT_STRING_EQUAL(parts.box, "shared.Tattle");
    mboxname_free_parts(&parts);
}

static void test_to_userid(void)
{
    static const char SAM_DRAFTS[] = "user.sam.Drafts";
    static const char BETTYAT_SENT[] = "boop.com!user.betty.Sent";
    static const char SHARED[] = "shared.Gossip";
    static const char SHAREDAT[] = "foonly.com!shared.Tattle";
    const char *r;

    r = mboxname_to_userid(SAM_DRAFTS);
    CU_ASSERT_STRING_EQUAL(r, "sam");

    r = mboxname_to_userid(BETTYAT_SENT);
    CU_ASSERT_STRING_EQUAL(r, "betty@boop.com");

    r = mboxname_to_userid(SHARED);
    CU_ASSERT_PTR_NULL(r);

    r = mboxname_to_userid(SHAREDAT);
    CU_ASSERT_PTR_NULL(r);
}

static void test_to_inbox(void)
{
    const char *r;

    r = mboxname_user_inbox("sam");
    CU_ASSERT_STRING_EQUAL(r, "user.sam");

    r = mboxname_user_inbox("betty@boop.com");
    CU_ASSERT_STRING_EQUAL(r, "boop.com!user.betty");

    r = mboxname_user_inbox(NULL);
    CU_ASSERT_PTR_NULL(r);
}


static void test_same_userid(void)
{
    static const char FRED_DRAFTS[] = "user.fred.Drafts";
    static const char FRED_SENT[] = "user.fred.Sent";
    static const char JANE_SENT[] = "user.jane.Sent";

    CU_ASSERT_EQUAL(mboxname_same_userid(FRED_DRAFTS, FRED_SENT), 1);
    CU_ASSERT_EQUAL(mboxname_same_userid(JANE_SENT, FRED_SENT), 0);
}

static void test_same_userid_domain(void)
{
    static const char FREDAT_DRAFTS[] = "bloggs.com!user.fred.Drafts";
    static const char FREDAT_SENT[] = "bloggs.com!user.fred.Sent";
    static const char JANEAT_SENT[] = "bloggs.com!user.jane.Sent";
    static const char JANE_SENT[] = "user.jane.Sent";

    CU_ASSERT_EQUAL(mboxname_same_userid(FREDAT_DRAFTS, FREDAT_SENT), 1);
    CU_ASSERT_EQUAL(mboxname_same_userid(JANEAT_SENT, FREDAT_SENT), 0);
    CU_ASSERT_EQUAL(mboxname_same_userid(JANE_SENT, FREDAT_SENT), 0);
    CU_ASSERT_EQUAL(mboxname_same_userid(JANE_SENT, JANEAT_SENT), 0);
}

static void test_nextmodseq(void)
{
    static const char FREDNAME[] = "bloggs.com!user.fred";
    struct mboxname_parts parts;
    char *fname;

    /* ensure there is no file */
    mboxname_to_parts(FREDNAME, &parts);
    fname = mboxname_conf_getpath(&parts, "modseq");
    unlink(fname);
    free(fname);
    mboxname_free_parts(&parts);

    /* initial value should be 1 without file */
    CU_ASSERT_EQUAL(mboxname_nextmodseq(FREDNAME, 0), 1);
    /* next value should always increment */
    CU_ASSERT_EQUAL(mboxname_nextmodseq(FREDNAME, 0), 2);
    /* higher value should force a jump */
    CU_ASSERT_EQUAL(mboxname_nextmodseq(FREDNAME, 100), 101);
    /* lower value should not decrease */
    CU_ASSERT_EQUAL(mboxname_nextmodseq(FREDNAME, 5), 102);
}

static enum enum_value old_config_virtdomains;
static char *old_config_dir;

static int set_up(void)
{
    char cwd[PATH_MAX];
    char *s;

    /*
     * TODO: this is pretty hacky.  There should be some
     * cleaner way of pushing aside the config for a moment
     * and temporarily setting up a particular set of config
     * options for testing.
     */
    old_config_virtdomains = config_virtdomains;
    config_virtdomains = IMAP_ENUM_VIRTDOMAINS_ON;

    old_config_dir = (char *)config_dir;
    s = getcwd(cwd, sizeof(cwd));
    assert(s);
    config_dir = strconcat(cwd, "/conf.d", (char *)NULL);

    return 0;
}

static int tear_down(void)
{
    char *cmd;
    int r;

    cmd = strconcat("rm -rf \"", config_dir, "\"", (char *)NULL);
    r = system(cmd);
    assert(!r);
    free(cmd);
    free((char *)config_dir);
    config_dir = old_config_dir;

    config_virtdomains = old_config_virtdomains;

    return 0;
}

