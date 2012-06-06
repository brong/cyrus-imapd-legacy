#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <fcntl.h>
#include <ctype.h>
#include <time.h>
#include <syslog.h>
#include <com_err.h>
#include <config.h>

#include "global.h"
#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "mailbox.h"
#include "imap_err.h"
#include "sieve_interface.h"
#include "script.h"

#define TIMSIEVE_FAIL 	-1
#define TIMSIEVE_OK 	0
#define MAX_FILENAME	1024

static int get_script_name(char *sievename, size_t buflen, const char *filename);
static int get_script_dir(char *sieve_script_dir, size_t buflen, char *userid, const char *sieve_dir);
int autoadd_sieve(char *userid, const char *source_script);

//static void fatal(const char *s, int code);
static void foo(void);
static int sieve_notify(void *ac __attribute__((unused)),
                        void *interp_context __attribute__((unused)),
                        void *script_context __attribute__((unused)),
                        void *message_context __attribute__((unused)),
                        const char **errmsg __attribute__((unused)));
static int mysieve_error(int lineno, const char *msg,
                  void *i __attribute__((unused)), void *s);
static int is_script_parsable(FILE *stream, char **errstr, sieve_script_t **ret);


sieve_vacation_t vacation2 = {
    0,                          /* min response */
    0,                          /* max response */
    (sieve_callback *) &foo,    /* autorespond() */
    (sieve_callback *) &foo     /* send_response() */
};


/*
 * Find the name of the sieve script
 * given the source script and compiled script names
 */
static int get_script_name(char *sievename, size_t buflen, const char *filename)
{
  char *p;
  int r;

  p = strrchr(filename, '/');
  if (p == NULL)
      p = (char *) filename;
  else
      p++;

  r = strlcpy(sievename, p, buflen) - buflen;
  return (r >= 0 || r == -buflen ? 1 : 0);
}


/*
 * Find the directory where the sieve scripts of the user
 * reside
 */
static int get_script_dir(char *sieve_script_dir, size_t buflen, char *userid, const char *sieve_dir)
{
    char *user = NULL, *domain = NULL;

    /* Setup the user and the domain */
    if(config_virtdomains && (domain = strchr(userid, '@'))) {
        user = (char *) xmalloc((domain - userid +1) * sizeof(char));
        strlcpy(user, userid, domain - userid + 1);
        domain++;
    } else
        user = userid;

    /*  Find the dir path where the sieve scripts of the user will reside */   
    if (config_virtdomains && domain) {
         if(snprintf(sieve_script_dir, buflen, "%s%s%c/%s/%c/%s/",
              sieve_dir, FNAME_DOMAINDIR, dir_hash_c(domain, config_fulldirhash), domain, dir_hash_c(user,config_fulldirhash), user) >= buflen) {
                 free(user);
                 return 1;
 	 }
    } else {
         if(snprintf(sieve_script_dir, buflen, "%s/%c/%s/", 
     	      sieve_dir, dir_hash_c(user,config_fulldirhash), user) >= buflen) 
                 return 1;
    }

    /* Free the xmalloced user memory, reserved above */
    if(user != userid)
        free(user);

    return 0;
}

int autoadd_sieve(char *userid, const char *source_script)
{   
    sieve_script_t *s = NULL;
    bytecode_info_t *bc = NULL;
    char *err = NULL;
    FILE *in_stream, *out_fp;
    int out_fd, in_fd, r, k;
    int do_compile = 0;
    const char *sieve_dir = NULL;
    const char *compiled_source_script = NULL;
    char sievename[MAX_FILENAME];
    char sieve_script_name[MAX_FILENAME];
    char sieve_script_dir[MAX_FILENAME];
    char sieve_bcscript_name[MAX_FILENAME];
    char sieve_default[MAX_FILENAME];
    char sieve_tmpname[MAX_FILENAME];
    char sieve_bctmpname[MAX_FILENAME];
    char sieve_bclink_name[MAX_FILENAME];
    char buf[4096];
    mode_t oldmask;
    struct stat statbuf;

    /* We don't support using the homedirectory, like timsieved */
    if (config_getswitch(IMAPOPT_SIEVEUSEHOMEDIR)) {
        syslog(LOG_WARNING,"autocreate_sieve: autocreate_sieve does not work with sieveusehomedir option in imapd.conf");
        return 1;
    }

    /* Check if sievedir is defined in imapd.conf */
    if(!(sieve_dir = config_getstring(IMAPOPT_SIEVEDIR))) { 
        syslog(LOG_WARNING, "autocreate_sieve: sievedir option is not defined. Check imapd.conf");
        return 1;
    }

    /* Check if autocreate_sieve_compiledscript is defined in imapd.conf */
    if(!(compiled_source_script  = config_getstring(IMAPOPT_AUTOCREATE_SIEVE_COMPILEDSCRIPT))) {
        syslog(LOG_WARNING, "autocreate_sieve: autocreate_sieve_compiledscript option is not defined. Compiling it");
        do_compile = 1;
    }

    if(get_script_dir(sieve_script_dir, sizeof(sieve_script_dir), userid, sieve_dir)) {
        syslog(LOG_WARNING, "autocreate_sieve: Cannot find sieve scripts directory");
        return 1;
    }

    if (get_script_name(sievename, sizeof(sievename), source_script)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve script %s", source_script);
        return 1;
    }

    if(snprintf(sieve_tmpname, sizeof(sieve_tmpname), "%s%s.script.NEW",sieve_script_dir, sievename) >= sizeof(sieve_tmpname)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }
    if(snprintf(sieve_bctmpname, sizeof(sieve_bctmpname), "%s%s.bc.NEW",sieve_script_dir, sievename) >= sizeof(sieve_bctmpname)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }    
    if(snprintf(sieve_script_name, sizeof(sieve_script_name), "%s%s.script",sieve_script_dir, sievename) >= sizeof(sieve_script_name)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }
    if(snprintf(sieve_bcscript_name, sizeof(sieve_bcscript_name), "%s%s.bc",sieve_script_dir, sievename) >= sizeof(sieve_bcscript_name)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }
    if(snprintf(sieve_default, sizeof(sieve_default), "%s%s",sieve_script_dir,"defaultbc") >= sizeof(sieve_default)) {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }
    if(snprintf(sieve_bclink_name, sizeof(sieve_bclink_name), "%s.bc", sievename) >= sizeof(sieve_bclink_name))  {
        syslog(LOG_WARNING, "autocreate_sieve: Invalid sieve path %s, %s, %s", sieve_dir, sievename, userid);
        return 1;
    }

    /* Check if a default sieve filter alrady exists */
    if(!stat(sieve_default,&statbuf)) {
        syslog(LOG_WARNING,"autocreate_sieve: Default sieve script already exists");
        fclose(in_stream);
        return 1;
    }

    /* Open the source script. if there is a problem with that exit */
    in_stream = fopen(source_script, "r");
    if(!in_stream) {
        syslog(LOG_WARNING,"autocreate_sieve: Unable to open sieve script %s. Check permissions",source_script);
        return 1;
    }
    
    
    /* 
     * At this point we start the modifications of the filesystem 
     */

    /* Create the directory where the sieve scripts will reside */
    r = cyrus_mkdir(sieve_script_dir, 0755);
    if(r == -1) {
        /* If this fails we just leave */
        syslog(LOG_WARNING,"autocreate_sieve: Unable to create directory %s. Check permissions",sieve_script_name);
        return 1;
    }

    /*
     * We open the file that will be used as the bc file. If this file exists, overwrite it 
     * since something bad has happened. We open the file here so that this error checking is
     * done before we try to open the rest of the files to start copying etc. 
     */
    out_fd = open(sieve_bctmpname, O_CREAT|O_TRUNC|O_WRONLY, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
    if(out_fd < 0) {
        if(errno == EEXIST) {
            syslog(LOG_WARNING,"autocreate_sieve: File %s already exists. Probaly left over. Ignoring",sieve_bctmpname);
        } else if (errno == EACCES) {
            syslog(LOG_WARNING,"autocreate_sieve: No access to create file %s. Check permissions",sieve_bctmpname);
            fclose(in_stream);
            return 1;
        } else {
            syslog(LOG_WARNING,"autocreate_sieve: Unable to create %s. Unknown error",sieve_bctmpname);
            fclose(in_stream);
            return 1;
        }
    }

    if(!do_compile && compiled_source_script && (in_fd = open(compiled_source_script, O_RDONLY)) != -1) {
        while((r = read(in_fd, buf, sizeof(buf))) > 0) {
            if((k=write(out_fd, buf,r)) < 0) {
                syslog(LOG_WARNING, "autocreate_sieve: Error writing to file: %s, error: %d", sieve_bctmpname, errno);
                close(out_fd);
                close(in_fd);
                fclose(in_stream);
                unlink(sieve_bctmpname);
                return 1;
           }
        } 

        if(r == 0) { /* EOF */
            close(out_fd);
            close(in_fd);
        } else if (r < 0) {
            syslog(LOG_WARNING, "autocreate_sieve: Error reading compiled script file: %s. Will try to compile it", 
                           compiled_source_script);
            close(in_fd);
            do_compile = 1;
            if(lseek(out_fd, 0, SEEK_SET)) {
                syslog(LOG_WARNING, "autocreate_sieve: Major IO problem. Aborting");
                return 1;
            }
        }
        close(in_fd);
    } else {
        if(compiled_source_script)
              syslog(LOG_WARNING,"autocreate_sieve: Problem opening compiled script file: %s. Compiling it", compiled_source_script);
        do_compile = 1;
    }


    /* Because we failed to open a precompiled bc sieve script, we compile one */
    if(do_compile) {
       if(is_script_parsable(in_stream,&err, &s) == TIMSIEVE_FAIL) {
            if(err && *err) {
               syslog(LOG_WARNING,"autocreate_sieve: Error while parsing script %s.",err);
               free(err);
            } else
                syslog(LOG_WARNING,"autocreate_sieve: Error while parsing script");
    
            unlink(sieve_bctmpname);
            fclose(in_stream);
            close(out_fd);
            return 1;
        }

        /* generate the bytecode */
        if(sieve_generate_bytecode(&bc, s) == TIMSIEVE_FAIL) {
            syslog(LOG_WARNING,"autocreate_sieve: problem compiling sieve script");
            /* removing the copied script and cleaning up memory */
            unlink(sieve_bctmpname);
            sieve_script_free(&s);
            fclose(in_stream);
            close(out_fd);
            return 1;
        }

        if(sieve_emit_bytecode(out_fd, bc) == TIMSIEVE_FAIL) {
            syslog(LOG_WARNING,"autocreate_sieve: problem emiting sieve script");
            /* removing the copied script and cleaning up memory */
            unlink(sieve_bctmpname);
            sieve_free_bytecode(&bc);
            sieve_script_free(&s);
            fclose(in_stream);
            close(out_fd);
            return 1;
        }

        /* clean up the memory */
        sieve_free_bytecode(&bc);
        sieve_script_free(&s);
    }

    close(out_fd);
    rewind(in_stream);

    /* Copy the initial script */
    oldmask = umask(077);
    if((out_fp = fopen(sieve_tmpname, "w")) == NULL) {
        syslog(LOG_WARNING,"autocreate_sieve: Unable to open %s destination sieve script", sieve_tmpname);
        unlink(sieve_bctmpname);
        umask(oldmask);
        fclose(in_stream);
        return 1;
    }
    umask(oldmask);

    while((r = fread(buf,sizeof(char), sizeof(buf), in_stream))) {
        if( fwrite(buf,sizeof(char), r, out_fp) != r) {
            syslog(LOG_WARNING,"autocreate_sieve: Problem writing to sieve script file: %s",sieve_tmpname);
            fclose(out_fp);
            unlink(sieve_tmpname);
            unlink(sieve_bctmpname);
            fclose(in_stream);
            return 1;
        }
    }
    
    if(feof(in_stream)) {
        fclose(out_fp);
    } else { /* ferror */
        fclose(out_fp);
        unlink(sieve_tmpname);
        unlink(sieve_bctmpname);
        fclose(in_stream);
        return 1;
    }

    /* Renaming the necessary stuff */
    if(rename(sieve_tmpname, sieve_script_name)) {
        unlink(sieve_tmpname);
        unlink(sieve_bctmpname);
        return 1;
    }

    if(rename(sieve_bctmpname, sieve_bcscript_name)) {
        unlink(sieve_bctmpname);
        unlink(sieve_bcscript_name);
        return 1;
    }

    /* end now with the symlink */
    if(symlink(sieve_bclink_name, sieve_default)) {
        if(errno != EEXIST) {
            syslog(LOG_WARNING, "autocreate_sieve: problem making the default link.");
            /* Lets delete the files */
            unlink(sieve_script_name);
            unlink(sieve_bcscript_name);
        }
    }

    /* 
     * If everything has succeeded AND we have compiled the script AND we have requested
     * to generate the global script so that it is not compiled each time then we create it.
     */
    if(do_compile && 
          config_getswitch(IMAPOPT_GENERATE_COMPILED_SIEVE_SCRIPT)) {

        if(!compiled_source_script) {
            syslog(LOG_WARNING, "autocreate_sieve: To save a compiled sieve script, autocreate_sieve_compiledscript must have been defined in imapd.conf");
            return 0;
        }

        if(snprintf(sieve_tmpname, sizeof(sieve_tmpname), "%s.NEW", compiled_source_script) >= sizeof(sieve_tmpname))
            return 0;

        /*
         * Copy everything from the newly created bc sieve sieve script.
         */
        if((in_fd = open(sieve_bcscript_name, O_RDONLY))<0) {
            return 0;
        }

        if((out_fd = open(sieve_tmpname, O_CREAT|O_EXCL|O_WRONLY, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH)) < 0) {
            if(errno == EEXIST) {
               /* Someone is already doing this so just bail out. */
               syslog(LOG_WARNING, "autocreate_sieve: %s already exists. Some other instance processing it, or it is left over", sieve_tmpname);
                close(in_fd);
                return 0; 
            } else if (errno == EACCES) {
                syslog(LOG_WARNING,"autocreate_sieve: No access to create file %s. Check permissions",sieve_tmpname);
                close(in_fd);
                return 0;
            } else {
                syslog(LOG_WARNING,"autocreate_sieve: Unable to create %s",sieve_tmpname);
                close(in_fd);
                return 0;
            }
        }

        while((r = read(in_fd, buf, sizeof(buf))) > 0) {
            if((k = write(out_fd,buf,r)) < 0) {
                syslog(LOG_WARNING, "autocreate_sieve: Error writing to file: %s, error: %d", sieve_tmpname, errno);
                close(out_fd);
                close(in_fd);
                unlink(sieve_tmpname);
                return 0;
           }
        }

        if(r == 0 ) { /*EOF */
            close(out_fd);
            close(in_fd);
        } else if (r < 0) {
                syslog(LOG_WARNING, "autocreate_sieve: Error writing to file: %s, error: %d", sieve_tmpname, errno);
                close(out_fd);
                close(in_fd);
                unlink(sieve_tmpname);
                return 0;
        }

        /* Rename the temporary created sieve script to its final name. */
        if(rename(sieve_tmpname, compiled_source_script)) {
            if(errno != EEXIST) {
               unlink(sieve_tmpname);
               unlink(compiled_source_script);
        }
            return 0;
        }

        syslog(LOG_NOTICE, "autocreate_sieve: Compiled sieve script was successfully saved in %s", compiled_source_script);
    }

    return 0;
}

/*static void fatal(const char *s, int code)
{   
    printf("Fatal error: %s (%d)\r\n", s, code);
    exit(1);
}*/

/* to make larry's stupid functions happy :) */
static void foo(void)
{
    fatal("stub function called", 0);
}

static int sieve_notify(void *ac __attribute__((unused)),
                        void *interp_context __attribute__((unused)),
                        void *script_context __attribute__((unused)),
                        void *message_context __attribute__((unused)),
                        const char **errmsg __attribute__((unused)))
{
    fatal("stub function called", 0);
    return SIEVE_FAIL;
}

static int mysieve_error(int lineno, const char *msg,
                  void *i __attribute__((unused)), void *s)
{
    char buf[1024];
    char **errstr = (char **) s;

    snprintf(buf, 80, "line %d: %s\r\n", lineno, msg);
    *errstr = (char *) xrealloc(*errstr, strlen(*errstr) + strlen(buf) + 30);
    syslog(LOG_DEBUG, "%s", buf);
    strcat(*errstr, buf);

    return SIEVE_OK;
}

/* end the boilerplate */

/* returns TRUE or FALSE */
int is_script_parsable(FILE *stream, char **errstr, sieve_script_t **ret)
{
    sieve_interp_t *i;
    sieve_script_t *s;
    int res;

    res = sieve_interp_alloc(&i, NULL);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_interp_alloc() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_redirect(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_redirect() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_discard(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_discard() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_reject(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_reject() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_fileinto(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_fileinto() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_keep(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_keep() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_imapflags(i, NULL);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_imapflags() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_size(i, (sieve_get_size *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_size() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_header(i, (sieve_get_header *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_header() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_envelope(i, (sieve_get_envelope *) &foo);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_envelope() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_vacation(i, &vacation2);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_vacation() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_notify(i, &sieve_notify);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_notify() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_parse_error(i, &mysieve_error);
    if (res != SIEVE_OK) {
        syslog(LOG_WARNING, "sieve_register_parse_error() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    rewind(stream);

    *errstr = (char *) xmalloc(20 * sizeof(char));
    strcpy(*errstr, "script errors:\r\n");

    res = sieve_script_parse(i, stream, errstr, &s);

    if (res == SIEVE_OK) {
        if(ret) {
            *ret = s;
        } else {
            sieve_script_free(&s);
        }
        free(*errstr);
        *errstr = NULL;
    }

    /* free interpreter */
    sieve_interp_free(&i);

    return (res == SIEVE_OK) ? TIMSIEVE_OK : TIMSIEVE_FAIL;
}

/*
 * Btw the initial date of this patch is Sep, 02 2004 which is the birthday of
 * Pavlos. Author of cyrusmaster. So consider this patch as his birthday present
 */

