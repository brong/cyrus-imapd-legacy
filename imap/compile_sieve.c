/* This tool compiles the sieve script from a command
line so that it can be used wby the autoadd patch */
#include <stdio.h>
#include <stdlib.h>

#include <config.h>
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
#include <com_err.h>

#include "global.h"

#include "util.h"
#include "xmalloc.h"
#include "xstrlcpy.h"
#include "xstrlcat.h"
#include "mailbox.h"
#include "imap_err.h"
#include "sieve_interface.h"
#include "script.h"

#include <pwd.h>

#define TIMSIEVE_FAIL 		-1
#define TIMSIEVE_OK 		0
#define MAX_FILENAME_SIZE	100

/* Needed by libconfig */
const int config_need_data = 0;

static int is_script_parsable(FILE *stream, char **errstr, sieve_script_t **ret);

/*static void fatal(const char *s, int code)
{   
    printf("Fatal error: %s (%d)\r\n", s, code);

    exit(1);
}*/

void usage(void)
{
    fprintf(stderr,
            "Usage:\n\tcompile_sieve [-C <altconfig>] [-i <infile> -o <outfile>]\n");
    exit(-1);
}


int main (int argc, char **argv)
{   

    sieve_script_t *s = NULL;
    bytecode_info_t *bc = NULL;
    char *err = NULL;
    FILE *in_stream;
    int  out_fd, opt;
    char *source_script = NULL;
    char *compiled_source_script = NULL;
    char *alt_config = NULL;
    extern char *optarg;
    char sieve_tmpname[MAX_MAILBOX_NAME+1];

    if (geteuid() == 0) fatal("must run as the Cyrus user", EC_USAGE);

    while((opt = getopt(argc, argv, "C:i:o:")) != EOF) {
        switch (opt) {
            case 'C': /* alt config file */
	        alt_config =  optarg;
	        break;
	    case 'i': /* input script file */
		source_script = optarg;
		break;
	    case 'o': /* output script file */
		compiled_source_script = optarg;
		break;
	    default:
	        usage();
		break;
	}
    }

    if(source_script && !compiled_source_script) {
	    fprintf(stderr, "No output file was defined\n");
	    usage();
    } else if (!source_script && compiled_source_script) {
	    fprintf(stderr, "No input file was defined\n");
	    usage();
    }	

    /*
     * If no <infile> has been defined, then read them from
     * the configuration file.
     */
    if (!source_script && !compiled_source_script) { 
	    cyrus_init(alt_config, "compile_sieve", 0);

	    /* Initially check if we want to have the sieve script created */
	    if(!(source_script = (char *) config_getstring(IMAPOPT_AUTOCREATE_SIEVE_SCRIPT))) {
        	fprintf(stderr,"autocreate_sieve_script option not defined. Check imapd.conf\n");
	        return 1;
	    }

	    /* Check if we have an already compiled sieve script*/
	    if(!(compiled_source_script = (char *) config_getstring(IMAPOPT_AUTOCREATE_SIEVE_COMPILEDSCRIPT))) {
	        fprintf(stderr, "autocreate_sieve_compiledscript option not defined. Check imapd.conf\n");
		return 1;
	    }

	    if(!strrchr(source_script,'/') || !strrchr(compiled_source_script,'/')) {
       		/* 
		 * At this point the only think that is inconsistent is the directory 
		 * that was created. But if the user will have any sieve scripts then 
		 * they will eventually go there, so no big deal 
		 */
	        fprintf(stderr, 
			"In imapd.conf the full path of the filenames must be defined\n");
	       	return 1;
	    }
    }

    printf("input file : %s, output file : %s\n", source_script, compiled_source_script);


    if(strlen(compiled_source_script) + sizeof(".NEW") + 1 > sizeof(sieve_tmpname)) {
	    fprintf(stderr, "Filename %s is too big\n", compiled_source_script);
	    return 1;
    }
    	
    snprintf(sieve_tmpname, sizeof(sieve_tmpname), "%s.NEW", compiled_source_script);

    in_stream = fopen(source_script,"r");

    if(!in_stream) {
        fprintf(stderr,"Unable to open %s source sieve script\n",source_script);
        return 1; 
    }

    /* 
     * We open the file that will be used as the bc file. If this file exists, overwrite it 
     * since something bad has happened. We open the file here so that this error checking is
     * done before we try to open the rest of the files to start copying etc. 
     */
    out_fd = open(sieve_tmpname, O_CREAT|O_EXCL|O_WRONLY, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
    if(out_fd < 0) {
        if(errno == EEXIST) {
            fprintf(stderr, "File %s already exists\n", sieve_tmpname);
        } else if (errno == EACCES) {
            fprintf(stderr,"No access to create file %s. Please check that you have the correct permissions\n",
			    sieve_tmpname);
        } else {
            fprintf(stderr,"Unable to create %s. Please check that you have the correct permissions\n", 
			    sieve_tmpname);
        }
	
	fclose(in_stream);
	return 1;
    }

    if(is_script_parsable(in_stream,&err, &s) == TIMSIEVE_FAIL) {
        if(err && *err) {
           fprintf(stderr, "Error while parsing script %s\n",err);
           free(err);
        }
        else
            fprintf(stderr,"Error while parsing script\n");
            unlink(sieve_tmpname);
	    fclose(in_stream);
	    close(out_fd);
        return 1;
   }


    /* generate the bytecode */
    if(sieve_generate_bytecode(&bc,s) == TIMSIEVE_FAIL) {
        fprintf(stderr,"Error occured while compiling sieve script\n");
        /* removing the copied script and cleaning up memory */
        unlink(sieve_tmpname);
        sieve_script_free(&s);
        fclose(in_stream);
        close(out_fd);
        return 1;
    }
    if(sieve_emit_bytecode(out_fd,bc) == TIMSIEVE_FAIL) {
        fprintf(stderr, "Error occured while emitting sieve script\n");
        unlink(sieve_tmpname);
        sieve_free_bytecode(&bc);
        sieve_script_free(&s);
        fclose(in_stream);
        close(out_fd);
        return 1;
    }

    /* clean up the memory */
    sieve_free_bytecode(&bc);
    sieve_script_free(&s);

    close(out_fd);

    if(rename(sieve_tmpname, compiled_source_script)) {
        if(errno != EEXIST) {
            unlink(sieve_tmpname);
            unlink(compiled_source_script);
            return 1;
        }
    }
    return 0;
}


/* to make larry's stupid functions happy :) */
static void foo(void)
{
    fatal("stub function called", 0);
}

extern sieve_vacation_t vacation2;/* = {
    0,                          / min response /
    0,                          / max response /
    (sieve_callback *) &foo,    / autorespond() /
    (sieve_callback *) &foo     / send_response() /
}; */

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
    fprintf(stderr, "%s\n", buf);
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
        fprintf(stderr, "sieve_interp_alloc() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_redirect(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_redirect() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_discard(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_discard() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_reject(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_reject() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_fileinto(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_fileinto() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }
    res = sieve_register_keep(i, (sieve_callback *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_keep() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_imapflags(i, NULL);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_imapflags() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_size(i, (sieve_get_size *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_size() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_header(i, (sieve_get_header *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_header() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_envelope(i, (sieve_get_envelope *) &foo);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_envelope() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_vacation(i, &vacation2);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_vacation() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_notify(i, &sieve_notify);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_notify() returns %d\n", res);
        return TIMSIEVE_FAIL;
    }

    res = sieve_register_parse_error(i, &mysieve_error);
    if (res != SIEVE_OK) {
        fprintf(stderr, "sieve_register_parse_error() returns %d\n", res);
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






