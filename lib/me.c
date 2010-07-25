/* Messagingengine.com utility functions */

#include <sys/socket.h>
#include <sys/un.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "me.h"
#include "libconfig.h"

#ifndef msg_warn
#include <sys/syslog.h>
void msg_warn(char *message)
{
  syslog(LOG_ERR, "%s", message);
}
#endif

static void rc4_encode(int key_len, unsigned char * key_buf, int data_len, unsigned char * data_buf);
static char * base64_encode (int data_len, unsigned char * data);

int me_send_rate(char * username, char *resource, int count)
{
  char message[2048];
  int  sock, cnt;
  struct sockaddr_un myname;

  sock = socket(PF_LOCAL, SOCK_STREAM, 0);
  if (sock < 0) {
    msg_warn("rated client socket failure");
    return 0;
  }

  myname.sun_family = AF_LOCAL;
  strncpy(myname.sun_path, ME_RATE_SOCK, sizeof(myname.sun_path));
  myname.sun_path[sizeof(myname.sun_path) - 1] = '\0';

  if (connect(sock, (struct sockaddr *) &myname, SUN_LEN(&myname)) < 0) {
    msg_warn("rated client connect failure");
    close(sock);
    return 0;
  }

  message[2047] = '\0';
  snprintf(message, 2047, "%s,%s,%d\n", username, resource, count);
  cnt = write(sock, message, strlen(message));
  close(sock);

  return 1;
}

char * me_create_sasl_enc(char *username)
{
  static char padded_sasl[256], junk_buf[256], key_buf[256];
  int i, junk_len, epoch, key_len, data_len;
  char *encoded_base64;
  const char * format;

  epoch = (int)time(0);
  junk_len = 31 - strlen(username);
  if (junk_len < 0) junk_len = 0;

  for (i = 0; i < junk_len; i++)
    junk_buf[i] = 'A' + (rand() % 26);
  junk_buf[i] = '\0';

  padded_sasl[255] = '\0';
  snprintf(padded_sasl, 255, "%02d%s%s", junk_len, junk_buf, username);

  key_buf[255] = '\0';
  format = config_getstring(IMAPOPT_ME_SECRET);
  snprintf(key_buf, 255, format, epoch, epoch);

  key_len = strlen(key_buf);
  data_len = strlen(padded_sasl);
  rc4_encode(key_len, (unsigned char *)key_buf, data_len, (unsigned char *)padded_sasl);
  encoded_base64 = base64_encode(data_len, (unsigned char *)padded_sasl);

  padded_sasl[255] = '\0';
  snprintf(padded_sasl, 255, "%s %d", encoded_base64, epoch);

  return padded_sasl;
}

static void rc4_encode(int key_len, unsigned char * key_buf, int data_len, unsigned char * data_buf) {
  static unsigned char S[256];
  unsigned char tmp;
  int i = 0, j = 0, l;

  for (i = 0; i < 256; i++) S[i] = i;
  for (i = 0; i < 256; i++) {
    j = (j + S[i] + key_buf[i % key_len]) % 256;
    tmp = S[i]; S[i] = S[j]; S[j] = tmp;
  }
  i = 0;
  for (l = 0; l < data_len; l++) {
    i = (i + 1) % 256;
    j = (j + S[i]) % 256;
    tmp = S[i]; S[i] = S[j]; S[j] = tmp;
    data_buf[l] ^= S[(S[i] + S[j]) % 256];
  }
}

static char * base64_encode (int data_len, unsigned char * data)
{
    static char* base64 =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    static char tobuf[512];
    unsigned char * end = data + (data_len < 500 ? data_len: 500);
    char *d = tobuf;
    unsigned char c1, c2, c3;

    while (1) {
        c1 = *data++;
        *d++ = base64[c1>>2];
        c2 = *data++;
        *d++ = base64[((c1 & 0x3) << 4) | ((c2 & 0xF0) >> 4)];
        if (data > end) break;
        c3 = *data++;
        *d++ = base64[((c2 & 0xF) << 2) | ((c3 & 0xC0) >> 6)];
        if (data > end) break;
        *d++ = base64[c3 & 0x3F];
        if (data == end) break;
    }
    *d = '\0';
    return tobuf;
}

