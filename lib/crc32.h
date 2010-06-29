/* crc32.h
 */

#ifndef CRC32_H
#define CRC32_H
#include <sys/uio.h>
#include <stdint.h>

uint32_t crc32_map(const char *buf, unsigned bytes);
uint32_t crc32_cstring(const char *buf);
uint32_t crc32_iovec(struct iovec *iov, int iovcnt);

#endif
