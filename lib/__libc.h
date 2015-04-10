/*	$Id: __libc.h,v 1.6 1999/07/20 17:17:57 acken Exp $	*/
/* make sure that __config.h has been included before this file! */
#ifndef __oo2c_libc__
#define __oo2c_libc__

#ifdef __cplusplus
  extern "C" {
#endif

typedef LOCAL_SIZE_T ooc_size_t;

/* --- prototypes of libc functions called by the emitted code: */
extern void* malloc(ooc_size_t n);
extern void free(void *ptr);
#ifdef __GNUC__
/* somehow gcc 2.7.2 on SunOS 4 doesn't like the size_t type defined above and
   complains about a declaration conflict with its builtin memcpy; but with 
   gcc there is always a tricky and non-standard way around this problem: */
extern void* memcpy(void* dest, const void* src, __typeof__(sizeof(int)) n);
extern void* memset(void* block, int c, __typeof__(sizeof(int)) n);
#else
extern void* memcpy(void* dest, const void* src, ooc_size_t n);
extern void* memset(void* block, int c, ooc_size_t n);
#endif
extern int strcmp(const char* s1, const char* s2);

#ifdef __cplusplus
  }  /* end of extern "C" */
#endif

#include "__mini_gc.h"

#endif /* __oo2c_libc__ */
