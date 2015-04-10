/*	$Id: __mini_gc.h,v 1.6 1999/07/20 17:17:49 acken Exp $	*/
/* if you include this file into standard C code, e.g. to specify the 
   implementation of a FOREIGN module, include stddef.h first to provide
   the definition of size_t */

#ifndef _GC_H  /* ignore this code if the original gc.h is included */

/* --- prototypes of gc functions called by the emitted code: */
#if USE_GC
#ifdef __cplusplus
  extern "C" {
#endif
#ifdef __oo2c_libc__
#define size_t ooc_size_t
#endif
extern void* GC_malloc(size_t n);
extern void* GC_malloc_atomic(size_t n);
extern void GC_free(void* ptr);
extern void GC_gcollect(void);
#ifdef __oo2c_libc__
#undef size_t
#endif
#ifdef __cplusplus
  }  /* end of extern "C" */
#endif
#else
#define GC_malloc malloc
#define GC_malloc_atomic malloc
#define GC_free free
#define GC_gcollect()
#endif

#endif
