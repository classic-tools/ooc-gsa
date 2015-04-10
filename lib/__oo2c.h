/*	$Id: __oo2c.h,v 1.21 2000/09/23 19:40:51 ooc-devel Exp $	*/
/*  Run-time system for oo2c programs.
    Copyright (C) 1997-2000  Michael van Acken

    This module is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public License
    as published by the Free Software Foundation; either version 2 of
    the License, or (at your option) any later version.

    This module is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with OOC. If not, write to the Free Software Foundation,
    59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/
#ifndef __oo2c__
#define __oo2c__

#include "__config.h"

/* AIX requires this to be the first thing in the file, except for 
   comments and preprocessor directives */
#ifdef __VISUALC__
#    include <malloc.h>
#elif defined(_ALLOCA_H)
/* ignore if alloca.h has already been included */
#elif __GNUC__
#  define alloca __builtin_alloca
#else
#  if HAVE_ALLOCA_H
#    include <alloca.h>  /* this can cause warnings in __libc.h */
#  else
#    ifdef _AIX
 #pragma alloca
#    else
#      ifndef alloca /* predefined by HP cc +Olibcalls */
char *alloca ();
#      endif
#    endif
#  endif
#endif

#include "__StdTypes.h"
#include "__Descr.h"
#include "__Exception.h"


/* define attributes that mark functions that won't return; those attributes
   are only used in __oo2c.h and __oo2c.c */
#undef NORETURN
#undef NORETURN2
#if defined(__GNUC__) && (__GNUC__>2 || (__GNUC__==2 && __GNUC_MINOR__>=6))
#define NORETURN
#define NORETURN2 __attribute__ ((__noreturn__))
#else
#define NORETURN
#define NORETURN2
#endif

/* set struct attribute to force the C compiler to avoid its own field
   alignment */
#if __GNUC__
#define _NOALIGN __attribute__((packed))
#else
#define _NOALIGN
#endif


/* --- prototypes for functions to report failed run-time checks: */
extern void NORETURN _deref_of_nil(_Pos pos) NORETURN2;
extern void NORETURN _real_div_by_zero(_Pos pos) NORETURN2;
extern void NORETURN _integer_div_by_zero(_Pos pos) NORETURN2;
extern void NORETURN _real_overflow(_Pos pos) NORETURN2;
extern void NORETURN _integer_overflow(_Pos pos) NORETURN2;
extern void NORETURN _invalid_length(LONGINT length, _Pos pos) NORETURN2;
extern void NORETURN _new_failed(_Pos pos) NORETURN2;
extern void NORETURN _index_out_of_range(LONGINT index, LONGINT length, _Pos pos) NORETURN2;
extern void NORETURN _element_out_of_range(LONGINT index, LONGINT size, _Pos pos) NORETURN2;
extern void NORETURN _no_return(_Pos pos) NORETURN2;
extern void NORETURN _case_failed(LONGINT select, _Pos pos) NORETURN2;
extern void NORETURN _with_failed(_Pos pos) NORETURN2;
extern void NORETURN _type_guard_failed(void* tag, _Pos pos) NORETURN2;
extern void NORETURN _type_assert_failed(_Pos pos) NORETURN2;
extern void NORETURN _assertion_failed(LONGINT code, _Pos pos) NORETURN2;
extern void NORETURN _array_stack_overflow(_Pos pos) NORETURN2;

#define _div_by_zero _integer_div_by_zero 
  /* for compability between 1.3.1 and 1.3.2; will be removed later... */

extern void NORETURN _default_exception_handler(void* source, LONGINT number, const OOC_CHAR* message) NORETURN2;
extern void NORETURN _halt(LONGINT code) NORETURN2;



/* --- macros to create local copies of value parameters: */
extern char* _top_vs;  /* top of value stack */
extern char* _end_vs;  /* end of value stack */

#define _push_value(_type,_dest,_src,_size) {			\
  _type _s = _size;						\
  _type _n = ((_type)_top_vs+_s+7) & ~((_type)7);		\
  _dest = memcpy((void*)_top_vs, (const void*)_src, _s);	\
  _top_vs = (char*)_n;						\
}
#define _push_value_ov(_type,_dest,_src,_size,_pos) {		\
  _type _s = _size;						\
  _type _n = ((_type)_top_vs+_s+7) & ~((_type)7);		\
  if((unsigned _type)_n > (unsigned _type)_end_vs)              \
    _array_stack_overflow(_pos);		                \
  _dest = memcpy((void*)_top_vs, (const void*)_src, _s);	\
  _top_vs = (char*)_n;						\
}
#define _push_value_alloca(_type,_dest,_src,_size) {		\
  _type _s = _size;						\
  _dest = memcpy((void*)alloca(_s), (const void*)_src, _s);	\
}



/* --- macros for some Oberon-2 operations: */
#define _div(_v,_x,_y,_type) {			\
  _type _quot = _x / _y, _rem = _x % _y;	\
  if (_rem && ((_rem > 0) != (_y > 0)))		\
    _v = _quot-1;				\
  else						\
    _v = _quot;					\
}

#define _mod(_v,_x,_y,_type) {			\
  _type _rem = _x % _y;				\
  if (_rem && ((_rem > 0) != (_y > 0)))		\
    _v = _rem+_y;				\
  else						\
    _v = _rem;					\
}

#define _abs(_x) (_x >= 0) ? (_x) : (- _x)

#define _entier(_v,_x) {			\
  _v = _x;					\
  if ((_v > _x) && (_v-1 <= _x)) _v--;		\
}

/* ... ASH undefined for ABS(_n)>=32, no overflow checking */
#define _ashl(_x,_n,_ucast) (_x << _n)
#define _ashr(_x,_n,_ucast) (_x >> _n) | ((_x >= 0) ? 0 : ~(~_ucast 0 >> _n))
#define _ash(_x,_n,_ucast) (_n >= 0) ? _ashl(_x,_n,_ucast) : _ashr(_x,- _n,_ucast)

#define _cap(_c) ((96<_c && _c<123) || (224<=_c && _c<255 && _c!=247)) ? (_c-32) : _c
#define _capl(_c) _cap(_c)

#define _odd(_x) _x & 1

#define _lshl(_x,_n,_ucast) (_ucast _x << _n)
#define _lshr(_x,_n,_ucast) (_ucast _x >> _n)
#define _lsh(_x,_n,_ucast) ((_n >= 0) ? _lshl(_x,_n,_ucast) : _lshr(_x,- _n,_ucast))

#define _rot(_x,_n,_bits,_ucast) ((_n % _bits >= 0) ? 			\
  (_ucast _x << _n % _bits) | (_ucast _x >> (_bits - _n % _bits)) :	\
  (_ucast _x >> -(_n % _bits)) | (_ucast _x << (_bits + _n % _bits)))
#define _rot_const(_x,_n,_bits,_ucast) \
  (_ucast _x << _n) | (_ucast _x >> (_bits - _n))

#define _bit_range(_ucast,_from,_to) (_from > _to) ? _ucast 0 :		\
  ((_ucast 1 << _to)*2-1) & ~((_ucast 1 << _from)-1)

#define _bit(_adr,_n) (*((char*)_adr + _n/8) & ((char)1 << _n%8)) != 0

#define _string_copy(_dest,_src,_max_len) {				\
  char* _d=(char*)_dest;						\
  const char* _s=(const char*)_src;					\
  char* _max=_d+_max_len-1;						\
  while ((_d != _max) && (*(_d++) = *(_s++)));				\
  if (_d == _max) *_d = '\000';						\
}

#define _string_copyl(_dest,_src,_max_len) {				\
  LONGCHAR* _d=(LONGCHAR*)_dest;					\
  const LONGCHAR* _s=(const LONGCHAR*)_src;				\
  LONGCHAR* _max=_d+_max_len-1;						\
  while ((_d != _max) && (*(_d++) = *(_s++)));				\
  if (_d == _max) *_d = 0;						\
}

#define _string_copy2l(_dest,_src,_max_len) {				\
  LONGCHAR* _d=(LONGCHAR*)_dest;					\
  const OOC_CHAR* _s=(const OOC_CHAR*)_src;					\
  LONGCHAR* _max=_d+_max_len-1;						\
  while ((_d != _max) && (*(_d++) = (LONGCHAR)*(_s++)));		\
  if (_d == _max) *_d = 0;						\
}

/* see also StdTypes.ValidReal */
#define _valid_real(_x) \
  ((-3.4028235677973366E+38 < _x) && (_x < 3.4028235677973366E+38))

/* see also StdTypes.ValidInt */
#define _valid_int(_x) \
  ((-2147483647 - 1 <= _x) && (_x - 1 < 2147483647))

/* see also StdTypes.ValidChar */
#define _valid_char(_x) \
  (0 <= _x) && (_x < 65536)



/* --- type test stuff: */
#define _type_test(_var_tag,_type_tag,_ext_level)			\
  (((_Type)_var_tag)->level >= _ext_level) &&				\
  (((_Type)_var_tag)->btypes[_ext_level] == (_Type)_type_tag)

#define _type_guard(_var_tag,_type_tag,_ext_level,_pos)			\
  if ((((_Type)_var_tag)->level < _ext_level) ||			\
      (((_Type)_var_tag)->btypes[_ext_level] != (_Type)_type_tag))	\
    _type_guard_failed((void*)_var_tag,_pos);

#define _type_assert(_var_tag,_type_tag,_pos)				\
  if ((_Type)_var_tag != (_Type)_type_tag) _type_assert_failed(_pos);

/* --- string comparison of LONGCHAR: */
extern int strcmpl(const LONGCHAR *S1, const LONGCHAR *S2);

/* --- misc stuff: */
#define _P(pos) pos##U*1024+_mid
extern void _oo2c_init(void);
extern LONGINT _program_argc;
extern OOC_CHAR **_program_argv;
extern INTEGER _program_exit_code;
#define _not_zero(_x) ((_x)?(_x):1)

#endif /* __oo2c__ */
