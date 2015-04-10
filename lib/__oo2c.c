/*	$Id: __oo2c.c,v 1.24 2000/09/23 19:40:51 ooc-devel Exp $	*/
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
#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <sys/types.h>
#include <string.h>
#if HAVE_UNISTD_H
#include <unistd.h>
#elif HAVE_IO_H
#include <io.h>
#endif

#if USE_GC
#  define _GC_H
#endif
#include "__oo2c.h"
#if USE_GC
#  undef _GC_H
#  include "__gc.h"  /* this is gc.h from the gc distrib */
#endif
#if HAVE_BACKTRACE_SYMBOLS
#  include <execinfo.h>
#endif

#define MAX_BACKTRACE_LEVELS 20  /* max number of backtraced procedure calls */

char* _top_vs;  /* top of value stack */
char* _end_vs;  /* end of value stack */

LONGINT _program_argc;
OOC_CHAR **_program_argv;
INTEGER _program_exit_code = 0;

/* the following variables are used by the default exception handler; they are
   declared in __Exception.h, see there for more information: */
_Pos _exception_pos = 0;
void* _exception_halt = (void*)1;
void* _exception_assert = (void*)2;
void* _exception_runtime = (void*)3;
void* _exception_signal = (void*)4;
void (*_exception_raise) (void*, LONGINT, const OOC_CHAR*, LONGINT) = NULL;
void (* _exception_run_term_procs) (void) = NULL;


/* --- initialization function, called at the beginning of main(): */
void _oo2c_init(void) {
#if USE_GC
  GC_INIT();
  /* tell GC to accept pointers with an offset of 8/16/24 as references to
     a given object; this is necessary if the GC was built without the
     ALL_INTERIOR_POINTERS option; the offsets cover records and open 
     arrays with upto 5 free dimensions */
  GC_register_displacement(8);
  GC_register_displacement(16);
  GC_register_displacement(24);
#endif
}


/* --- string comparison of LONGCHAR: */
int strcmpl(const LONGCHAR *S1, const LONGCHAR *S2) {
  int i = 0;
  while (S1[i] && (S1[i] == S2[i])) { i++; }
  return ((int)S1[i] - (int)S2[i]);
}


/* --- functions to handle exceptions and failed run-time checks: */
#define POS_MODULO 1024
#define PREFIX "## "

static void NORETURN _break_rtc(void) NORETURN2;
static void NORETURN raise_exception(void* source, LONGINT number, 
				     const char* message, _Pos pos) NORETURN2;


static void _break_rtc(void) {
/* use this function as breakpoint when debugging a failed runtime check */
  exit(127);
}

static void write_backtrace () {
#if HAVE_BACKTRACE_SYMBOLS
#define BACKTRACE_OFFSET 1
  void* farray[MAX_BACKTRACE_LEVELS+BACKTRACE_OFFSET];
  int i, size;
  char** names;
  
  size = backtrace(farray, MAX_BACKTRACE_LEVELS+BACKTRACE_OFFSET);
  names = backtrace_symbols(farray, size);
  for (i=0; i<size; i++) {
    (void)fprintf(stderr, "%d: %s\n", i, names[i]);
  }
#endif
}

void _default_exception_handler(void* source, LONGINT number, 
				const OOC_CHAR* message) {
/* Default exception handler, activated if the Exception module isn't part of
   the program, or if the stack of execution contexts is empty.  Depending on
   the value of `source' one of the following actions will be taken:
   a) source is _exception_halt
      exit silently, using `number' as exit code
   b) source is _exception_assert
      print message to stderr, exit with code `number'
   c) source is _exception_runtime
      print message to stderr, call _break_rtc to exit
   If the variable _exception_pos isn't zero (i.e., if it has been set by one 
   of the functions activated for failed run-time checks), the module name and
   the file position is inserted into the output.  */
  _Module m;
  const char *mname, *start, *end;
  char buffer[256];
  int i;
  
  if (source == _exception_halt) {
    /* exit silently, setting the exit code to `number' */
    exit(number);
  } else {
    /* write message including the message, the number, and (if available) the
       file position to stdout */
    (void)fprintf(stderr, 
		  PREFIX "\n" 
		  PREFIX "Unhandled exception (#" LI_FORMAT ")", number);
  
    if(_exception_pos) {
      /* someone passed us the file position for the raised exception; extract
	 module and character position and write it to stderr */
      m = _get_module (_exception_pos % POS_MODULO);
      if (m) {
	mname = (const char*)m->name;
      } else { 
	mname = "<\?\?\?>";
      }
      (void)fprintf(stderr, " in module %s at pos " LI_FORMAT ":\n",
		    mname, _exception_pos / POS_MODULO);
    } else {
      (void)fprintf(stderr, ":\n");
    }
    
    /* extract lines from `message' */
    start = (const char*)message;
    while (*start) {
      end = start;
      i = 0;
      while (*end && (*end != '\n')) {
	buffer[i] = *end;
	end++;
	i++;
      }
      buffer[i] = '\000';
      
      (void)fprintf(stderr, PREFIX "%s\n", buffer);
      
      if (*end) {
	start = end+1;
      } else {
	start = end;
      }
    }
    (void)fprintf(stderr, PREFIX "\n");

    if (source == _exception_signal) {
      (void)signal(number, SIG_DFL);
      if (_exception_run_term_procs) {
	_exception_run_term_procs();
      }
      write_backtrace();
#if HAVE_RAISE
      raise(number);
#else
      (void)kill(getpid(), number);
#endif
      _break_rtc();
    } else if (source == _exception_assert) {
      write_backtrace();
      exit(number);
    } else {
      write_backtrace();
      _break_rtc();
    }
  }
}

static void raise_exception(void* source, LONGINT number, 
			    const char* message, _Pos pos) {
/* If module Exception is part of the program, call Exception.RAISE with 
   the appropriate parameters.  Otherwise activate the default exception
   handler.  */
  _exception_pos = pos;
  if (_exception_raise) {
    _exception_raise(source, number, (const OOC_CHAR*)message, strlen(message)+1);
    exit(127);			/* should never be reached */
  } else {
    _default_exception_handler(source, number, (const OOC_CHAR*)message);
  }
}


void _deref_of_nil(_Pos pos) {
  raise_exception(_exception_runtime, RT_derefOfNIL, 
		  "Dereference of NIL", pos);
}

void _real_div_by_zero(_Pos pos) {
  raise_exception(_exception_runtime, RT_realDivByZero, 
		  "Real division by zero", pos);
}

void _integer_div_by_zero(_Pos pos) {
  raise_exception(_exception_runtime, RT_integerDivByZero, 
		  "Integer division by zero", pos);
}

void _real_overflow(_Pos pos) {
  raise_exception(_exception_runtime, RT_realOverflow, 
		  "Real overflow", pos);
}

void _integer_overflow(_Pos pos) {
  raise_exception(_exception_runtime, RT_integerOverflow, 
		  "Integer overflow", pos);
}

void _invalid_length(LONGINT length, _Pos pos) {
  char s[512];
  
  (void)sprintf(s, "NEW was called with a length of " LI_FORMAT, length);
  raise_exception(_exception_runtime, RT_illegalLength, s, pos);
}

void _new_failed(_Pos pos) {
  raise_exception(_exception_runtime, RT_outOfMemory, 
		  "Failed to allocate heap object", pos);
}

void _index_out_of_range(LONGINT index, LONGINT length, _Pos pos) {
  char s[512];
  
  (void)sprintf(s, "Array index out of range\n" 
		LI_FORMAT " not in 0 <= x < " LI_FORMAT, index, length);
  raise_exception(_exception_runtime, RT_indexOutOfRange, s, pos);
}

void _element_out_of_range(LONGINT index, LONGINT size, _Pos pos) {
  char s[512];
  
  (void)sprintf(s, "Set element out of range\n" 
		LI_FORMAT " not in 0 <= x < " LI_FORMAT, index, size);
  raise_exception(_exception_runtime, RT_elementOutOfRange, s, pos);
}

void _no_return(_Pos pos) {
  raise_exception(_exception_runtime, RT_endOfFunction, 
		  "Control reaches end of function procedure", pos);
}

void _case_failed(LONGINT select, _Pos pos) {
  char s[512];
  
  (void)sprintf(s, "Invalid CASE selector\n`" LI_FORMAT 
		"' doesn't match any label", select);
  raise_exception(_exception_runtime, RT_noMatchingLabel, s, pos);
}

void _with_failed(_Pos pos) {
  raise_exception(_exception_runtime, RT_noValidGuard, 
		  "All guards of WITH statement failed", pos);
}

void _type_guard_failed(void* tag, _Pos pos) {
  const OOC_CHAR *tname = ((_Type)tag)->name;
  const OOC_CHAR *mname = ((_Type)tag)->module->name;
  char s[512];

  if (!tname) tname = (const OOC_CHAR*)"<unknown>";
  (void)sprintf(s, "Type guard failed\nThe variable's dynamic type is %s.%s",
		mname, tname);
  raise_exception(_exception_runtime, RT_typeGuardFailed, s, pos);
}

void _type_assert_failed(_Pos pos) {
  raise_exception(_exception_runtime, RT_typeAssertFailed, 
		  "Dynamic type of assignment target differs from static type", pos);
}

void _assertion_failed(LONGINT code, _Pos pos) {
  raise_exception(_exception_assert, code, "Assertion failed", pos);
}

void _halt(LONGINT code){
  raise_exception(_exception_halt, code, "HALT", 0);
}

void _array_stack_overflow(_Pos pos) {
  raise_exception(_exception_runtime, RT_stackOverflow, 
		  "Overflow of array stack", pos);
}


#include "__Descr.c"
