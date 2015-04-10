/*      $Id: Exception.c,v 1.10 1999/10/03 11:46:36 ooc-devel Exp $    */
/*  Provides facilities to raise and handle exceptions.
    Copyright (C) 1997, 1998, 1999  Michael van Acken

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
#include <stddef.h>
#include <setjmp.h>
#include <string.h>

#include "__oo2c.h"
#include "__mini_gc.h"
#include "__config.h"

/* --- begin #include "Exception.d" */
#include "Exception.h"

/* local definitions */
Exception__Source Exception__halt;
Exception__Source Exception__assert;
Exception__Source Exception__signal;
Exception__Source Exception__runtime;

/* function prototypes */

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const char name[10];
} _n0 = {10, NULL, {"Exception"}};
static struct _MD Exception_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL
  }
};

static const struct {
  int length;
  void* pad;
  const char name[20];
} _n1 = {20, NULL, {"SourceDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[1];
} Exception__SourceDesc_tdb = {
  1, 
  NULL, 
  {
    &Exception__SourceDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb0 = {0, NULL, {
  NULL
}};
struct _TD Exception__SourceDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Exception__SourceDesc_tdb.btypes,
    _tb0.tbprocs,
    (const unsigned char*)_n1.name,
    &Exception_md.md,
    0, 
    '0', '1',
    sizeof(Exception__SourceDesc),
    NULL
  }
};

/* local strings */

/* --- end #include "Exception.d" */


/* boolean variable to distinguish between normal and exception execution 
   state; the program starts in the state of normal execution, of course */
static int is_exception = 0;

/* current top of context stack; NULL means the stack is empty, the default
   exception handler should be used */
static _ExecutionContext top_context = NULL;

/* this variable is used to pass the exception source to the reactivation
   of PUSHCONTEXT: */
void* _Exception__source = NULL;

/* exception source associated with exceptions raised by this module */
static Exception__Source eexcept;
#define NORMAL_EXECUTION 1
#define EXCEPTIONAL_EXECUTION 2
#define STACK_EMPTY 3
#define INVALID_RAISE 4

/* the following variables describe together with _Exception__source the raised
   exception if the program is in the exceptional execution state: */
#define MESSAGE_LENGTH 128
static _ExecutionContext _Exception__context = NULL;
static LONGINT _Exception__number = 0;
static CHAR _Exception__message[MESSAGE_LENGTH];


#define STR_PARAM(text) (CHAR*)text,sizeof(text)


static _ModId _mid;

void _push_Exception__context(_ExecutionContext c) {
  c->next = top_context;
  top_context = c;
}

void Exception__POPCONTEXT(void) {
  if(top_context) {     /* stack isn't empty */
    if(is_exception) {
      /* pass exception along to next higher exception handler; since we are
         in an exception, RAISE will reactivate the second stack element */
      Exception__RAISE(_Exception__source, _Exception__number, 
                      _Exception__message,
                      strlen((char*)_Exception__message));
    } else {                    /* just pop top of stack */
      top_context = top_context->next;
    }
  } else {
    Exception__RAISE(eexcept, STACK_EMPTY,
                    STR_PARAM("[Exception] POPCONTEXT called while stack is empty"));
  }
}

void Exception__RETRY(void) {
  _exception_pos = 0;           /* clear file position */
  if(is_exception) {
    longjmp(*(jmp_buf*)_Exception__context->jmpbuf, -1);
  } else {
    Exception__RAISE(eexcept, NORMAL_EXECUTION, 
                    STR_PARAM("[Exception] RETRY called in normal execution state"));
  }
}

void Exception__ACKNOWLEDGE(void) {
  _exception_pos = 0;           /* clear file position */
  if(is_exception) {
    is_exception = 0;
  } else {
    Exception__RAISE(eexcept, NORMAL_EXECUTION, 
                    STR_PARAM("[Exception] ACKNOWLEDGE called in normal execution state"));
  }
}

void Exception__AllocateSource(Exception__Source *newSource) {
  NEW_REC(*newSource, Exception__SourceDesc);
}

void Exception__RAISE(Exception__Source source, LONGINT number, 
                     const CHAR* message__ref, LONGINT message_0d) {
  if (!source) {
    Exception__RAISE(eexcept, INVALID_RAISE, 
                    STR_PARAM("[Exception] First parameter of RAISE is NIL"));
  }
    
  if(is_exception) {
    /* if an exception was raised while handling an exception, pop the topmost
       context that caused the second exception and reactivate the context 
       below it to deal with the new exception */
    top_context = top_context->next;
  } else {
    is_exception = 1;
  }
  /* store information describing the current exception in global variables */
  _Exception__source = source;
  _Exception__number = number;
  _Exception__context = top_context;
  _string_copy(_Exception__message, message__ref, MESSAGE_LENGTH);
  if (_Exception__context) {
    /* reactivate topmost context */
    longjmp(*(jmp_buf*)_Exception__context->jmpbuf, 1);
  } else {
    /* oops, stack is empty; use default exception handler from __oo2c.c --
       it'll write a nice message and abort */
    _default_exception_handler(source, number, message__ref);
  }
}

LONGINT Exception__CurrentNumber(Exception__Source source) {
  if(is_exception) {
    return _Exception__number;
  } else {
    Exception__RAISE(eexcept, NORMAL_EXECUTION, 
                    STR_PARAM("[Exception] CurrentNumber called in normal execution state"));
    return 0;  /* never reached */
  }
}

void Exception__GetMessage(CHAR* text, LONGINT text_0d) {
  if(is_exception) {
    _string_copy(text, _Exception__message, text_0d);
  } else {
    Exception__RAISE(eexcept, NORMAL_EXECUTION, 
                    STR_PARAM("[Exception] GetMessage called in normal execution state"));
  }
}

BOOLEAN Exception__IsExceptionalExecution(void) {
  return (BOOLEAN)(is_exception != 0);
}

void Exception_init(void) {
  _mid = _register_module(&Exception_md.md, &Exception__SourceDesc_td.td);
  Exception__AllocateSource(&eexcept);
  Exception__AllocateSource(&Exception__halt);
  Exception__AllocateSource(&Exception__assert);
  Exception__AllocateSource(&Exception__runtime);
  Exception__AllocateSource(&Exception__signal);
  _exception_halt = Exception__halt;
  _exception_assert = Exception__assert;
  _exception_raise = (void (*) (void*, LONGINT, const CHAR*, LONGINT)) Exception__RAISE;
}
