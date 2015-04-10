(* 	$Id: Exception.Mod,v 1.9 1999/10/03 11:46:22 ooc-devel Exp $	 *)
MODULE Exception [FOREIGN "C"; LINK FILE "Exception.c" END];
(*  Provides facilities to raise and handle exceptions.
    Copyright (C) 1997, 1998  Michael van Acken, Eric Nikitin

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
*)
<* Warnings := FALSE *>


(* Exceptions are events that may require special processing by the user 
   program or by the implementation. 
   
   Exceptions may be raised by the computer's error-detection mechanisms,
   via calls to HALT or ASSERT, by the user program itself, or by actions
   external to the program.
   
   The primary use of this module is to provide error handling and allow
   programmer control over both system and language ( HALT and ASSERT )
   exception handling. The programmer may define handlers which can be
   used in place of those defined by the implementation.
*)

(*
Notes:
Wherever the word `thread' appears below it should be read as
`program' for the moment.  Multi-threading isn't supported yet. 

There are two states of program execution: normal and exceptional.
Until the first call to RAISE the program is in the normal execution
state.  After that it stays in the exceptional execution state until
ACKNOWLEDGE or RETRY is called.  

The restriction of PUSHCONTEXT that at most one context can be active
in a procedure allows an efficient implementation of the context stack
without falling back upon heap objects.

The state of all nonglobal variables that were modified after a
PUSHCONTEXT is undefined if the context is activated again by raising
an exception or calling RETRY.  The reason is simple: while the
compiler ensures that the evaluation of a piece of code delivers the
correct results in the end, it does not ensure that the state of an
interrupted computation is correctly reflected by the memory contents
at the time of the interruption.  An additional restriction affects
exceptions that weren't initiated by an explicit call to RAISE, i.e.,
failed run-time checks and external signals.  For these exceptions the
exact place of the raised execption, i.e., the set of instructions that
were completed before it was raised, is undefined.  The reason is that
a sequence of instructions as specified in the source code may be
evaluated in a different order or in an overlapped fashion in the
emitted machine code.  

Unlike Modula-2, the programmer is responsible for managing the stack of
exception handlers.  The stack is primarily manipulated through the procedures 
PUSHCONTEXT and POPCONTEXT.  The only other action that changes the stack is
a raised exception while the program is an exceptional execution state: this
will pop the topmost context (that was responsible for the exception) from the
stack before moving control to the then topmost execution context.  Raising an
exception in the state of normal execution will _not_ change the stack.  
Therefore every call to PUSHCONTEXT must have exactly one matching call to
POPCONTEXT in the same procedure, assuming that the program parts in between
are completed without raising an exception.

If a stack underflow occurs when POPCONTEXT is called, an exception is raised.
If an execution context is left of the stack that doesn't correspond to a valid
procedure, i.e. a procedure doing a PUSHCONTEXT was left without doing a 
matching POPCONTEXT, activating the context by raising an exception will 
transfer the program into a completely undefined state.  Most likely it'll 
abort due to a segmentation violation or a comparable error, or the stack of
execution contexts is rolled back until a valid context is reached.  There is
no way to check for such a situation.  Any programmer should be aware that an
invalid context stack can cause considerable grief.

With the procedure `SetException' of module Signal a signal handler can be 
installed that will raise an exception for a given signal number.  Unless 
specified otherwise, signals will trigger their respective default actions.
*)


CONST
  (* the following exception numbers belong to the source `runtime'; they 
     correspond to failed run-time checks; note for maintainer: this list has
     to be in sync with the one defined in __Exception.h *)
  derefOfNIL* = 1;       (* dereference of NIL or type test on NIL *)
  realDivByZero* = 2;    (* integer or real division by zero *)
  integerDivByZero* = 3; (* integer or real division by zero *)
  realOverflow* = 4;     (* real overflow (conversion or arithmetic op) *)
  integerOverflow* = 5;  (* integer overflow (conversion or arithmetic op) *)
  illegalLength* = 6;    (* NEW was called with negative length for array *)
  outOfMemory* = 7;      (* NEW couldn't allocate the requested memory *)
  indexOutOfRange* = 8;  (* array index out of range *)
  elementOutOfRange* = 9;(* set element out of range *)
  endOfFunction* = 10;   (* control reaches end of function procedure *)
  noMatchingLabel* = 11; (* no matching label in CASE construct *)
  noValidGuard* = 12;    (* all guards of WITH failed *)
  typeGuardFailed* = 13; (* type guard failed *)
  typeAssertFailed* = 14;(* illegal type of target of record assignment *)
  stackOverflow* = 15;   (* stack overflow *)
  
TYPE
  Number* = LONGINT;
  Source* = POINTER TO SourceDesc;
  SourceDesc* = RECORD
  END;

VAR
  (* these two exception variables are associated to the standard
     predefined procedures HALT and ASSERT; HALT(n) is equivalent to 
     RAISE(halt, n, ""), and ASSERT(FALSE, n) to RAISE (assert, n, "") *)
  halt-: Source;
  assert-: Source;
  (* this exception source is used to report failed run-time checks: *)
  runtime-: Source;

PROCEDURE [PROC_ID=1] PUSHCONTEXT* (VAR source: Source);
(* Pushes the current execution context onto the exception handler
stack and sets `source' to NIL.  If the context is reactivated later by 
raising an exception, it will be set to the exception's source.
Only one context can be pushed per procedure at a time.  During a 
single procedure evaluation two successive calls to PUSHCONTEXT without
a POPCONTEXT in between are not allowed and will result in undefined
program behaviour.
Note: All nonglobal variables of the enclosing procedures that were
modified after the initial call to PUSHCONTEXT are undefined when the
context is activated again by raising an exception.  *)

PROCEDURE POPCONTEXT*;
(* Removes the exception handler on the top of the stack.  During the
execution of a procedure the dynamic number of calls to POPCONTEXT has
to balance the ones to PUSHCONTEXT.  If the stack is empty an exception
is raised.  If the program is in an exceptional execution state at the
point where POPCONTEXT is called, the exception is raised again, thereby
passing it along to the next higher exception handler.  *)

PROCEDURE RETRY*;
(* If the current thread is in the exceptional execution state, the
context on top of the stack of exception handlers is reactivated in
the state of normal execution; this will look as if the corresponding
call of PUSHCONTEXT will return again, with the parameter `source' set 
to NIL.  This allows the "normal" part to be re-executed.  Be very
careful when using this since all local variables of the enclosing
procedure that were modified after the initial call to PUSHCONTEXT are
undefined when activating the context again. 
If the current thread is in the normal execution state, calling
RETRY will raise an exception.  *)

PROCEDURE ACKNOWLEDGE*;
(* If the current thread is in the exceptional execution state, it
is placed back into the state of normal execution.  Otherwise an
exception will be raised.  Calling this procedure indicates that an
exception has been handled without retrying the "normal" part.  *)

PROCEDURE AllocateSource* (VAR newSource: Source);
(* Allocates a unique value of type Source.  If an unique
value cannot be allocated, an exception will be raised.  *)

PROCEDURE RAISE* (source: Source; number: Number;
                  message: ARRAY OF CHAR);
(* Associates the given values of source, number and message with the
current context and raises an exception.  This means that the current
thread switches into the exceptional execution state and activates
a program context from the stack of exception handlers. If the program
is in the normal execution state, the context on top of the stack is
selected.  If it's in an exceptional execution state the stack is 
popped first.  Reactivating the execution context will look as if the 
corresponding call to PUSHCONTEXT will return a second time, this time 
returning the first argument of RAISE in the variable parameter `source'.

The message should have the format "[<module>] <description>".  It may be 
truncated by RAISE to an implementation-defined length.   Using a value of NIL 
for the first argument will raise an exception. *)


PROCEDURE CurrentNumber* (source: Source): Number; 
(* If the current thread is in the exceptional execution state
because of the raising of an exception from source, returns the
corresponding number, and otherwise raises an exception.  *)

PROCEDURE GetMessage* (VAR text: ARRAY OF CHAR);
(* If the current thread is in the exceptional execution state,
returns the possibly truncated string associated with the current
context.  Otherwise, in normal execution state, returns the empty
string.  *)

PROCEDURE IsExceptionalExecution* (): BOOLEAN;
(* If the current thread is in the exceptional execution state
because of the raising of an exception, returns TRUE, and otherwise
returns FALSE.  *)

END Exception.
