(*	$Id: Signal.Mod,v 1.7 1999/10/03 11:48:41 ooc-devel Exp $	*)
MODULE Signal [FOREIGN "C"; LINK FILE "Signal.c" END];
(*  Signal handling facilities.
    Copyright (C) 1997-1999  Michael van Acken

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

(*
This module provides the means to connect Unix-style signals to the exception 
handling mechanism defined by module Exception.  Beyond that it only implements
a rudimentary interface to signals and signal handling.  Anyone in need of a 
more elaborate interface (e.g., including sigaction) should extend this module
and send me a copy.  Procedures to send signals to other processes are missing
because the OOC lib doesn't know anything about processes (yet).

To learn more about signals check one of the many Unix books.  Or read the 
excellent and free  documentation of the GNU people for their libc 
implementation ("info libc" or "info glibc", chapter "Signal Handling").  Or 
talk a walk through the man pages of your system, maybe starting with "man 
signal" and following the "SEE ALSO" links.
*)


IMPORT
  Exception, C;
  
(* The following constants define symbolic names for signals.  Since signal 
   numbers vary from system to system the numbers below cannot be passed 
   directly to a system call.  A number has to be mapped to the system's 
   numbering scheme first by the function `Map'.  Multiple names can be 
   mapped to a single signal number.  Example: On most systems the signals
   `sigiot' and `sigabrt' are aliases.  Not all signals are available on all
   systems.  If a signal isn't defined for the current system, `Map' will
   return the value `unknownSignal'.  *)
CONST
  (* program error signals *)
  sigfpe* = 0;     (* fatal arithmetic error *)
  sigill* = 1;     (* illegal instruction *)
  sigsegv* = 2;    (* segmentation violation *)
  sigbus* = 3;     (* bus error *)
  sigabrt* = 4;    (* program abortion *)
  sigiot* = 5;     (* I/O trap, usually just another name for sigabrt *)
  sigtrap* = 6;    (* program breakpoint *)
  sigemt* = 7;     (* emulator trap *)
  sigsys* = 8;     (* bad system call *)
  sigstkflt* = 9;  (* stack fault *)
  (* termination signals *)
  sigterm* = 10;   (* generic way to cause program termination *)
  sigint* = 11;    (* program interrupt (usually caused by `C-c') *)
  sigquit* = 12;   (* program interrupt (usually caused by `C-\') *)
  sigkill* = 13;   (* immediate program termination *)
  sighup* = 14;    (* "hang-up" signal *)
  (* alarm signals *)
  sigalrm* = 15;   (* typically indicates expiration of a timer *)
  sigvtalrm* = 16; (* virtual timerO *)
  sigio* = 17;     (* file descriptor is ready to perform input or output *)
  sigurg* = 18;    (* "urgent" or out-of-band data arrived at socket *)
  sigpoll* = 19;   (* System V signal name, similar to sigio *)
  (* job control signals *)
  sigchld* = 20;   (* child process terminates or stops *)
  sigcld* = 21;    (* obsolete name for sigchld *)
  sigcont* = 22;   (* continue process *)
  sigstop* = 23;   (* stop process *)
  sigtstp* = 24;   (* interactive stop signal *)
  sigttin* = 25;   (* background process reads from terminal *)
  sigttou* = 26;   (* background process writes to terminal *)
  (* operation error signals *)
  sigpipe* = 27;   (* broken pipe *)
  siglost* = 28;   (* resource lost *)
  sigxcpu* = 29;   (* CPU time limit exceeded *)
  sigxfsz* = 30;   (* File size limit exceeded *)
  sigpwr* = 31;    (* power state indication *)
  (* miscellaneous signals *)
  sigusr1* = 32;   (* user defined signal 1 *)
  sigusr2* = 33;   (* user defined signal 2 *)
  sigwinch* = 34;  (* window size change *)
  siginfo* = 35;   (* information request *)
  sigdil* = 36;    (* ??? *)

TYPE
  SigNumber* = C.int;
  (* A system dependant integer type.  *)
  
  SigHandler* = PROCEDURE (signum: SigNumber);  
  (* Signature of a signal handler, to be installed with the procedure 
     `SetHandler'.  A procedure variable of this type is activated upon the
     arrival of the signal, passing the system dependent signal number to
     the `signum' parameter.  *)
     
CONST
  unknownSignal* = MIN (SigNumber);
  (* result of `Map' for invalid signal names *)
  

VAR
  exception-: Exception.Source;
  (* exception source for signals; see `handlerException' below *)

VAR  (* Standard signal handlers for `SetHandler'.
        IMPORTANT: Invoking these variables directly has undefined results.  *)
  handlerDefault-,                      (* Default action for signal. *)
  handlerIgnore-,                       (* Signal should be ignored. *)
  handlerException-: SigHandler;           
  (* Signal should raise exception.  Upon arrival of the signal `signum' the
  handler will reinstall itself again as handler for the given signal number,
  and then activate Exception.RAISE with `exception' as source, the message
  string "[Signal] Caught signal number <signum>", and the system dependent
  value of `signum' as exception number.  If the exception isn't handled by the
  user, the default exception handler will print the usual message to stderr,
  reset the signal's handler to the default action, and raise the signal again.
  If the latter doesn't terminate the program, the default handler will
  terminate the program like a failed run-time check.  *)

VAR
  handlerError-: SigHandler;           
  (* The value of this variable is used as the return value from 
     `SetHandler' to indicate an error. *)
  

PROCEDURE Map* (signum: SigNumber): SigNumber;
(* Maps a signal name from the above list onto the system dependent signal 
   number associated with that name.  If the signal isn't defined for the
   system, `unknownSignal' is returned.  More than one signal may be mapped
   onto the same number.  *)

PROCEDURE SetHandler* (signum: SigNumber; action: SigHandler): SigHandler;
(* Installs the signal handler `action' for the signal number `signum'.  The 
   number must be mapped to the system's number scheme first.  That is, the 
   names defined above can't be used directly, they have to be passed through
   `Map' first.  The behaviour of this procedure is undefined if the given
   number doesn't correspond to a legal signal.  If the signal can be handled,
   the next occurence of the given signal will activate the procedure in 
   `action', passing the system specific signal number to its `signum' 
   parameter.  The system might or might not reset the signal handler to the
   default action before calling `action'.  It's generally a good idea to 
   explicitly set the signal handler again as part of `action'.  Calling this
   procedure with `action = NIL' is equivalent to calling it with 
   `action = handlerDefault'.  
   
   On success, the `SetHandler' function returns the action that was previously
   in effect for the specified `signum'.  You can save this value and
   restore it later by calling `SetHandler' again.
   
   On failure the value `handlerError' is returned.  Possible errors are an
   invalid `signum', or an attempt to ignore or provide a handler for the
   signals `SIGKILL' or `SIGSTOP'.
   
   Note: This function is just a wrapper around the C function `signal'.  For 
   more details check the specification of this function (e.g. its man page or
   the relevant chapter of libc info).  *)

PROCEDURE Raise* (signum: SigNumber);
(* Raises a signal associated with `signum' for the current process.  See 
   `SetHandler' for the restrictions regarding the values of `signum'.  *)

END Signal.
