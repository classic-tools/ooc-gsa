/* $Id: Signal.c,v 1.12 2000/09/23 19:40:45 ooc-devel Exp $ */
/*  Signal handling facilities.
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
#include <signal.h>
#include <string.h>
#include <stdio.h>
#include <sys/types.h>

#include "__oo2c.h"
#include "__config.h"
#include "Signal.h"

#if HAVE_UNISTD_H
#include <unistd.h>
#elif HAVE_IO_H
#include <io.h>
#endif

Exception__Source Signal__exception;
Signal__SigHandler Signal__handlerDefault;
Signal__SigHandler Signal__handlerIgnore;
Signal__SigHandler Signal__handlerException;
Signal__SigHandler Signal__handlerError;


Signal__SigNumber Signal__Map (Signal__SigNumber signum) {
  switch (signum) {
  case Signal__sigfpe:
#ifdef SIGFPE
    return SIGFPE;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigill:
#ifdef SIGILL
    return SIGILL;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigsegv:
#ifdef SIGSEGV
    return SIGSEGV;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigbus:
#ifdef SIGBUS
    return SIGBUS;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigabrt:
#ifdef SIGABRT
    return SIGABRT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigiot:
#ifdef SIGIOT
    return SIGIOT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigtrap:
#ifdef SIGTRAP
    return SIGTRAP;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigemt:
#ifdef SIGEMT
    return SIGEMT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigsys:
#ifdef SIGSYS
    return SIGSYS;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigstkflt:
#ifdef SIGSTKFLT
    return SIGSTKFLT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigterm:
#ifdef SIGTERM
    return SIGTERM;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigint:
#ifdef SIGINT
    return SIGINT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigquit:
#ifdef SIGQUIT
    return SIGQUIT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigkill:
#ifdef SIGKILL
    return SIGKILL;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sighup:
#ifdef SIGHUP
    return SIGHUP;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigalrm:
#ifdef SIGALRM
    return SIGALRM;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigvtalrm:
#ifdef SIGVTALRM
    return SIGVTALRM;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigio:
#ifdef SIGIO
    return SIGIO;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigurg:
#ifdef SIGURG
    return SIGURG;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigpoll:
#ifdef SIGPOLL
    return SIGPOLL;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigchld:
#ifdef SIGCHLD
    return SIGCHLD;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigcld:
#ifdef SIGCLD
    return SIGCLD;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigcont:
#ifdef SIGCONT
    return SIGCONT;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigstop:
#ifdef SIGSTOP
    return SIGSTOP;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigtstp:
#ifdef SIGTSTP
    return SIGTSTP;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigttin:
#ifdef SIGTTIN
    return SIGTTIN;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigttou:
#ifdef SIGTTOU
    return SIGTTOU;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigpipe:
#ifdef SIGPIPE
    return SIGPIPE;
#else
    return Signal__unknownSignal;
#endif
  case Signal__siglost:
#ifdef SIGLOST
    return SIGLOST;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigxcpu:
#ifdef SIGXCPU
    return SIGXCPU;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigxfsz:
#ifdef SIGXFSZ
    return SIGXFSZ;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigpwr:
#ifdef SIGPWR
    return SIGPWR;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigusr1:
#ifdef SIGUSR1
    return SIGUSR1;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigusr2:
#ifdef SIGUSR2
    return SIGUSR2;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigwinch:
#ifdef SIGWINCH
    return SIGWINCH;
#else
    return Signal__unknownSignal;
#endif
  case Signal__siginfo:
#ifdef SIGINFO
    return SIGINFO;
#else
    return Signal__unknownSignal;
#endif
  case Signal__sigdil:
#ifdef SIGDIL
    return SIGDIL;
#else
    return Signal__unknownSignal;
#endif
  default:
    return Signal__unknownSignal;
  }
}

Signal__SigHandler Signal__SetHandler (Signal__SigNumber signum, Signal__SigHandler action) {
  if (action) {
    return (Signal__SigHandler) signal((int)signum, action);
  } else {
    return (Signal__SigHandler) signal((int)signum, SIG_DFL);
  }
}

static void handle_exception(Signal__SigNumber signum) {
  char str[64];

  (void)signal((int)signum, handle_exception);
  sprintf(str, "[Signal] Caught signal number %i", signum);
  Exception__RAISE(Signal__exception, signum, (OOC_CHAR*)str, strlen(str));
}

void Signal__Raise(Signal__SigNumber signum) {
#if HAVE_RAISE
  raise((int)signum);
#else
  (void)kill(getpid(), (int)signum);
#endif
}

void Signal_init(void) {
  Exception__AllocateSource(&Signal__exception);
  _exception_signal = Signal__exception;
  Signal__handlerDefault = (Signal__SigHandler)SIG_DFL;
  Signal__handlerIgnore = (Signal__SigHandler)SIG_IGN;
  Signal__handlerException = (Signal__SigHandler)(&handle_exception);
  Signal__handlerError = (Signal__SigHandler)SIG_ERR;
}
