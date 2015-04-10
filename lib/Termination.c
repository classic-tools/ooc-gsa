/*	$Id: Termination.c,v 1.9 2000/09/23 11:55:49 ooc-devel Exp $	*/
/*  Provides procedures for program finalization.
    Copyright (C) 1997, 1999, 2000  Michael van Acken

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
#include <stddef.h>
#include <stdlib.h>
#include <signal.h>
#include <sys/types.h>

#include "__oo2c.h"
#include "__mini_gc.h"
#include "__StdTypes.h"
#include "__config.h"

#if HAVE_UNISTD_H
#include <unistd.h>
#elif HAVE_IO_H
#include <io.h>
typedef int ssize_t;
#endif

/* --- begin #include "Termination.d" */
#include "Termination.h"

/* local definitions */

/* function prototypes */

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const char name[12];
} _n0 = {12, NULL, {"Termination"}};
static struct _MD Termination_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL
  }
};

/* local strings */

/* --- end #include "Termination.d" */


#if !HAVE_ATEXIT  /* assume this is a SunOS 4, use on_exit instead */
#ifdef __cplusplus
extern "C" int on_exit(void (*procp)(void),void* arg);
#else
extern int on_exit(void (*procp)(void),void* arg);
#endif
#endif

static Termination__Proc *proc_list = NULL;
static unsigned int proc_count = 0;
static unsigned int max_proc_count = 0;
static volatile int /*sig_atomic_t*/ noSignalHandlerInProgress = 1;
static _ModId _mid;

void Termination__RegisterProc(Termination__Proc proc) {
  int i;
  
  if (proc_count == 0) {
    max_proc_count = 32;
    proc_list = GC_malloc(sizeof(Termination__Proc)*max_proc_count);
    for (i=0; i<max_proc_count; i++) {
      proc_list[i] = (Termination__Proc)NULL;
    }
  } else if (proc_count == max_proc_count) {
    static Termination__Proc *new;

    max_proc_count += 32;
    new = GC_malloc(sizeof(Termination__Proc)*max_proc_count);
    for (i=0; i<proc_count; i++) {
      new[i] = proc_list[i];
    }
    for (i=proc_count; i<max_proc_count; i++) {
      new[i] = (Termination__Proc)NULL;
    }
    proc_list = new;
  }
  
  proc_list[proc_count] = proc;
  proc_count++;
}

void Termination__UnregisterProc(Termination__Proc proc) {
  int i, j;

  i = proc_count;
  while (i != 0) {
    i--;
    if (proc_list[i] == proc) {
      j = i+1;
      while (j != proc_count) {
	proc_list[j-1] = proc_list[j];
	j++;
      }
      proc_count--;
      return;
    }
  }
}


static void run_term_procs (void) {
  int i;
  Termination__Proc ptr;

  i = proc_count;
  while (i != 0) {
    i--;
    ptr = proc_list[i];
    if (ptr) {
      proc_list[i] = (Termination__Proc)NULL;
      (*ptr)();
    }
  }
}

static RETSIGTYPE signal_handler (int sig) {
  signal(sig, SIG_DFL);  /* install default handler, necessary for SunOS 4 */
  if (noSignalHandlerInProgress) {
    noSignalHandlerInProgress = 0;
    run_term_procs();
  }
#if HAVE_RAISE
  raise(sig);
#else
  (void)kill(getpid(), sig);	/* raise signal to call default handler */
#endif
}

static void catch_signal (int sig) {
  void (*func)(int); 

  func = signal (sig, signal_handler);
  if (func == SIG_IGN) {
    signal (sig, SIG_IGN);
  }
}

void Termination_init(void) {
  _mid = _register_module(&Termination_md.md, NULL);
  _exception_run_term_procs = run_term_procs;
  
  /* error signals */
  catch_signal(SIGFPE);
  catch_signal(SIGILL);
  catch_signal(SIGSEGV);
  catch_signal(SIGABRT);
#ifdef SIGBUS
  catch_signal(SIGBUS);
#endif
#ifdef SIGIOT
  catch_signal(SIGIOT);
#endif
#ifdef SIGSTKFLT
  catch_signal(SIGSTKFLT);
#endif
  
  /* termination signals */
#ifdef SIGHUP
  catch_signal(SIGHUP);
#endif
  catch_signal(SIGINT);
#ifdef SIGQUIT
  catch_signal(SIGQUIT);
#endif
  catch_signal(SIGTERM);
  
  /* normal program exit */
#if HAVE_ATEXIT
  (void)atexit(&run_term_procs);
#else
  (void)on_exit(&run_term_procs,NULL);
#endif
}
