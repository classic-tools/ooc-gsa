/*	$Id: __Descr.h,v 1.9 2001/01/14 14:09:29 ooc-devel Exp $	*/
/*  Low-level functions to manage module and type descriptors.
    Copyright (C) 1997-1999, 2001  Michael van Acken

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
#include "__StdTypes.h"

typedef struct _ModuleDesc* _Module;
typedef struct _TypeDesc* _Type;

typedef struct _ModuleDesc {
  _Module next;
  const OOC_CHAR* name;
  LONGINT key;
  _Type tdescs;
  const void* const* procs;
  const void* const* vars;
  LONGINT fingerprint;
} _ModuleDesc;

typedef struct _TypeDesc {
  const _Type* btypes;
  const void* const* tbprocs;
  const OOC_CHAR* name;
  _Module module;
  INTEGER level;
  char _18pad, _19pad;
  LONGINT size;
  _Type next;
} _TypeDesc;

/* strictly speaking, the `pad' fields are not necessary for 64 bit systems; 
   they only exist to have the record aligned to sizeof(double); they are 
   included for simplicity, although records allocated on the heap omit this
   waste of space on 64 bit systems */ 
struct _MD {
  void* pad;
  _Type tag;
  _ModuleDesc md;
};
struct _TD {
  void* pad;
  _Type tag;
  _TypeDesc td;
};

extern struct _TD Kernel__ModuleDesc_td;
extern struct _TD Types__TypeDesc_td;



/* --- managing modules: */
extern _ModId _register_module (_Module m, const _Type tdescs);
extern _Module _get_module (_ModId key);
