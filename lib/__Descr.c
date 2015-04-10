/*	$Id: __Descr.c,v 1.6 2000/09/23 19:40:47 ooc-devel Exp $	*/
/* this file is included into __oo2c.c */

/*  Low-level functions to manage module and type descriptors.
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
*/

/* module descriptor `Kernel' and type descriptor `Kernel.ModuleDesc': */
static struct {
  int length;
  void* pad;
  const char name[7];
} _n0 = {7, NULL, {"Kernel"}};
struct _MD Kernel__md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const OOC_CHAR*)_n0.name, 
    -1, 
    NULL
  }
};
static struct {
  int length;
  void* pad;
  const char name[11];
} _n1 = {11, NULL, {"ModuleDesc"}};
struct _TD Kernel__ModuleDesc_td = {
  NULL, 
  &Types__TypeDesc_td.td, 
  {
    NULL, 
    NULL, 
    (const OOC_CHAR*)_n1.name, 
    &Kernel__md.md, 
    0, 
    '0', '1', 
    sizeof(struct _ModuleDesc), 
    NULL
  }
};

/* module descriptor `Types' and type descriptor `Types.TypeDesc': */
static struct {
  int length;
  void* pad;
  const char name[6];
} _n2 = {6, NULL, {"Types"}};
struct _MD Types__md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const OOC_CHAR*)_n2.name, 
    -1, 
    NULL
  }
};
static struct {
  int length;
  void* pad;
  const char name[9];
} _n3 = {9, NULL, {"TypeDesc"}};
struct _TD Types__TypeDesc_td = {
  NULL, 
  &Types__TypeDesc_td.td, 
  {
    NULL, 
    NULL, 
    (const OOC_CHAR*)_n3.name, 
    &Types__md.md, 
    0, 
    '0', '1', 
    sizeof(struct _TypeDesc), 
    NULL
  }
};



/* --- functions to manage modules: */
_Module _program_modules = NULL;
static _ModId module_count = 0;

_ModId _register_module (_Module m, const _Type tdescs) {
  m->key = module_count;
  m->tdescs = tdescs;
  m->next = _program_modules;
  _program_modules = m;
  module_count++;
  return m->key;
}

_Module _get_module (_ModId key) {
  _Module m;

  m = _program_modules;
  while ((m != NULL) && (m->key != key)) {
    m = m->next;
  };
  return m;
}
