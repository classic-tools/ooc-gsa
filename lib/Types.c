/* low level interface to the type descriptor mechanism. */
#include "Types.h"
#include "__StdTypes.h"
#include "__Descr.h"
#include "__config.h"
#include "__libc.h"


/* number of bytes between start of memory block and start of user defined
   data: */
#define OFFSET_PTR 8


static _ModId _mid;

/* module descriptor */
static const struct {
  int length;
  void* pad;
  const char name[6];
} _n0 = {6, NULL, {"Types"}};
static struct _MD Types_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL
  }
};


Types__Type Types_BaseOf (Types__Type t, INTEGER level) {
  if ((0 <= level) && (level <= t->level)) {
    return t->btypes[level];
  } else {
    return NULL;
  }
}

INTEGER Types_LevelOf (Types__Type t) {
  return t->level;
}

void Types_NewObj (PTR (* o), Types__Type t) {
  char* mem = GC_malloc(t->size+OFFSET_PTR);
  char* var = mem+OFFSET_PTR;

#if !USE_GC
  (void)memset((void*)mem, 0, t->size+OFFSET_PTR);
#endif
  ((Types__Type*)var)[-1] = t;
  *o = var;
}

Types__Type Types_This (Kernel__Module mod, const CHAR *name) {
  Types__Type td = (Types__Type)mod->tdescs;
  while (td) {
    if (!strcmp((const char*)name, (const char*)td->name)) {
      return td;
    }
    td = td->next;
  };
  return NULL;
}

Types__Type Types_TypeOf (PTR o) {
  return ((Types__Type*)o)[-1];
}

void Types_init (void) {
  _mid = _register_module (&Types_md.md, NULL);
}


