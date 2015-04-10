/*	$Id: LocStrings.c,v 1.3 2000/09/23 19:40:42 ooc-devel Exp $	*/
#include "__oo2c.h"
#include "__libc.h"

/* --- begin #include "LocStrings.d" */
#include "LocStrings.h"

/* local definitions */

/* function prototypes */

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const char name[11];
} _n0 = {11, NULL, {"LocStrings"}};
static struct _MD LocStrings_md = {
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

/* --- end #include "LocStrings.d" */
static _ModId _mid;

OOC_CHAR LocStrings__IsAlpha(OOC_CHAR ch) {
  return (OOC_CHAR) isalpha((int)ch) != 0;
}

OOC_CHAR LocStrings__IsAlphaNumeric(OOC_CHAR ch) {
  return (OOC_CHAR)isalnum((int)ch) != 0;
}

OOC_CHAR LocStrings__IsControl(OOC_CHAR ch) {
  return (OOC_CHAR)iscntrl((int)ch) != 0;
}

OOC_CHAR LocStrings__IsDigit(OOC_CHAR ch) {
  return (OOC_CHAR)isdigit((int)ch) != 0;
}

OOC_CHAR LocStrings__IsGraphic(OOC_CHAR ch) {
  return (OOC_CHAR)isgraph((int)ch) != 0;
}

OOC_CHAR LocStrings__IsPrintable(OOC_CHAR ch) {
  return (OOC_CHAR)isprint((int)ch) != 0;
}

OOC_CHAR LocStrings__IsLower(OOC_CHAR ch) {
  return (OOC_CHAR)islower((int)ch) != 0;
}

OOC_CHAR LocStrings__IsPunctuation(OOC_CHAR ch) {
  return (OOC_CHAR)ispunct((int)ch) != 0;
}

OOC_CHAR LocStrings__IsSpace(OOC_CHAR ch) {
  return (OOC_CHAR)isspace((int)ch) != 0;
}

OOC_CHAR LocStrings__IsUpper(OOC_CHAR ch) {
  return (OOC_CHAR)isupper((int)ch) != 0;
}

OOC_CHAR LocStrings__ToUpper(OOC_CHAR ch) {
  return (int)toupper((int)ch);
}

OOC_CHAR LocStrings__ToLower(OOC_CHAR ch) {
  return (int)tolower((int)ch);
}

SHORTINT LocStrings__Cmp(const OOC_CHAR* s1__ref, int s1_0d, const OOC_CHAR* s2__ref, int s2_0d) {
  register int i0;
  i0 = strcoll(s1__ref, s2__ref);
  if (i0<0) return -1;
  else if (i0>0) return 1;
  else return 0;
}

OOC_BOOLEAN LocStrings__Equal(const OOC_CHAR* s1__ref, int s1_0d, const OOC_CHAR* s2__ref, int s2_0d) {
  return strcoll(s1__ref, s2__ref) == 0;
}

void LocStrings__Capitalize(OOC_CHAR* s1, int s1_0d) {
  register int i0 = 0;
  while (s1[i0] != 0) {
    s1[i0]=toupper((int)s1[i0]); i0++;
  }
}

void LocStrings_init(void) {
  _mid = _register_module(&LocStrings_md.md, NULL);
}
