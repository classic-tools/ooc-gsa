/*	$Id: LocStrings.c,v 1.2 1999/06/03 12:12:32 acken Exp $	*/
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

CHAR LocStrings__IsAlpha(CHAR ch) {
  return (CHAR) isalpha((int)ch) != 0;
}

CHAR LocStrings__IsAlphaNumeric(CHAR ch) {
  return (CHAR)isalnum((int)ch) != 0;
}

CHAR LocStrings__IsControl(CHAR ch) {
  return (CHAR)iscntrl((int)ch) != 0;
}

CHAR LocStrings__IsDigit(CHAR ch) {
  return (CHAR)isdigit((int)ch) != 0;
}

CHAR LocStrings__IsGraphic(CHAR ch) {
  return (CHAR)isgraph((int)ch) != 0;
}

CHAR LocStrings__IsPrintable(CHAR ch) {
  return (CHAR)isprint((int)ch) != 0;
}

CHAR LocStrings__IsLower(CHAR ch) {
  return (CHAR)islower((int)ch) != 0;
}

CHAR LocStrings__IsPunctuation(CHAR ch) {
  return (CHAR)ispunct((int)ch) != 0;
}

CHAR LocStrings__IsSpace(CHAR ch) {
  return (CHAR)isspace((int)ch) != 0;
}

CHAR LocStrings__IsUpper(CHAR ch) {
  return (CHAR)isupper((int)ch) != 0;
}

CHAR LocStrings__ToUpper(CHAR ch) {
  return (int)toupper((int)ch);
}

CHAR LocStrings__ToLower(CHAR ch) {
  return (int)tolower((int)ch);
}

SHORTINT LocStrings__Cmp(const CHAR* s1__ref, int s1_0d, const CHAR* s2__ref, int s2_0d) {
  register int i0;
  i0 = strcoll(s1__ref, s2__ref);
  if (i0<0) return -1;
  else if (i0>0) return 1;
  else return 0;
}

BOOLEAN LocStrings__Equal(const CHAR* s1__ref, int s1_0d, const CHAR* s2__ref, int s2_0d) {
  return strcoll(s1__ref, s2__ref) == 0;
}

void LocStrings__Capitalize(CHAR* s1, int s1_0d) {
  register int i0 = 0;
  while (s1[i0] != 0) {
    s1[i0]=toupper((int)s1[i0]); i0++;
  }
}

void LocStrings_init(void) {
  _mid = _register_module(&LocStrings_md.md, NULL);
}
