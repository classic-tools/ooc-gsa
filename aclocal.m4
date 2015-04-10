dnl OOC_CHECK_LONG_SIZE_T()
dnl Checks whether size_t is a `long' type, or just unsigned
AC_DEFUN(OOC_CHECK_LONG_SIZE_T,
[AC_REQUIRE([AC_HEADER_STDC])dnl
AC_MSG_CHECKING(whether size_t is long)
AC_CACHE_VAL(ooc_cv_type_long_size_t,
[AC_EGREP_CPP([typedef[^a-z_].*long.*[^a-z_]size_t],
[#include <sys/types.h>
#if STDC_HEADERS
#include <stdlib.h>
#endif], ooc_cv_type_long_size_t=yes, ooc_cv_type_long_size_t=no)])dnl
AC_MSG_RESULT($ooc_cv_type_long_size_t)
if test $ooc_cv_type_long_size_t = no; then
  AC_DEFINE(LOCAL_SIZE_T, unsigned)
else
  AC_DEFINE(LOCAL_SIZE_T, unsigned long)
fi])



dnl OOC_CHECK_INT64_T()
dnl Checks whether a 64 bit int type exists.
AC_DEFUN(OOC_CHECK_INT64_T,
[ooc_int64_t=""
AC_CHECK_SIZEOF(long int,0)
if test $ac_cv_sizeof_long_int = 8; then
  ooc_int64_t="long int"
  ooc_target_long_int="HUGEINT"
  ooc_target_long_set="SYSTEM.SET64"
else
  ooc_target_long_int="LONGINT"
  ooc_target_long_set="SET"
  AC_CHECK_SIZEOF(long long int,0)
  if test $ac_cv_sizeof_long_long_int = 8; then
    ooc_int64_t="long long int"
  fi
fi

if test -z "$ooc_int64_t"; then
  AC_DEFINE_UNQUOTED(LOCAL_INT64_T, long int)
  ooc_target_integer=32
else
  AC_DEFINE_UNQUOTED(LOCAL_INT64_T, $ooc_int64_t)
  ooc_target_integer=64
fi
AC_SUBST(ooc_target_integer)
AC_SUBST(ooc_target_long_int)
AC_SUBST(ooc_target_long_set)
])



dnl OOC_STRUCT_ST_MTIME_USEC()
dnl Defines HAVE_ST_MTIME_USEC if the stat structure has a field st_mtime_usec
AC_DEFUN(OOC_STRUCT_ST_MTIME_USEC,
[AC_CACHE_CHECK([for st_mtime_usec in struct stat], ooc_cv_struct_st_mtime_usec,
[AC_TRY_COMPILE([#include <sys/types.h>
#include <sys/stat.h>], [struct stat s; s.st_mtime_usec;],
ooc_cv_struct_st_mtime_usec=yes, ooc_cv_struct_st_mtime_usec=no)])
if test $ooc_cv_struct_st_mtime_usec = yes; then
  AC_DEFINE(HAVE_ST_MTIME_USEC)
fi
])



dnl OOC_CHECK_SIZEOF_JMP_BUF
dnl Determines the size of the jmp_buf type
AC_DEFUN(OOC_CHECK_SIZEOF_JMP_BUF,
[define(AC_TYPE_NAME, SIZEOF_JMP_BUF)dnl
define(AC_CV_NAME, ooc_cv_sizeof_jmp_buf)dnl
AC_MSG_CHECKING(size of jmp_buf)
AC_CACHE_VAL(AC_CV_NAME,
[AC_TRY_RUN([#include <stdio.h>
#include <setjmp.h>
main()
{
  FILE *f=fopen("conftestval", "w");
  if (!f) exit(1);
  fprintf(f, "%d\n", sizeof(jmp_buf));
  exit(0);
}], AC_CV_NAME=`cat conftestval`, AC_CV_NAME=0)])dnl
AC_MSG_RESULT($AC_CV_NAME)
AC_DEFINE_UNQUOTED(AC_TYPE_NAME, $AC_CV_NAME)
undefine(AC_TYPE_NAME)dnl
undefine(AC_CV_NAME)dnl
])


dnl OOC_CHECK_TARGET_BYTE_ORDER
dnl Determines the byte order of the target machine
AC_DEFUN(OOC_CHECK_TARGET_BYTE_ORDER,
[define(AC_TYPE_NAME, OOC_TARGET_BYTE_ORDER)dnl
define(AC_CV_NAME, ooc_cv_target_byte_order)dnl
AC_MSG_CHECKING(target byte order)
AC_CACHE_VAL(AC_CV_NAME,
[AC_TRY_RUN([#include <stdio.h>
main()
{
  FILE *f=fopen("conftestval", "w");
  int test = 0x04030201;
  char* x = (char*)&test;
  int i;
  if (!f) exit(1);
  for (i=0; i<sizeof(test); i++) { fprintf(f, "%d", x[i]); }
  fprintf(f, "\n");
  exit(0);
}], AC_CV_NAME=`cat conftestval`, AC_CV_NAME=0, AC_CV_NAME=unknown)])dnl
AC_MSG_RESULT($AC_CV_NAME)
AC_DEFINE_UNQUOTED(AC_TYPE_NAME, $AC_CV_NAME)
undefine(AC_TYPE_NAME)dnl
undefine(AC_CV_NAME)dnl
ooc_target_byte_order="$ooc_cv_target_byte_order";
AC_SUBST(ooc_target_byte_order)])



dnl OOC_GEN_PUSHCONTEXT()
dnl Generates a cpp'ed file that will implement the setjmp for PUSHCONTEXT
AC_DEFUN(OOC_GEN_PUSHCONTEXT,
[AC_REQUIRE_CPP()dnl
cat > conftest.$ac_ext <<EOF
[#]line __oline__ "configure"
{
  void **src_ptr = (void**)(_SOURCE_PTR);
#include "confdefs.h"
#include <setjmp.h>
  _SAVE_RVARS
  _push_exception_context (&_local_context);
  if (setjmp(*(jmp_buf*)(&_local_context.jmpbuf)) > 0) {
    extern void* _exception_source;
    _RESTORE_RVARS
    *src_ptr = (void*)_exception_source;
  } else {
    *src_ptr = NULL;
  }
}
EOF
dnl Capture the stderr of cpp.  eval is necessary to expand ac_cpp.
dnl We used to copy stderr to stdout and capture it in a variable, but
dnl that breaks under sh -x, which writes compile commands starting
dnl with ` +' to stderr in eval and subshells.
ac_try="$ac_cpp conftest.$ac_ext >conftest.cpp 2>conftest.out"
AC_TRY_EVAL(ac_try)
ac_err=`grep -v '^ *+' conftest.out`
if test -z "$ac_err"; then
  sed  -e "/^ *$/d" -e "/^#/d" conftest.cpp >lib/__pushcontext.h
  rm -rf conftest*
else
  echo "" >lib/__pushcontext.h
  AC_MSG_WARN("Failed to extract system dependent code for PUSHCONTEXT.")
dnl  AC_MSG_WARN("Calling PUSHCONTEXT will have no effect.")
fi
rm -f conftest*])



dnl OOC_CHECK_EXE_SUFFIX()
dnl Determines the suffix attached to executables.  For an MS-DOS derived OS
dnl this is .exe, and the empty string for Unix.
AC_DEFUN(OOC_CHECK_EXE_SUFFIX,
[AC_MSG_CHECKING(name suffix of executables)
AC_CACHE_VAL(ooc_cv_exe_suffix,
[ooc_cv_exe_suffix=""
AC_TRY_RUN_NATIVE(
  [int main(void) {return 0;}],
  [if test -f conftest.exe; then ooc_cv_exe_suffix=.exe; fi])
])dnl
if test -z "$ooc_cv_exe_suffix"; then
  AC_MSG_RESULT(none)
  ooc_target_os="Unix"
else
  AC_MSG_RESULT($ooc_cv_exe_suffix)
  ooc_target_os="Win32"
fi
exe_suffix="$ooc_cv_exe_suffix";
AC_SUBST(exe_suffix)
AC_SUBST(ooc_target_os)])
