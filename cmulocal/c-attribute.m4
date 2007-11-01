dnl
dnl $Id: c-attribute.m4,v 1.3.10.1 2007/11/01 14:39:29 murch Exp $
dnl

dnl
dnl Test for __attribute__
dnl

AC_DEFUN([CMU_C___ATTRIBUTE__], [
AC_MSG_CHECKING(for __attribute__)
AC_CACHE_VAL(ac_cv___attribute__, [
AC_TRY_COMPILE([
#include <stdlib.h>
static void foo(void) __attribute__ ((noreturn));

static void
foo(void)
{
  exit(1);
}
],
[
],
ac_cv___attribute__=yes,
ac_cv___attribute__=no)])
if test "$ac_cv___attribute__" = "yes"; then
  AC_DEFINE(HAVE___ATTRIBUTE__, 1, [define if your compiler has __attribute__])
fi
AC_MSG_RESULT($ac_cv___attribute__)
])

