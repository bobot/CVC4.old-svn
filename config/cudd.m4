# CVC4_CHECK_CUDD
# ---------
# Check for CUDD libraries and headers.  Complicated because different
# packagers have packaged it differently.
AC_DEFUN([CVC4_CHECK_CUDD], [
CUDD_CPPFLAGS=
CUDD_LDFLAGS=
CUDD_LIBS=
cvc4cudd=no
AC_MSG_CHECKING([whether user requested CUDD support])
AC_ARG_WITH([cudd],
  [AS_HELP_STRING([--with-cudd], [force linking/not linking against CUDD])],
  [with_cudd_set=yes],
  [with_cudd=check; with_cudd_set=no])
AC_ARG_WITH([cudd-dir],
  [AS_HELP_STRING([--with-cudd-dir=DIR], [path to cudd installation])],
  [CUDD_DIR="$withval"],
  [if test "$with_cudd_set" = yes -a "$with_cudd" != yes -a "$with_cudd" != no -a "$with_cudd" != check; then
     dnl maybe the user gave --with-cudd=DIR ?
     CUDD_DIR="$with_cudd"
     with_cudd=yes
   fi])
if test -n "$CUDD_DIR" -a "$with_cudd_set" = no; then
  dnl if --with-cudd-dir or CUDD_DIR given, force --with-cudd
  dnl unless --with-cudd=... given explicitly
  with_cudd=yes
fi
if test "$with_cudd" = no; then
  AC_MSG_RESULT([no, CUDD disabled by user])
else
  if test "$with_cudd" = check; then
    AC_MSG_RESULT([no preference by user, will auto-detect])
  else
    AC_MSG_RESULT([yes, CUDD enabled by user])
  fi
  if test -z "$CUDD_DIR"; then
    dnl default location if unspecified
    CUDD_DIR=/usr
  fi
  AC_MSG_CHECKING([for C++ cudd includes under $CUDD_DIR])
  result="not found"
  cvc4save_CPPFLAGS="$CPPFLAGS"
  AC_LANG_PUSH([C++])
  for cuddinc in "$CUDD_DIR/include" "$CUDD_DIR/include/cudd" "$CUDD_DIR"; do
    CPPFLAGS="$cvc4save_CPPFLAGS -I$cuddinc"
    AC_COMPILE_IFELSE(
      [AC_LANG_PROGRAM([
#include <stdio.h>
#include "cuddObj.hh"],
         [Cudd c;])],
      [ CUDD_CPPFLAGS="-I$cuddinc"
        result="$cuddinc"
        cvc4cudd=yes
        break
      ])
  done
  CPPFLAGS="$cvc4save_CPPFLAGS"
  AC_MSG_RESULT([$result])
  if test $cvc4cudd = yes; then
    AC_MSG_CHECKING([for C++ cudd libraries under $CUDD_DIR])
    cvc4cudd=no
    result="not found"
    cvc4save_CPPFLAGS="$CPPFLAGS"
    CPPFLAGS="$CPPFLAGS $CUDD_CPPFLAGS"
    cvc4save_LDFLAGS="$LDFLAGS"
    cvc4save_LIBS="$LIBS"
    dnl This is messy.  We try to find Fedora packages, Debian packages, and
    dnl a built CUDD source directory.  We can't -lutil or -lst because these
    dnl names of CUDD libraries conflict with other libraries commonly
    dnl installed.  So we fall back to naming them directly.  The CUDD
    dnl sources build static libs only, so we go with that.
    for cuddlibdirs in "-L$CUDD_DIR/lib" "-L$CUDD_DIR/lib/cudd" "-L$CUDD_DIR" \
        "-L$CUDD_DIR/obj -L$CUDD_DIR/cudd -L$CUDD_DIR/mtr -L$CUDD_DIR/epd -L$CUDD_DIR/st"; do
      for cuddlibs in -lcuddxx -lcuddobj "-lobj -lcudd $CUDD_DIR/util/libutil.a $CUDD_DIR/st/libst.a -lepd -lmtr"; do
        LDFLAGS="$cvc4save_LDFLAGS $cuddlibdirs"
        LIBS="$cvc4save_LIBS $cuddlibs"
        AC_LINK_IFELSE(
          [AC_LANG_PROGRAM([
#include <stdio.h>
#include "cuddObj.hh"],
             [Cudd c;])],
          [ CUDD_LDFLAGS="$cuddlibdirs"
            CUDD_LIBS="$cuddlibs"
            result="$cuddlibdirs"
            cvc4cudd=yes
            break
          ])
      done
    done
    CPPFLAGS="$cvc4save_CPPFLAGS"
    LDFLAGS="$cvc4save_LDFLAGS"
    LIBS="$cvc4save_LIBS"
    AC_MSG_RESULT([$result]);
    if test $cvc4cudd = yes; then
      AC_DEFINE_UNQUOTED(CVC4_CUDD, [], [Defined if using the CU Decision Diagram package (cudd).])
    fi
  fi
  AC_LANG_POP([C++])
fi
AC_SUBST([CUDD_CPPFLAGS])
AC_SUBST([CUDD_LDFLAGS])
AC_SUBST([CUDD_LIBS])

if test "$with_cudd" = yes -a "$cvc4cudd" = no; then
  AC_ERROR([--with-cudd was given, but cudd not available])
fi
])# CVC4_CHECK_CUDD
