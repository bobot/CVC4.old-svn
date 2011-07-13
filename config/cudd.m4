# CVC4_CHECK_CUDD
# ---------
# Check for CUDD libraries and headers.  Complicated because different
# packagers have packaged it differently.
AC_DEFUN([CVC4_CHECK_CUDD], [
CUDD_CPPFLAGS=
CUDD_LDFLAGS=
cvc4cudd=no
AC_MSG_CHECKING([whether user requested CUDD support])
AC_ARG_WITH([cudd], [AS_HELP_STRING([--with-cudd], [force linking/not linking against CUDD])], [], [with_cudd=check])
if test "$with_cudd" = no; then
  AC_MSG_RESULT([no, CUDD disabled by user])
else
  if test "$with_cudd" = check; then
    AC_MSG_RESULT([no preference by user, will auto-detect])
  else
    AC_MSG_RESULT([yes, CUDD enabled by user])
  fi
  AC_ARG_WITH([cudd-dir],
    [AS_HELP_STRING([--with-cudd-dir=DIR], [path to cudd installation])],
    [CUDD_DIR="$withval"])
  if test -z "$CUDD_DIR"; then
    CUDD_DIR=/usr
  fi
  AC_MSG_CHECKING([for cudd includes under $CUDD_DIR])
  result="not found"
  for cuddinc in "$CUDD_DIR/include" "$CUDD_DIR/include/cudd" "$CUDD_DIR"; do
    if test -r "$cuddinc/cudd.h"; then
      dnl TODO - should do a TRY_COMPILE instead
      CUDD_CPPFLAGS="\"-I$cuddinc\""
      result="$cuddinc"
      cvc4cudd=yes
      break
    fi
  done
  AC_MSG_RESULT([$result])
  if test $cvc4cudd = yes; then
    AC_MSG_CHECKING([for cudd libraries under $CUDD_DIR])
    cvc4cudd=no
    result="not found"
    for cuddlib in "$CUDD_DIR/lib" "$CUDD_DIR/lib/cudd" "$CUDD_DIR"; do
      if test -r "$cuddlib/libcuddxx.la"; then
        dnl TODO - should do a TRY_LINK instead, that has the extra benefit
        dnl of making sure both shared & static work
        CUDD_LDFLAGS="\"-L$cuddlib\" -lcuddxx"
        result="$cuddlib"
        cvc4cudd=yes
        break
      fi
    done
    AC_MSG_RESULT([$result]);
    if test $cvc4cudd = yes; then
      AC_DEFINE_UNQUOTED(CVC4_CUDD, [], [Defined if using the CU Decision Diagram package (cudd).])
    fi
  fi
fi
AC_SUBST([CUDD_CPPFLAGS])
AC_SUBST([CUDD_LDFLAGS])

if test "$with_cudd" = yes -a "$cvc4cudd" = no; then
  AC_ERROR([--with-cudd was given, but cudd not available])
fi
])# CVC4_CHECK_CUDD
