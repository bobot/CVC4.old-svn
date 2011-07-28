# CVC4_AC_INIT
# ------------
# Do early initialization/diversion of autoconf things for CVC4 build process.
AC_DEFUN([CVC4_AC_INIT],
dnl _AS_ME_PREPARE
[CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE
])# CVC4_AC_INIT


# CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE
# -----------------------------------
# Rewrite (e.g.) "./configure debug" to "./configure --with-build=debug"
AC_DEFUN([CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE],
[m4_divert_push([PARSE_ARGS])dnl

unset ac_cvc4_rewritten_args
for ac_option
do
  case $ac_option in
    -*|*=*) ;;
    production|production-*|debug|debug-*|default|default-*|competition|competition-*)
      # regexp `\?' not supported on Mac OS X
      ac_option_build=`expr "$ac_option" : '\([[^-]]*\)-\{0,1\}'`
      ac_cvc4_build_profile_set=yes
      as_me=configure
      AC_MSG_NOTICE([CVC4: building profile $ac_option_build])
      for x in optimized statistics replay assertions tracing dumping muzzle coverage profiling; do
        if expr "$ac_option" : '.*-no'$x'$' >/dev/null || expr "$ac_option" : '.*-no'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'$' >/dev/null || expr "$ac_option" : '.*-'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-$x\""'
        fi
      done
      if expr "$ac_option" : '.*-nostaticbinary$' >/dev/null || expr "$ac_option" : '.*-nostaticbinary-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-staticbinary$' >/dev/null || expr "$ac_option" : '.*-staticbinary-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-nodebugsymbols$' >/dev/null || expr "$ac_option" : '.*-nodebugsymbols-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-debug-symbols\""'
      fi
      if expr "$ac_option" : '.*-debugsymbols$' >/dev/null || expr "$ac_option" : '.*-debugsymbols-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-debug-symbols\""'
      fi
      for x in cln gmp; do
        if expr "$ac_option" : '.*-no'$x'$' >/dev/null || expr "$ac_option" : '.*-no'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--without-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'$' >/dev/null || expr "$ac_option" : '.*-'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--with-$x\""'
        fi
      done
      ac_option="--with-build=$ac_option_build"
  esac
  eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"$ac_option\""'
done
eval set x $ac_cvc4_rewritten_args
shift
dnl echo "args are now:" "${@}"
m4_divert_pop([PARSE_ARGS])dnl
])# CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE


# CVC4_COPY_IF_CHANGED(FROM, TO)
# ------------------------------
# Copy file FROM to TO, if they have textual differences.
AC_DEFUN([CVC4_COPY_IF_CHANGED], [
if diff -q "$1" "$2" >/dev/null 2>&1; then
  dnl they are the same
  :
else
  dnl they are different
  cp "$1" "$2"
fi
])# CVC4_COPY_IF_CHANGED


# CVC4_CONFIG_FILE_ONLY_IF_CHANGED(FILE)
# --------------------------------------
# Run AC_CONFIG_FILES to generate file named in the argument, but if it
# exists already, only replace it if it would be changed (this preserves
# the old timestamp if no textual changes are to be made to the file).
AC_DEFUN([CVC4_CONFIG_FILE_ONLY_IF_CHANGED], [
AC_CONFIG_FILES([$1.tmp:$1.in],
                CVC4_COPY_IF_CHANGED([$1.tmp],[$1]))
])# CVC4_CONFIG_FILE_ONLY_IF_CHANGED
