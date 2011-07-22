# LIBCVC4COMPAT_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4COMPAT_VERSION = @CVC4_COMPAT_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4COMPATLIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

if CVC4_BUILD_LIBCOMPAT

nobase_lib_LTLIBRARIES = libcvc4compat.la
noinst_LTLIBRARIES = libcvc4compat_noinst.la

libcvc4compat_la_LDFLAGS = $(ANTLR_LDFLAGS) \
	-version-info $(LIBCVC4COMPAT_VERSION)
libcvc4compat_noinst_la_LDFLAGS = $(ANTLR_LDFLAGS)

libcvc4compat_la_LIBADD = \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../lib/libreplacements.la
libcvc4compat_noinst_la_LIBADD = \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../lib/libreplacements.la

libcvc4compat_la_SOURCES = \
	cvc3_compat.h \
	cvc3_compat.cpp

libcvc4compat_noinst_la_SOURCES = \
	cvc3_compat.h \
	cvc3_compat.cpp

include_HEADERS = \
	cvc3_compat.h

else

EXTRA_DIST = \
	cvc3_compat.h \
	cvc3_compat.cpp

endif
