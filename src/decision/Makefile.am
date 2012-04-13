AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -I@srcdir@/minisat -I@srcdir@/bvminisat
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libdecision.la

libdecision_la_SOURCES = \
	decision_engine.h


