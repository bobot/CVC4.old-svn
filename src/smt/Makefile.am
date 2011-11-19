AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsmt.la

libsmt_la_SOURCES = \
	smt_engine.cpp \
	smt_engine.h \
	modal_exception.h \
	bad_option_exception.h \
	no_such_function_exception.h

nodist_libsmt_la_SOURCES = \
	smt_options.cpp

BUILT_SOURCES = \
	smt_options.cpp

EXTRA_DIST = \
	bad_option_exception.i \
	no_such_function_exception.i \
	modal_exception.i \
	smt_engine.i \
	options

smt_options.cpp: smt_options_template.cpp @top_srcdir@/src/options/mkoptions @top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options
	$(AM_V_at)chmod +x @top_srcdir@/src/options/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@top_srcdir@/src/options/mkoptions \
		$< $@ \
		@top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options \
	) || (rm -f $@ && exit 1)

