AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libuf.la

libuf_la_SOURCES = \
	theory_uf.h \
	theory_uf.cpp \
	theory_uf_type_rules.h \
	theory_uf_rewriter.h \
	equality_engine.h \
	equality_engine_impl.h \
	symmetry_breaker.h \
	symmetry_breaker.cpp

nodist_libuf_la_SOURCES = \
	options.cpp \
	options.h

BUILT_SOURCES = \
	options.cpp \
	options.h

EXTRA_DIST = \
	kinds \
	options

options:;
options.h options.cpp: @top_srcdir@/src/options/base_options_template.h @top_srcdir@/src/options/base_options_template.cpp @top_srcdir@/src/options/mkoptions options
	$(MAKE) -C @top_srcdir@/src/options builts
