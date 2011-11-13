AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -I@srcdir@/minisat
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = minisat

noinst_LTLIBRARIES = libprop.la

libprop_la_SOURCES = \
	prop_engine.cpp \
	prop_engine.h \
	sat.h \
	sat.cpp \
	cnf_stream.h \
	cnf_stream.cpp

nodist_libprop_la_SOURCES = \
	options.cpp \
	options.h

BUILT_SOURCES = \
	options.cpp \
	options.h

EXTRA_DIST = \
	options

options:;
options.h options.cpp: @top_srcdir@/src/options/base_options_template.h @top_srcdir@/src/options/base_options_template.cpp @top_srcdir@/src/options/mkoptions options
	$(MAKE) -C @top_srcdir@/src/options builts
