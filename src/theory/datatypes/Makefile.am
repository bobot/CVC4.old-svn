AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libdatatypes.la

libdatatypes_la_SOURCES = \
	theory_datatypes_type_rules.h \
	theory_datatypes.h \
	datatypes_rewriter.h \
	theory_datatypes.cpp \
	union_find.h \
	union_find.cpp \
	explanation_manager.h \
	explanation_manager.cpp

nodist_libdatatypes_la_SOURCES = \
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
