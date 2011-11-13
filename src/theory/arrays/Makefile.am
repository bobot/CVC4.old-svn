AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarrays.la

libarrays_la_SOURCES = \
	theory_arrays_type_rules.h \
	theory_arrays_rewriter.h \
	theory_arrays.h \
	theory_arrays.cpp \
	union_find.h \
	union_find.cpp \
	array_info.h \
	array_info.cpp \
	static_fact_manager.h \
	static_fact_manager.cpp

nodist_libarrays_la_SOURCES = \
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
