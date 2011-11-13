AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbv.la

libbv_la_SOURCES = \
	theory_bv.h \
	theory_bv.cpp \
	theory_bv_utils.h \
	theory_bv_rewrite_rules.h \
	theory_bv_rewrite_rules_core.h \
	theory_bv_type_rules.h \
	theory_bv_rewriter.h \
	theory_bv_rewriter.cpp \
	equality_engine.h \
	equality_engine.cpp \
	slice_manager.h \
	cd_set_collection.h 

nodist_libbv_la_SOURCES = \
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
