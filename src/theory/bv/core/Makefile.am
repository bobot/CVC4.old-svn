AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../../include -I@srcdir@/../../.. -I@builddir@/../../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbvcore.la

libbvcore_la_SOURCES = \
	theory_bv_rewrite_rules_core.h \
	equality_engine.h \
	equality_engine.cpp \
	slice_manager.h \
	cd_set_collection.h \
	cd_list_collection.h \
	watch_manager.h  
