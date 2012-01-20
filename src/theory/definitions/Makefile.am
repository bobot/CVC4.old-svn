AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libdefinitions.la

libdefinitions_la_SOURCES = \
	theory_definitions.h \
	theory_definitions.cpp

EXTRA_DIST =
