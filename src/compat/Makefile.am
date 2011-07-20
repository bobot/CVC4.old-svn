AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libcompat.la

libcompat_la_SOURCES = \
	cvc3_compat.h \
	cvc3_compat.cpp

include_HEADERS = \
	cvc3_compat.h
