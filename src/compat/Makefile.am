AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libcompat.la

libcompat_la_SOURCES = \
	cvc3_compat.h \
	cvc3_compat.cpp

BUILT_SOURCES = \
	$(CVC4_LANGUAGE_BINDINGS:%=cvc3_compat_%.c)

CLEAN_FILES = \
	$(CVC4_LANGUAGE_BINDINGS:%=cvc3_compat_%.c)

cvc3_compat_c.c: cvc3_compat.h
	$(SWIG) -module cvc3 -c++ -o $@ $<
cvc3_compat_c++.c:
 $(patsubst %,cvc3_compat_%.c,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): cvc3_compat_%.c: cvc3_compat.h
	$(SWIG) -module cvc3 -c++ -$(patsubst cvc3_compat_%.c,%,$@) -o $@ $<

include_HEADERS = \
	cvc3_compat.h
