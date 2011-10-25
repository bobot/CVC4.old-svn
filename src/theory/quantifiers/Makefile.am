AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libquantifiers.la

libquantifiers_la_SOURCES = \
	theory_quantifiers_type_rules.h \
	theory_quantifiers.h \
	quantifiers_rewriter.h \
	theory_quantifiers.cpp \
	theory_quantifiers_instantiator.h \
	theory_quantifiers_instantiator.cpp

EXTRA_DIST = kinds