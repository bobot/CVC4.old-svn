AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libprinter.la

libprinter_la_SOURCES = \
	printer.h \
	printer.cpp \
	ast/ast_printer.h \
	ast/ast_printer.cpp \
	smt/smt_printer.h \
	smt/smt_printer.cpp \
	smt2/smt2_printer.h \
	smt2/smt2_printer.cpp \
	cvc/cvc_printer.h \
	cvc/cvc_printer.cpp

nodist_libprinter_la_SOURCES = \
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
