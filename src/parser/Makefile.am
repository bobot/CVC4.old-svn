# LIBCVC4PARSER_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4PARSER_VERSION = @CVC4_PARSER_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = smt smt2 cvc

lib_LTLIBRARIES = libcvc4parser.la
if HAVE_CXXTESTGEN
check_LTLIBRARIES = libcvc4parser_noinst.la
endif

libcvc4parser_la_LDFLAGS = $(ANTLR_LDFLAGS) \
	-version-info $(LIBCVC4PARSER_VERSION)
libcvc4parser_noinst_la_LDFLAGS = $(ANTLR_LDFLAGS)

libcvc4parser_la_LIBADD = \
	@builddir@/smt/libparsersmt.la \
	@builddir@/smt2/libparsersmt2.la \
	@builddir@/cvc/libparsercvc.la \
	@builddir@/../lib/libreplacements.la \
	-L@builddir@/.. -lcvc4
libcvc4parser_noinst_la_LIBADD = \
	@builddir@/smt/libparsersmt.la \
	@builddir@/smt2/libparsersmt2.la \
	@builddir@/cvc/libparsercvc.la \
	@builddir@/../lib/libreplacements.la \
	@builddir@/../libcvc4_noinst.la

libcvc4parser_la_SOURCES = \
	antlr_input.h \
	antlr_input.cpp \
	antlr_input_imports.cpp \
	bounded_token_buffer.h \
	bounded_token_buffer.cpp \
	bounded_token_factory.h \
	bounded_token_factory.cpp \
	input.h \
	input.cpp \
	memory_mapped_input_buffer.h \
	memory_mapped_input_buffer.cpp \
	parser.h \
	parser.cpp \
	parser_builder.h \
	parser_builder.cpp \
	parser_exception.h \
	antlr_tracing.h

nodist_libcvc4parser_la_SOURCES = \
	options.cpp \
	options.h

libcvc4parser_noinst_la_SOURCES = \
	antlr_input.h \
	antlr_input.cpp \
	antlr_input_imports.cpp \
	bounded_token_buffer.h \
	bounded_token_buffer.cpp \
	bounded_token_factory.h \
	bounded_token_factory.cpp \
	input.h \
	input.cpp \
	memory_mapped_input_buffer.h \
	memory_mapped_input_buffer.cpp \
	parser.h \
	parser.cpp \
	parser_builder.h \
	parser_builder.cpp \
	parser_exception.h \
	antlr_tracing.h

nodist_libcvc4parser_noinst_la_SOURCES = \
	options.cpp \
	options.h

BUILT_SOURCES = \
	options.cpp \
	options.h

EXTRA_DIST = \
	Makefile.antlr_tracing \
	cvc4parser.i \
	input.i \
	parser_builder.i \
	parser_exception.i \
	parser.i \
	options

options:;
options.h options.cpp: @top_srcdir@/src/options/base_options_template.h @top_srcdir@/src/options/base_options_template.cpp @top_srcdir@/src/options/mkoptions options
	$(MAKE) -C @top_srcdir@/src/options builts
