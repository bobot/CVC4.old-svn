AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

bin_PROGRAMS = cvc4
noinst_LIBRARIES = libmain.a

libmain_a_SOURCES = \
	interactive_shell.h \
	interactive_shell.cpp \
	main.h \
	main.cpp \
	util.cpp

nodist_libmain_a_SOURCES = \
	options.cpp \
	options.h

cvc4_SOURCES =
cvc4_LDADD = \
	libmain.a \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../libcvc4.la \
	@builddir@/../lib/libreplacements.la \
	$(READLINE_LIBS)

BUILT_SOURCES = \
	$(TOKENS_FILES) \
	options.cpp \
	options.h

TOKENS_FILES = \
	cvc_tokens.h \
	smt_tokens.h \
	smt2_tokens.h

cvc_tokens.h: @srcdir@/../parser/cvc/Cvc.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]*\)'\''.*/"\1",/' | sort -u >$@
smt_tokens.h: @srcdir@/../parser/smt/Smt.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]*\)'\''.*/"\1",/' | sort -u >$@
smt2_tokens.h: @srcdir@/../parser/smt2/Smt2.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]*\)'\''.*/"\1",/' | sort -u >$@

options:;
options.h options.cpp: @top_srcdir@/src/options/base_options_template.h @top_srcdir@/src/options/base_options_template.cpp @top_srcdir@/src/options/mkoptions options
	$(MAKE) -C @top_srcdir@/src/options builts

EXTRA_DIST = \
	options

clean-local:
	rm -f $(BUILT_SOURCES)

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static
else
cvc4_LINK = $(CXXLINK)
endif
