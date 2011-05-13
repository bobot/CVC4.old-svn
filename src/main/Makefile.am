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
	usage.h \
	util.cpp

if CVC4_HAS_THREADS
bin_PROGRAMS += pcvc4
pcvc4_SOURCES = \
	main_portfolio.cpp \
	driver_portfolio.cpp
pcvc4_LDADD = \
	libmain.a \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la \
	$(READLINE_LDFLAGS)
pcvc4_CPPFLAGS = $(AM_CPPFLAGS) $(BOOST_CPPFLAGS)
pcvc4_LDADD += $(BOOST_THREAD_LIBS) -lpthread
pcvc4_LDADD += $(BOOST_THREAD_LDFLAGS)

if STATIC_BINARY
pcvc4_LINK = $(CXXLINK) -all-static
else
pcvc4_LINK = $(CXXLINK)
endif
endif

cvc4_SOURCES = main.cpp driver.cpp
cvc4_LDADD = \
	libmain.a \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la \
	$(READLINE_LDFLAGS)

BUILT_SOURCES = \
	$(TOKENS_FILES)

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

clean-local:
	rm -f $(BUILT_SOURCES)

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static
else
cvc4_LINK = $(CXXLINK)
endif

