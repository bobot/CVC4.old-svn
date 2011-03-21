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

## Uncomment following lines if you want cvc4 to point to single-threaded
# cvc4_SOURCES = main.cpp
# cvc4_LDADD = \
# 	libmain.a \
# 	../parser/libcvc4parser.la \
# 	../libcvc4.la \
# 	../lib/libreplacements.la

# if STATIC_BINARY
# cvc4_LINK = $(CXXLINK) -all-static
# else
# cvc4_LINK = $(CXXLINK)
# endif

# pcvc4_SOURCES = main_portfolio.cpp driver_portfolio.cpp
# pcvc4_LDADD = \
# 	libmain.a \
# 	../parser/libcvc4parser.la \
# 	../libcvc4.la \
# 	../lib/libreplacements.la

# if STATIC_BINARY
# pcvc4_LINK = $(CXXLINK) -all-static
# else
# pcvc4_LINK = $(CXXLINK)
# endif


## And these one if you want to call cvc4 to point to multi-threaded
if CVC4_HAS_THREADS
bin_PROGRAMS += pcvc4
pcvc4_SOURCES = main_portfolio.cpp driver_portfolio.cpp
pcvc4_LDADD = \
	libmain.a \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la
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
	../lib/libreplacements.la

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static
else
cvc4_LINK = $(CXXLINK)
endif

