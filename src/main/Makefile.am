AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

## Uncomment following line if you want cvc4 to point to single-threaded
# bin_PROGRAMS = cvc4 pcvc4
## And this one if you want to call cvc4 to point to multi-threaded
bin_PROGRAMS = cvc4 scvc4

noinst_LIBRARIES = libmain.a

libmain_a_SOURCES = \
	interactive_shell.h \
	interactive_shell.cpp \
	main.h \
	usage.h \
	util.cpp \
	driver.cpp

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
cvc4_SOURCES = main_portfolio.cpp driver_portfolio.cpp
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


scvc4_SOURCES = main.cpp
scvc4_LDADD = \
	libmain.a \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la

if STATIC_BINARY
scvc4_LINK = $(CXXLINK) -all-static
else
scvc4_LINK = $(CXXLINK)
endif

