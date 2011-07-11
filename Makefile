# -*-makefile-*-
#
# This makefile is the _source_ directory's makefile, and is static,
# not generated.  Makefile.am is the automake makefile for the build
# top-level (its corresponding Makefile.in is here, too, but the
# corresponding Makefile is under builds/$arch/$buildid.
#
builddir = builds

.PHONY: all
all .DEFAULT:
	@if test -d $(builddir); then \
		echo cd $(builddir); \
		cd $(builddir); \
		echo $(MAKE) $@; \
		$(MAKE) $@; \
	else \
		echo; \
		echo 'Run configure first, or type "make" in a configured build directory.'; \
		echo; \
	fi

# synonyms for "check"
.PHONY: test
test: check

.PHONY: doc
doc: doc-builds

submission:
	if [ ! -e configure ]; then ./autogen.sh; fi
	./configure competition --disable-shared --enable-static-binary
	$(MAKE)
	mkdir -p cvc4-smtcomp-2011
	cp -p $(top_builddir)/bin/cvc4 cvc4-smtcomp-2011/cvc4
	strip cvc4-smtcomp-2011/cvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./cvc4 -L smt2 --no-interactive' ) > cvc4-smtcomp-2011/run
	chmod 755 cvc4-smtcomp-2011/run
	tar cf cvc4-smtcomp-2011.tar cvc4-smtcomp-2011