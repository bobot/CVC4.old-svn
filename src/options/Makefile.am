AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	options.h

nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	base_options.cpp \
	base_options.h \
	prop_options.cpp \
	prop_options.h \
	theory_uf_options.h \
	theory_uf_options.cpp \
	theory_arith_options.cpp \
	theory_arith_options.h

BUILT_SOURCES = \
	options.cpp \
	options_holder.h \
	base_options.cpp \
	base_options.h \
	$(builddir)/../prop/options.cpp \
	$(builddir)/../prop/options.h \
	$(builddir)/../theory/uf/options.h \
	$(builddir)/../theory/uf/options.cpp \
	$(builddir)/../theory/arith/options.cpp \
	$(builddir)/../theory/arith/options.h \
	exprs-builts

EXTRA_DIST = \
	mkoptions \
	options \
	options_template.cpp \
	options_holder_template.h \
	options.i

if CVC4_DEBUG
# listing Debug_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Debug_tags.h \
	Debug_tags
endif
if CVC4_TRACING
# listing Trace_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Trace_tags.h \
	Trace_tags
endif
%_tags.h: %_tags
	$(AM_V_GEN)( \
	  echo 'static char const* const $^[] = {'; \
	  for tag in `cat $^`; do \
	    echo "\"$$tag\","; \
	  done; \
	  echo 'NULL'; \
	  echo '};' \
	) >"$@"

# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
%_tags: %_tags.tmp
	$(AM_V_GEN)\
	diff -q "$^" "$@" &>/dev/null || mv "$^" "$@" || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: Debug_tags.tmp Trace_tags.tmp
# The "sed" invocation below is particularly obnoxious, but it works around
# inconsistencies in REs on different platforms, using only a basic regular
# expression (no |, no \<, ...).
Debug_tags.tmp Trace_tags.tmp:
	$(AM_V_GEN)\
	grep '\<$(@:_tags.tmp=) *( *\".*\" *)' \
		`find @srcdir@/../ -name "*.cpp" -or -name "*.h" -or -name "*.cc" -or -name "*.g"` | \
	sed 's/^$(@:_tags.tmp=) *( *\"\([^"]*\)\".*/\1/;s/.*[^a-zA-Z0-9_]$(@:_tags.tmp=) *( *\"\([^"]*\)\".*/\1/' | sort | uniq >"$@"

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

options_holder.h: options_holder_template.h mkoptions @top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options \
	) || (rm -f $@ && exit 1)

options.cpp: options_template.cpp mkoptions @top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@top_srcdir@/src/*/options @top_srcdir@/src/theory/*/options \
	) || (rm -f $@ && exit 1)

base_options.h: base_options_template.h mkoptions options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/options \
	) || (rm -f $@ && exit 1)

base_options.cpp: base_options_template.cpp mkoptions options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../theory/arith/options:;
$(builddir)/../theory/arith/options.h: base_options_template.h mkoptions ../theory/arith/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arith/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../theory/arith/options.cpp: base_options_template.cpp mkoptions ../theory/arith/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arith/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../theory/uf/options:;
$(builddir)/../theory/uf/options.h: base_options_template.h mkoptions ../theory/uf/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/uf/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../theory/uf/options.cpp: base_options_template.cpp mkoptions ../theory/uf/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/uf/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../prop/options:;
$(builddir)/../prop/options.h: base_options_template.h mkoptions ../prop/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../prop/options \
	) || (rm -f $@ && exit 1)

$(builddir)/../prop/options.cpp: base_options_template.cpp mkoptions ../prop/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../prop/options \
	) || (rm -f $@ && exit 1)

.PHONY: exprs-builts builts
builts: $(BUILT_SOURCES)
exprs-builts:; $(MAKE) -C ../expr builts
