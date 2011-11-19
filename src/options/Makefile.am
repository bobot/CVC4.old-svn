OPTIONS_FILES = \
	options/options \
	expr/options \
	theory/booleans/options \
	theory/options \
	theory/bv/options \
	theory/datatypes/options \
	theory/builtin/options \
	theory/arith/options \
	theory/uf/options \
	theory/arrays/options \
	prop/options \
	proof/options \
	printer/options \
	smt/options \
	main/options \
	parser/options

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	options.h \
	base_options_handlers.h

nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	base_options.cpp \
	base_options.h \
	$(OPTIONS_FILES:%=../%.cpp) \
	$(OPTIONS_FILES:%=../%.h)

BUILT_SOURCES = \
	options.cpp \
	options_holder.h \
	base_options.cpp \
	base_options.h \
	$(OPTIONS_FILES:%=../%.cpp) \
	$(OPTIONS_FILES:%=../%.h) \
	exprs-builts

EXTRA_DIST = \
	mkoptions \
	options \
	base_options_template.h \
	base_options_template.cpp \
	options_template.cpp \
	options_holder_template.h \
	options.i \
	$(OPTIONS_FILES:%=../%)

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

options:;
../options/options:;
../expr/options:;
../expr/options.h: base_options_template.h mkoptions ../expr/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../expr/options \
	) || (rm -f $@ && exit 1)

../expr/options.cpp: base_options_template.cpp mkoptions ../expr/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../expr/options \
	) || (rm -f $@ && exit 1)

../theory/options:;
../theory/options.h: base_options_template.h mkoptions ../theory/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/options \
	) || (rm -f $@ && exit 1)

../theory/options.cpp: base_options_template.cpp mkoptions ../theory/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/options \
	) || (rm -f $@ && exit 1)

../theory/builtin/options:;
../theory/builtin/options.h: base_options_template.h mkoptions ../theory/builtin/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/builtin/options \
	) || (rm -f $@ && exit 1)

../theory/builtin/options.cpp: base_options_template.cpp mkoptions ../theory/builtin/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/builtin/options \
	) || (rm -f $@ && exit 1)

../theory/booleans/options:;
../theory/booleans/options.h: base_options_template.h mkoptions ../theory/booleans/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/booleans/options \
	) || (rm -f $@ && exit 1)

../theory/booleans/options.cpp: base_options_template.cpp mkoptions ../theory/booleans/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/booleans/options \
	) || (rm -f $@ && exit 1)


../theory/arith/options:;
../theory/arith/options.h: base_options_template.h mkoptions ../theory/arith/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arith/options \
	) || (rm -f $@ && exit 1)

../theory/arith/options.cpp: base_options_template.cpp mkoptions ../theory/arith/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arith/options \
	) || (rm -f $@ && exit 1)

../theory/datatypes/options:;
../theory/datatypes/options.h: base_options_template.h mkoptions ../theory/datatypes/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/datatypes/options \
	) || (rm -f $@ && exit 1)

../theory/datatypes/options.cpp: base_options_template.cpp mkoptions ../theory/datatypes/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/datatypes/options \
	) || (rm -f $@ && exit 1)

../theory/bv/options:;
../theory/bv/options.h: base_options_template.h mkoptions ../theory/bv/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/bv/options \
	) || (rm -f $@ && exit 1)

../theory/bv/options.cpp: base_options_template.cpp mkoptions ../theory/bv/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/bv/options \
	) || (rm -f $@ && exit 1)

../theory/arrays/options:;
../theory/arrays/options.h: base_options_template.h mkoptions ../theory/arrays/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arrays/options \
	) || (rm -f $@ && exit 1)

../theory/arrays/options.cpp: base_options_template.cpp mkoptions ../theory/arrays/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/arrays/options \
	) || (rm -f $@ && exit 1)

../theory/uf/options:;
../theory/uf/options.h: base_options_template.h mkoptions ../theory/uf/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/uf/options \
	) || (rm -f $@ && exit 1)

../theory/uf/options.cpp: base_options_template.cpp mkoptions ../theory/uf/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../theory/uf/options \
	) || (rm -f $@ && exit 1)

../prop/options:;
../prop/options.h: base_options_template.h mkoptions ../prop/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../prop/options \
	) || (rm -f $@ && exit 1)

../prop/options.cpp: base_options_template.cpp mkoptions ../prop/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../prop/options \
	) || (rm -f $@ && exit 1)

../smt/options:;
../smt/options.h: base_options_template.h mkoptions ../smt/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../smt/options \
	) || (rm -f $@ && exit 1)

../smt/options.cpp: base_options_template.cpp mkoptions ../smt/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../smt/options \
	) || (rm -f $@ && exit 1)

../parser/options:;
../parser/options.h: base_options_template.h mkoptions ../parser/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../parser/options \
	) || (rm -f $@ && exit 1)

../parser/options.cpp: base_options_template.cpp mkoptions ../parser/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../parser/options \
	) || (rm -f $@ && exit 1)

../proof/options:;
../proof/options.h: base_options_template.h mkoptions ../proof/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../proof/options \
	) || (rm -f $@ && exit 1)

../proof/options.cpp: base_options_template.cpp mkoptions ../proof/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../proof/options \
	) || (rm -f $@ && exit 1)

../printer/options:;
../printer/options.h: base_options_template.h mkoptions ../printer/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../printer/options \
	) || (rm -f $@ && exit 1)

../printer/options.cpp: base_options_template.cpp mkoptions ../printer/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../printer/options \
	) || (rm -f $@ && exit 1)

../main/options:;
../main/options.h: base_options_template.h mkoptions ../main/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../main/options \
	) || (rm -f $@ && exit 1)

../main/options.cpp: base_options_template.cpp mkoptions ../main/options
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkoptions \
		$< $@ \
		@srcdir@/../main/options \
	) || (rm -f $@ && exit 1)

.PHONY: exprs-builts
exprs-builts:; $(AM_V_at)[ "$(FROM_EXPR)" != 1 ] && $(MAKE) -C ../expr builts || true
