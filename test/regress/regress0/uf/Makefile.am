BINARY = cvc4
LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(TESTS_ENVIRONMENT) $(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	euf_simp01.smt \
	euf_simp02.smt \
	euf_simp03.smt \
	euf_simp04.smt \
	euf_simp05.smt \
	euf_simp06.smt \
	euf_simp08.smt \
	euf_simp09.smt \
	euf_simp10.smt \
	euf_simp11.smt \
	euf_simp12.smt \
	euf_simp13.smt \
	eq_diamond1.smt \
	eq_diamond14.reduced.smt \
	eq_diamond14.reduced2.smt \
	eq_diamond23.smt \
	NEQ016_size5_reduced2a.smt \
	NEQ016_size5_reduced2b.smt \
	ccredesign-fuzz.smt \
	dead_dnd002.smt \
	iso_brn001.smt \
	gensys_brn001.smt2 \
	simple.01.cvc \
	simple.02.cvc \
	simple.03.cvc \
	simple.04.cvc

EXTRA_DIST = $(TESTS) \
	mkpidgeon

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
