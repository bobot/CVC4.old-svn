TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS =


# Regression tests for SMT2 inputs
SMT2_TESTS = \
	FIREFLY_3_e2_2236_e7_3681.ec.minimized.smt2 \
	FIREFLY_3_e2_2236_e7_3681.ec.core.smt2 \
	DRAGON_11_e1_2450.ec.minimized.smt2 \
	microwave21.ec.minimized.smt2


# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# Necessary to get automake's attention when splitting TESTS into
# SMT_TESTS, SMT2_TESTS, etc..
EXTRA_DIST = $(TESTS) \
	FIREFLY_3_e2_2236_e7_3681.ec.minimized.smt2.expect \
	FIREFLY_3_e2_2236_e7_3681.ec.core.smt2.expect \
	DRAGON_11_e1_2450.ec.minimized.smt2.expect

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
