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
	FIREFLY_luke_1b_e2_3049_e7_1173.ec.minimized.smt2 \
	DRAGON_11_e1_2450.ec.minimized.smt2 \
	microwave21.ec.minimized.smt2 \
	stalmark_e7_27_e7_31.ec.minimize.smt2 \
	stalmark_e7_27_e7_31.ec.smt2 \
	speed2_e8_449_e8_517.ec.smt2 \
	tiny.smt2 \
	check01.smt2 \
	check02.smt2 \
	check04.smt2 \
	check03.smt2

# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# Necessary to get automake's attention when splitting TESTS into
# SMT_TESTS, SMT2_TESTS, etc..
EXTRA_DIST = $(TESTS) \
	car_6.ec.smt2 \
	FIREFLY_3_e2_2236_e7_3681.ec.minimized.smt2.expect \
	FIREFLY_3_e2_2236_e7_3681.ec.core.smt2.expect \
	DRAGON_11_e1_2450.ec.minimized.smt2.expect \
	stalmark_e7_27_e7_31.ec.minimize.smt2.expect \
	stalmark_e7_27_e7_31.ec.smt2.expect \
	speed2_e8_449_e8_517.ec.smt2.expect \
	tiny.smt2.expect \
	check02.smt2.expect \
	check03.smt2.expect \
	check04.smt2.expect


# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
