SUBDIRS = . core

BINARY = cvc4
TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/$(BINARY)
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS =

# Regression tests for SMT2 inputs
SMT2_TESTS =

# Regression tests for PL inputs
CVC_TESTS = bvsimple.cvc

# Regression tests derived from bug reports
BUG_TESTS =

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	test00.smt \
	bvcomp.cvc
