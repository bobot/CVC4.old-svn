SUBDIRS = .

BINARY = cvc4
LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(TESTS_ENVIRONMENT) $(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	tuple.cvc \
	rec1.cvc \
	rec2.cvc \
	rec4.cvc \
	rec5.cvc \
	datatype.cvc \
	datatype0.cvc \
	datatype1.cvc \
	datatype2.cvc \
	datatype3.cvc \
	datatype4.cvc \
	datatype13.cvc \
	mutually-recursive.cvc \
	rewriter.cvc \
	typed_v1l50016-simp.cvc \
	typed_v10l30054.cvc \
	typed_v1l80005.cvc \
	typed_v2l30079.cvc \
	typed_v3l20092.cvc \
	typed_v5l30069.cvc \
	v10l40099.cvc \
	v2l40025.cvc \
	v3l60006.cvc \
	v5l30058.cvc \
	bug286.cvc \
	bug438.cvc \
	bug438b.cvc \
	wrong-sel-simp.cvc

FAILING_TESTS = \
	datatype-dump.cvc

EXTRA_DIST = $(TESTS)

if CVC4_BUILD_PROFILE_COMPETITION
else
TESTS += \
	error.cvc
endif

# and make sure to distribute it
EXTRA_DIST += \
	error.cvc \
	$(FAILING_TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
