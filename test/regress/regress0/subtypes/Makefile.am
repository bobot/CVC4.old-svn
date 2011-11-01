SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	subranges.cvc \
	arith-subranges.cvc \
	arith-negative-subranges.cvc \
	subtype.cvc \
	subtype2.cvc \
	subtype3.cvc \
	subtype4.cvc \
	bug99.cvc \
	models_diff_int_01.cvc \
	george.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
