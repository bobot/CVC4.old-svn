SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	test/regress/regress0/datatypes/datatype.cvc \
	test/regress/regress0/datatypes/datatype0.cvc \
	test/regress/regress0/datatypes/datatype1.cvc \
	test/regress/regress0/datatypes/datatype2.cvc \
	test/regress/regress0/datatypes/datatype3.cvc \
	test/regress/regress0/datatypes/datatype4.cvc \
	test/regress/regress0/datatypes/datatype5.cvc \
	test/regress/regress0/datatypes/datatype6.cvc \
	test/regress/regress0/datatypes/datatype7.cvc \
	test/regress/regress0/datatypes/datatype8.cvc \
	test/regress/regress0/datatypes/datatype9.cvc \
	test/regress/regress0/datatypes/datatype10.cvc \
	test/regress/regress0/datatypes/datatype11.cvc \
	test/regress/regress0/datatypes/datatype12.cvc \
	test/regress/regress0/datatypes/datatype13.cvc \
	test/regress/regress0/datatypes/typed_v1l50016-simp.cvc

EXTRA_DIST = $(TESTS)

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
