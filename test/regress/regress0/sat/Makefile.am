SUBDIRS = . 

TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = \
	par8-1-c.cnf.smt \
	par8-1.cnf.smt \
	par8-2-c.cnf.smt \
	par8-2.cnf.smt \
	par8-3-c.cnf.smt \
	par8-3.cnf.smt \
	par8-4-c.cnf.smt \
	par8-4.cnf.smt \
	par8-5-c.cnf.smt \
	par8-5.cnf.smt \
	uf20-010.cnf.smt \
	uf20-0111.cnf.smt \
	uf20-0145.cnf.smt \
	uf20-019.cnf.smt \
	uf20-0359.cnf.smt \
	uf20-0416.cnf.smt \
	uf20-0546.cnf.smt \
	uf20-0678.cnf.smt \
	uf20-0684.cnf.smt \
	uf20-0693.cnf.smt \
	uf20-0710.cnf.smt \
	uf20-075.cnf.smt \
	uf20-0777.cnf.smt \
	uf20-0839.cnf.smt \
	uf20-0962.cnf.smt

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
