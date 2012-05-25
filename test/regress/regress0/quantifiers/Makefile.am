TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	bug269.smt2 \
	ex3.smt2 \
	Arrays_Q1-noinfer.smt2 \
	array-unsat-simp3.smt2 \
	bignum_quant.smt2 \
	bug269.smt2 \
	burns13.smt2 \
	burns4.smt2 \
	ex1.smt2 \
	ex3.smt2 \
	ex6.smt2 \
	ex7.smt2 \
	opisavailable-12.smt2 \
	ricart-agrawala6.smt2 \
	set8.smt2 \
	smtlib384a03.smt2 \
	smtlib46f14a.smt2 \
	smtlibf957ea.smt2

# removed because they take more than 20s
#		ex1.smt2 \
#		ex6.smt2 \
#	        ex7.smt2 \
#		array-unsat-simp3.smt2are
#		javafe.ast.ArrayInit.35.smt2 \
#		javafe.ast.StandardPrettyPrint.319.smt2 \
#		javafe.ast.StmtVec.009.smt2 \
#		javafe.ast.WhileStmt.447.smt2 \
#		javafe.tc.CheckCompilationUnit.001.smt2 \
#		AdditiveMethods_AdditiveMethods..ctor.smt2 \
#		AdditiveMethods_OwnedResults.Mz.smt2 \
#		javafe.tc.FlowInsensitiveChecks.682.smt2 \
#

EXTRA_DIST = $(TESTS) \
	array-unsat-simp3.smt2.expect \
	ex1.smt2.expect \
	ex7.smt2.expect

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
