AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_static_learner.h \
	arith_static_learner.cpp \
	arith_prop_manager.h \
	arith_prop_manager.cpp \
	arithvar_node_map.h \
	atom_database.h \
	atom_database.cpp \
	normal_form.h\
	normal_form.cpp \
	arith_utilities.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	ordered_set.h \
	arithvar_set.h \
	tableau.h \
	tableau.cpp \
	arith_priority_queue.h \
	arith_priority_queue.cpp \
	simplex.h \
	simplex.cpp \
	theory_arith.h \
	theory_arith.cpp \
	dio_solver.h \
	dio_solver.cpp

nodist_libarith_la_SOURCES = \
	options.cpp \
	options.h

BUILT_SOURCES = \
	options.cpp \
	options.h

EXTRA_DIST = \
	kinds \
	options

options:;
options.h options.cpp: @top_srcdir@/src/options/base_options_template.h @top_srcdir@/src/options/base_options_template.cpp @top_srcdir@/src/options/mkoptions options
	$(MAKE) -C @top_srcdir@/src/options builts
