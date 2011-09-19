%import "bindings/swig.h"
%module cvc4

%include "util/integer.i"
%include "util/rational.i"
%include "util/exception.i"
%include "util/options.i"
%include "util/cardinality.i"

%include "expr/command.i"
%include "expr/declaration_scope.i"
%include "expr/kind.i"
%include "expr/type.i"
%include "expr/expr.i"
%include "expr/expr_manager.i"

%include "smt/smt_engine.i"
