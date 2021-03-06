%{
#include "expr/type.h"
%}

%rename(apply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;

%ignore CVC4::operator<<(std::ostream&, const Type&);

%rename(assign) CVC4::Type::operator=(const Type&);
%rename(equals) CVC4::Type::operator==(const Type&) const;
%ignore CVC4::Type::operator!=(const Type&) const;
%rename(less) CVC4::Type::operator<(const Type&) const;
%rename(lessEqual) CVC4::Type::operator<=(const Type&) const;
%rename(greater) CVC4::Type::operator>(const Type&) const;
%rename(greaterEqual) CVC4::Type::operator>=(const Type&) const;

%rename(toBooleanType) CVC4::Type::operator BooleanType() const;
%rename(toIntegerType) CVC4::Type::operator IntegerType() const;
%rename(toRealType) CVC4::Type::operator RealType() const;
%rename(toStringType) CVC4::Type::operator StringType() const;
%rename(toBitVectorType) CVC4::Type::operator BitVectorType() const;
%rename(toFunctionType) CVC4::Type::operator FunctionType() const;
%rename(toTupleType) CVC4::Type::operator TupleType() const;
%rename(toSExprType) CVC4::Type::operator SExprType() const;
%rename(toArrayType) CVC4::Type::operator ArrayType() const;
%rename(toDatatypeType) CVC4::Type::operator DatatypeType() const;
%rename(toConstructorType) CVC4::Type::operator ConstructorType() const;
%rename(toSelectorType) CVC4::Type::operator SelectorType() const;
%rename(toTesterType) CVC4::Type::operator TesterType() const;
%rename(toSortType) CVC4::Type::operator SortType() const;
%rename(toSortConstructorType) CVC4::Type::operator SortConstructorType() const;
%rename(toPredicateSubtype) CVC4::Type::operator PredicateSubtype() const;
%rename(toSubrangeType) CVC4::Type::operator SubrangeType() const;

namespace CVC4 {
  namespace expr {
    %ignore exportTypeInternal;
  }/* CVC4::expr namespace */
}/* CVC4 namespace */

%include "expr/type.h"
