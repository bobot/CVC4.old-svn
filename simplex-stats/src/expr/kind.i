%{
#include "expr/kind.h"
%}

%ignore CVC4::kind::operator<<(std::ostream&, CVC4::Kind);
%ignore CVC4::operator<<(std::ostream&, TypeConstant);
%ignore CVC4::theory::operator<<(std::ostream&, TheoryId);

%ignore CVC4::theory::operator++(TheoryId&);

%rename(Kind) CVC4::kind::Kind_t;

%include "expr/kind.h"
