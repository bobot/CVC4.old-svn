%{
#include "options/options.h"
%}

%ignore CVC4::operator<<(std::ostream&, Options::SimplificationMode);
%ignore CVC4::operator<<(std::ostream&, Options::ArithPivotRule);

%apply char** STRING_ARRAY { char* argv[] }
%include "options/options.h"
%clear char* argv[];
