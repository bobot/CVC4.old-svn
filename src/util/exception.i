%{
#include "util/exception.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Exception&) throw();
%ignore CVC4::Exception::Exception(const char*) throw();
%typemap(javabase) CVC4::Exception "java.lang.RuntimeException";

%include "util/exception.h"
