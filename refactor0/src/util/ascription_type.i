%{
#include "util/ascription_type.h"
%}

%rename(equals) CVC4::AscriptionType::operator==(const AscriptionType&) const;
%ignore CVC4::AscriptionType::operator!=(const AscriptionType&) const;

%ignore CVC4::operator<<(std::ostream&, AscriptionType);

%include "util/ascription_type.h"
