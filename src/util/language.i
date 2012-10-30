%{
#include "util/language.h"
%}

namespace CVC4 {
  namespace language {
    namespace input {
      %ignore operator<<(std::ostream&, Language);
    }/* CVC4::language::input namespace */

    namespace output {
      %ignore operator<<(std::ostream&, Language);
    }/* CVC4::language::output namespace */
  }/* CVC4::language namespace */
}/* CVC4 namespace */

// These clash in the monolithic Java namespace, so we rename them.
%rename(InputLanguage) CVC4::language::input::Language;
%rename(OutputLanguage) CVC4::language::output::Language;

%rename(INPUT_LANG_AUTO) CVC4::language::input::LANG_AUTO;
%rename(INPUT_LANG_SMTLIB_V1) CVC4::language::input::LANG_SMTLIB_V1;
%rename(INPUT_LANG_SMTLIB_V2) CVC4::language::input::LANG_SMTLIB_V2;
%rename(INPUT_LANG_TPTP) CVC4::language::input::LANG_TPTP;
%rename(INPUT_LANG_CVC4) CVC4::language::input::LANG_CVC4;
%rename(INPUT_LANG_MAX) CVC4::language::input::LANG_MAX;

%rename(OUTPUT_LANG_AUTO) CVC4::language::output::LANG_AUTO;
%rename(OUTPUT_LANG_SMTLIB_V1) CVC4::language::output::LANG_SMTLIB_V1;
%rename(OUTPUT_LANG_SMTLIB_V2) CVC4::language::output::LANG_SMTLIB_V2;
%rename(OUTPUT_LANG_TPTP) CVC4::language::output::LANG_TPTP;
%rename(OUTPUT_LANG_CVC4) CVC4::language::output::LANG_CVC4;
%rename(OUTPUT_LANG_AST) CVC4::language::output::LANG_AST;
%rename(OUTPUT_LANG_MAX) CVC4::language::output::LANG_MAX;

%include "util/language.h"
