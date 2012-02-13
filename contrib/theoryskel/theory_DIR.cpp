#include "theory/$dir/theory_$dir.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace $dir {

/** Constructs a new instance of Theory$camel w.r.t. the provided contexts. */
Theory$camel::Theory$camel(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation) :
  Theory(THEORY_UF, c, u, out, valuation) {
}/* Theory$camel::Theory$camel() */

void Theory$camel::check(Effort level) {

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("$dir") << "Theory$camel::check(): processing " << fact << std::endl;

    // Do the work
    switch(fact.getKind()) {

    /* cases for all the theory's kinds go here... */

    default:
      Unhandled(fact.getKind());
    }
  }

}/* Theory$camel::check() */

}/* CVC4::theory::$dir namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
