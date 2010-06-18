

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H

#include "expr/node.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdo.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithUnatePropagator {
private:
  context::CDO<unsigned int> d_pendingAssertions;
  context::CDList<Node> d_assertions;

  std::vector<Node> d_saver;

public:
  ArithUnatePropagator(context::Context* cxt);

  void addAtom(TNode atom);

  void assertLiteral(TNode lit);

  std::vector<Node> getImpliedLiterals();

  Node explain(TNode lit);

private:
  void addImplication(TNode a0, TNode a1);
  void introduceImplications(TNode atom, TNode otherAtom);

};



namespace propagator {

struct ListCleanupStrategy{
  static void cleanup(std::vector<Node> * l){
    Debug("arithgc") << "cleaning up  " << l << "\n";
    delete l;
  }
};

struct IsInPropagatorID {};
typedef expr::Attribute<IsInPropagatorID, bool> IsInPropagator;

struct PropagatorIGID {};
typedef expr::Attribute<PropagatorIGID,
                        std::vector<Node>*,
                        ListCleanupStrategy> PropagatorIG;

struct PropagatorRegisteredAtomsID {};
typedef expr::Attribute<PropagatorRegisteredAtomsID,
                        std::vector<Node>*,
                        ListCleanupStrategy> PropagatorRegisteredAtoms;


struct PropagatorMarkedID {};
typedef expr::CDAttribute<PropagatorMarkedID, bool> PropagatorMarked;

struct PropagatorExplanationID {};
typedef expr::CDAttribute<PropagatorExplanationID, Node> PropagatorExplanation;

}/* CVC4::theory::arith::propagator */
}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
