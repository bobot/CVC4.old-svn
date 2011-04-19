#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H
#define __CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H


#include "theory/arith/arith_utilities.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdmap.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithVarNodeMap {
private:
  /**
   * Bidirectional map between Nodes and ArithVars.
   */
  NodeToArithVarMap d_nodeToArithVarMap;
  ArithVarToNodeMap d_arithVarToNodeMap;

public:
  ArithVarNodeMap() {}

  inline bool hasArithVar(TNode x) const {
    return d_nodeToArithVarMap.find(x) != d_nodeToArithVarMap.end();
  }

  inline ArithVar asArithVar(TNode x) const{
    Assert(hasArithVar(x));
    Assert((d_nodeToArithVarMap.find(x))->second <= ARITHVAR_SENTINEL);
    return (d_nodeToArithVarMap.find(x))->second;
  }
  inline Node asNode(ArithVar a) const{
    Assert(d_arithVarToNodeMap.find(a) != d_arithVarToNodeMap.end());
    return (d_arithVarToNodeMap.find(a))->second;
  }

  inline void setArithVar(TNode x, ArithVar a){
    Assert(!hasArithVar(x));
    Assert(d_arithVarToNodeMap.find(a) == d_arithVarToNodeMap.end());
    d_arithVarToNodeMap[a] = x;
    d_nodeToArithVarMap[x] = a;
  }

  const ArithVarToNodeMap& getArithVarToNodeMap() const {
    return d_arithVarToNodeMap;
  }

};/* class ArithVarNodeMap */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H */
