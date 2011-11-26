#include "theory/arith/difference_manager.h"
#include "theory/uf/equality_engine_impl.h"

namespace CVC4 {
namespace theory {
namespace arith {

DifferenceManager::DifferenceManager(context::Context* c)
  : d_reasons(c),
    d_propQueue(c),
    d_propIndex(c,0),
    d_notify(*this),
    d_ee(d_notify, c, "theory::arith::DifferenceManager")
{}

void DifferenceManager::propagate(TNode x){
  Debug("arith::differenceManager")<< "DifferenceManager::propagate("<<x<<")"<<std::endl;

  d_propQueue.push_back(x);
}

void DifferenceManager::addDifference(ArithVar s, Node x, Node y){
  Assert(s >= d_differences.size() || !isDifferenceSlack(s));

  Debug("arith::differenceManager") << s << x << y << std::endl;

  d_differences.resize(s+1);
  d_differences[s] = Difference(x,y);
}

void DifferenceManager::differenceIsZero(ArithVar s, TNode reason){
  Assert(isDifferenceSlack(s));
  TNode x = d_differences[s].x;
  TNode y = d_differences[s].y;

  d_reasons.push_back(reason);
  d_ee.addEquality(x, y, reason);
}

void DifferenceManager::differenceCannotBeZero(ArithVar s, TNode reason){
  Assert(isDifferenceSlack(s));
  TNode x = d_differences[s].x;
  TNode y = d_differences[s].y;

  d_reasons.push_back(reason);
  d_ee.addDisequality(x, y, reason);
}

void DifferenceManager::addSharedTerm(Node x){
  d_ee.addTriggerTerm(x);
}


bool DifferenceManager::hasMorePropagations() const{
    return d_propIndex < d_propQueue.size();
  }

Node DifferenceManager::nextPropagation(){
  Node prop = d_propQueue[d_propIndex];
  d_propIndex = d_propIndex + 1;
  return prop;
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
