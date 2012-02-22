#include "theory/arith/bcqueue.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

uint32_t BranchAndCutQueue::ScorePair::s_idDist = 0;

void BranchAndCutQueue::pushVector(const std::vector<ArithVar>& v){
  std::vector<ArithVar>::const_iterator i, end;

  for(i = v.begin(), end = v.end(); i != end; ++i){
    push(*i);
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
