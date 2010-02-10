
#ifndef __CVC4__THEORY__THEORY_UF_H
#define __CVC4__THEORY__THEORY_UF_H

#include "theory/theory.h"

class TheoryUF : public Theory {
public:
  void setup(const Node& n);
  
  void check(OutputChannel& out, Effort level= FULL_EFFORT);

  void propagate(OutputChannel& out, Effort level= FULL_EFFORT){}

  void explain(OutputChannel& out,
               const Node& n,
               Effort level = FULL_EFFORT){}
};


#endif /* __CVC4__THEORY__THEORY_UF_H */
