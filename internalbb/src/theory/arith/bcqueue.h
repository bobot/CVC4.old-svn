/*********************                                                        */
/*! \file bcqueue.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__BRANCH_AND_CUT_QUEUE_H
#define __CVC4__THEORY__ARITH__BRANCH_AND_CUT_QUEUE_H

#include "theory/arith/arith_utilities.h"
#include <vector>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class BranchAndCutQueue {
public:
  BranchAndCutQueue(ArithVarPredicate& p) : d_hasIntegerValue(p){}

  bool empty(){
    popUntilValid();
    return d_queue.empty();
  }

  ArithVar pop(){
    popUntilValid();
    Assert(!d_queue.empty());
    ArithVar top = d_queue.top().d_variable;
    Debug("bacqueue") << "pop" << d_queue.top().d_variable << " " << d_queue.top().d_score << std::endl;

    d_queue.pop();
    return top;
  }

  void push(ArithVar x){
    d_queue.push(ScorePair(x, score(x)));
  }

  void pushVector(const std::vector<ArithVar>& v);


  void changeScore(ArithVar x, bool left, uint32_t delta){
    if(left){
      d_scores[x].d_lnumerator += delta;
      d_scores[x].d_ldenominator ++;
    }else{
      d_scores[x].d_rnumerator += delta;
      d_scores[x].d_rdenominator ++;
    }
  }

  void addVariable(){
    d_scores.push_back(ScoreInformation());
  }

private:
  ArithVarPredicate& d_hasIntegerValue;

  struct ScoreInformation{
    double d_lnumerator;
    double d_rnumerator;
    double d_ldenominator;
    double d_rdenominator;
    ScoreInformation() :
      d_lnumerator(0), d_rnumerator(0), d_ldenominator(0), d_rdenominator(0)
    {}
  };
  std::vector<ScoreInformation> d_scores;

  class ScorePair{
  private:
    uint32_t d_id;
    static uint32_t s_idDist;

  public:
    ScorePair(ArithVar x, double score) :
      d_id(++s_idDist), d_variable(x), d_score(score)
    {}

    ArithVar d_variable;
    double d_score;

    bool operator<(const ScorePair& other) const{
      if(d_score == other.d_score){
        return d_id < other.d_id;
      }
      else{
        return d_score > other.d_score;
      }
    }
  };

  std::priority_queue< ScorePair > d_queue;

  double scoreSideLeft(ArithVar x){
    double num = d_scores[x].d_lnumerator;
    double den = d_scores[x].d_ldenominator;
    if(den == 0){
      return 1;
    }else{
      return num / den;
    }
  }

  double scoreSideRight(ArithVar x){
    double num = d_scores[x].d_rnumerator;
    double den = d_scores[x].d_rdenominator;
    if(den == 0){
      return 1;
    }else{
      return num / den;
    }
  }

  double score(ArithVar x){
    return std::min(scoreSideLeft(x), scoreSideRight(x));
  }

  bool isValid(const ScorePair& p){
    if(score(p.d_variable) == p.d_score){
      return !d_hasIntegerValue.callback(p.d_variable);
    }else{
      return false;
    }
  }

  void popUntilValid(){
    while(!d_queue.empty()){
      const ScorePair& p = d_queue.top();
      if(isValid(p)){
        break;
      }else{
        d_queue.pop();
      }
    }
  }
};


}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__BRANCH_AND_CUT_QUEUE_H */
