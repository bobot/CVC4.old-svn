/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/


#include "theory/arrays/theory_arrays.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/uf/equality_engine_impl.h"


using namespace std;


namespace CVC4 {
namespace theory {
namespace arrays {


TheoryArrays::TheoryArrays(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_ARRAY, c, u, out, valuation),
  d_numRow("theory::arrays::number of Row lemmas", 0),
  d_numExt("theory::arrays::number of Ext lemmas", 0),
  d_numProp("theory::arrays::number of propagations", 0),
  d_numExplain("theory::arrays::number of explanations", 0),
  d_checkTimer("theory::arrays::checkTime"),
  d_ppNotify(),
  d_ppEqualityEngine(d_ppNotify, u, "theory::arrays::TheoryArraysPP"),
  d_literalsToPropagate(c),
  d_literalsToPropagateIndex(c, 0),
  d_donePreregister(u, false),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::arrays::TheoryArrays"),
  d_conflict(c, false)
{
  StatisticsRegistry::registerStat(&d_numRow);
  StatisticsRegistry::registerStat(&d_numExt);
  StatisticsRegistry::registerStat(&d_numProp);
  StatisticsRegistry::registerStat(&d_numExplain);
  StatisticsRegistry::registerStat(&d_checkTimer);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  d_ppEqualityEngine.addTerm(d_true);
  d_ppEqualityEngine.addTerm(d_false);
  d_ppEqualityEngine.addTriggerEquality(d_true, d_false, d_false);

  d_equalityEngine.addTerm(d_true);
  d_equalityEngine.addTerm(d_false);
  d_equalityEngine.addTriggerEquality(d_true, d_false, d_false);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SELECT);
  d_equalityEngine.addFunctionKind(kind::EQUAL);
}


TheoryArrays::~TheoryArrays() {

  StatisticsRegistry::unregisterStat(&d_numRow);
  StatisticsRegistry::unregisterStat(&d_numExt);
  StatisticsRegistry::unregisterStat(&d_numProp);
  StatisticsRegistry::unregisterStat(&d_numExplain);
  StatisticsRegistry::unregisterStat(&d_checkTimer);

}


// TODO: move this into Node somewhere
static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());
  // TODO: move this check somewhere else?
  // Remove true assumption - these come from using equalities that are instances of axioms
  all.erase(NodeManager::currentNM()->mkConst<bool>(true));

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}


/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////


Node TheoryArrays::preprocessTerm(TNode term) {
  switch (term.getKind()) {
    case kind::SELECT: {
      // select(store(a,i,v),j) = select(a,j)
      //    IF i != j
      if (term[0].getKind() == kind::STORE &&
          d_ppEqualityEngine.areDisequal(term[0][1], term[1])) {
        return NodeBuilder<2>(kind::SELECT) << term[0][0] << term[1];
      }
      break;
    }
    case kind::STORE: {
      // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
      //    IF i != j and j comes before i in the ordering
      if (term[0].getKind() == kind::STORE &&
          (term[1] < term[0][1]) &&
          d_ppEqualityEngine.areDisequal(term[1], term[0][1])) {
        Node inner = NodeBuilder<3>(kind::STORE) << term[0][0] << term[1] << term[2];
        Node outer = NodeBuilder<3>(kind::STORE) << inner << term[0][1] << term[0][2];
        return outer;
      }
      break;
    }
    case kind::EQUAL: {
      if (term[0].getKind() == kind::STORE ||
          term[1].getKind() == kind::STORE) {
        TNode left = term[0];
        TNode right = term[1];
        int leftWrites = 0, rightWrites = 0;

        // Count nested writes
        TNode e1 = left;
        while (e1.getKind() == kind::STORE) {
          ++leftWrites;
          e1 = e1[0];
        }

        TNode e2 = right;
        while (e2.getKind() == kind::STORE) {
          ++rightWrites;
          e2 = e2[0];
        }

        if (rightWrites > leftWrites) {
          TNode tmp = left;
          left = right;
          right = tmp;
          int tmpWrites = leftWrites;
          leftWrites = rightWrites;
          rightWrites = tmpWrites;
        }

        NodeManager* nm = NodeManager::currentNM();
        if (rightWrites == 0) {
          if (e1 == e2) {
            // write(store, index_0, v_0, index_1, v_1, ..., index_n, v_n) = store IFF
            //
            // read(store, index_n) = v_n &
            // index_{n-1} != index_n -> read(store, index_{n-1}) = v_{n-1} &
            // (index_{n-2} != index_{n-1} & index_{n-2} != index_n) -> read(store, index_{n-2}) = v_{n-2} &
            // ...
            // (index_1 != index_2 & ... & index_1 != index_n) -> read(store, index_1) = v_1
            // (index_0 != index_1 & index_0 != index_2 & ... & index_0 != index_n) -> read(store, index_0) = v_0
            TNode write_i, write_j, index_i, index_j;
            Node conc;
            NodeBuilder<> result(kind::AND);
            int i, j;
            write_i = left;
            for (i = leftWrites-1; i >= 0; --i) {
              index_i = write_i[1];

              // build: [index_i /= index_n && index_i /= index_(n-1) &&
              //         ... && index_i /= index_(i+1)] -> read(store, index_i) = v_i
              write_j = left;
              {
                NodeBuilder<> hyp(kind::AND);
                for (j = leftWrites - 1; j > i; --j) {
                  index_j = write_j[1];
                  if (d_ppEqualityEngine.areDisequal(index_i, index_j)) {
                    continue;
                  }
                  Node hyp2(index_i.getType() == nm->booleanType()? 
                            index_i.iffNode(index_j) : index_i.eqNode(index_j));
                  hyp << hyp2.notNode();
                  write_j = write_j[0];
                }

                Node r1 = nm->mkNode(kind::SELECT, e1, index_i);
                conc = (r1.getType() == nm->booleanType())? 
                  r1.iffNode(write_i[2]) : r1.eqNode(write_i[2]);
                if (hyp.getNumChildren() != 0) {
                  if (hyp.getNumChildren() == 1) {
                    conc = hyp.getChild(0).impNode(conc);
                  }
                  else {
                    r1 = hyp;
                    conc = r1.impNode(conc);
                  }
                }

                // And into result
                result << conc;

                // Prepare for next iteration
                write_i = write_i[0];
              }
            }
            Assert(result.getNumChildren() > 0);
            if (result.getNumChildren() == 1) {
              return result.getChild(0);
            }
            return result;
          }
          break;
        }
        else {
          // store(...) = store(a,i,v) ==>
          // store(store(...),i,select(a,i)) = a && select(store(...),i)=v
          Node l = left;
          Node tmp;
          NodeBuilder<> nb(kind::AND);
          while (right.getKind() == kind::STORE) {
            tmp = nm->mkNode(kind::SELECT, l, right[1]);
            nb << tmp.eqNode(right[2]);
            tmp = nm->mkNode(kind::SELECT, right[0], right[1]);
            l = nm->mkNode(kind::STORE, l, right[1], tmp);
            right = right[0];
          }
          nb << l.eqNode(right);
          return nb;
        }
      }
      break;
    }
    default:
      break;
  }
  return term;
}

Node TheoryArrays::recursivePreprocessTerm(TNode term) {
  unsigned nc = term.getNumChildren();
  if (nc == 0 ||
      (theoryOf(term) != theory::THEORY_ARRAY &&
       term.getType() != NodeManager::currentNM()->booleanType())) {
    return term;
  }
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end()) {
    return (*find).second;
  }
  NodeBuilder<> newNode(term.getKind());
  unsigned i;
  for (i = 0; i < nc; ++i) {
    newNode << recursivePreprocessTerm(term[i]);
  }
  Node newTerm = Rewriter::rewrite(newNode);
  Node newTerm2 = preprocessTerm(newTerm);
  if (newTerm != newTerm2) {
    newTerm = recursivePreprocessTerm(Rewriter::rewrite(newTerm2));
  }
  d_ppCache[term] = newTerm;
  return newTerm;
}


Theory::SolveStatus TheoryArrays::solve(TNode in, SubstitutionMap& outSubstitutions) {
  // switch(in.getKind()) {
  //   case kind::EQUAL:
  //   {
  //     d_ppFacts.push_back(in);
  //     d_ppEqualityEngine.addEquality(in[0], in[1], in);
  //     if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
  //       outSubstitutions.addSubstitution(in[0], in[1]);
  //       return SOLVE_STATUS_SOLVED;
  //     }
  //     if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
  //       outSubstitutions.addSubstitution(in[1], in[0]);
  //       return SOLVE_STATUS_SOLVED;
  //     }
  //     break;
  //   }
  //   case kind::NOT:
  //   {
  //     d_ppFacts.push_back(in);
  //     Assert(in[0].getKind() == kind::EQUAL ||
  //            in[0].getKind() == kind::IFF );
  //     Node a = in[0][0];
  //     Node b = in[0][1];
  //     d_ppEqualityEngine.addDisequality(a, b, in);
  //     break;
  //   }
  //   default:
  //     break;
  // }
  return SOLVE_STATUS_UNSOLVED;
}


Node TheoryArrays::preprocess(TNode atom) {
  return atom;
  // if (d_donePreregister) return atom;
  // Assert(atom.getKind() == kind::EQUAL, "expected EQUAL, got %s", atom.toString().c_str());
  // return recursivePreprocessTerm(atom);
}


/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////


bool TheoryArrays::propagate(TNode literal)
{
  Debug("arrays") << "TheoryArrays::propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("arrays") << "TheoryArrays::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // See if the literal has been asserted already
  bool satValue = false;
  bool isAsserted = literal == d_false || d_valuation.hasSatValue(literal, satValue);

  // If asserted, we're done or in conflict
  if (isAsserted) {
    if (satValue) {
      Debug("arrays") << "TheoryArrays::propagate(" << literal << ") => already known" << std::endl;
      return true;
    } else {
      Debug("arrays") << "TheoryArrays::propagate(" << literal << ") => conflict" << std::endl;
      std::vector<TNode> assumptions;
      Node negatedLiteral;
      if (literal != d_false) {
        negatedLiteral = literal.getKind() == kind::NOT ? (Node) literal[0] : literal.notNode();
        assumptions.push_back(negatedLiteral);
      }
      explain(literal, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return false;
    }
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("arrays") << "TheoryArrays::propagate(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  return true;
}/* TheoryArrays::propagate(TNode) */


void TheoryArrays::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::SELECT:
      lhs = literal;
      rhs = d_true;
      break;
    case kind::NOT:
      if (literal[0].getKind() == kind::EQUAL) {
        // Disequalities
        d_equalityEngine.explainDisequality(literal[0][0], literal[0][1], assumptions);
        return;
      } else {
        // Predicates
        lhs = literal[0];
        rhs = d_false;
        break;
      }
    case kind::CONST_BOOLEAN:
      // we get to explain true = false, since we set false to be the trigger of this
      lhs = d_true;
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_equalityEngine.explainEquality(lhs, rhs, assumptions);
}


  /**
   * Stores in d_infoMap the following information for each term a of type array:
   *
   *    - all i, such that there exists a term a[i] or a = store(b i v)
   *      (i.e. all indices it is being read atl; store(b i v) is implicitly read at
   *      position i due to the implicit axiom store(b i v)[i] = v )
   *
   *    - all the stores a is congruent to (this information is context dependent)
   *
   *    - all store terms of the form store (a i v) (i.e. in which a appears
   *      directly; this is invariant because no new store terms are created)
   *
   * Note: completeness depends on having pre-register called on all the input
   *       terms before starting to instantiate lemmas.
   */
void TheoryArrays::preRegisterTerm(TNode node)
{
  Debug("arrays") << "TheoryArrays::preRegisterTerm(" << node << ")" << std::endl;

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the terms
    d_equalityEngine.addTerm(node[0]);
    d_equalityEngine.addTerm(node[1]);
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(node[0], node[1], node);
    d_equalityEngine.addTriggerDisequality(node[0], node[1], node.notNode());
    break;
  case kind::SELECT:
    // Reads
    d_equalityEngine.addTerm(node);
    // Maybe it's a predicate
    // TODO: remove this or keep it if we allow Boolean elements in arrays.
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerEquality(node, d_true, node);
      d_equalityEngine.addTriggerEquality(node, d_false, node.notNode());
    }

    //    d_infoMap.addIndex(n[0], n[1]);
    //    checkRowForIndex(n[1], find(n[0]));

    break;

  case kind::STORE: {
    TNode a = node[0];
    TNode i = node[1];
    TNode v = node[2];

    NodeManager* nm = NodeManager::currentNM();
    Node ni = nm->mkNode(kind::SELECT, node, i);
    //    Node eq = nm->mkNode(kind::EQUAL, ni, v);

    // Apply RIntro1 Rule
    d_equalityEngine.addEquality(ni, v, d_true);

    //      d_infoMap.addIndex(n, i);
    //      d_infoMap.addStore(n, n);
    //      d_infoMap.addInStore(a, n);

    //      checkStore(n);
    break;
  }
  default:
    // Variables etc
    d_equalityEngine.addTerm(node);
    break;
  }
}


void TheoryArrays::propagate(Effort e)
{
  Debug("arrays") << "TheoryArrays::propagate()" << std::endl;
  if (!d_conflict) {
    for (; d_literalsToPropagateIndex < d_literalsToPropagate.size(); d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
      TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
      Debug("arrays") << "TheoryArrays::propagate(): propagating " << literal << std::endl;
      bool satValue;
      if (!d_valuation.hasSatValue(literal, satValue)) {
        d_out->propagate(literal);
      } else {
        if (!satValue) {
          Debug("arrays") << "TheoryArrays::propagate(): in conflict" << std::endl;
          Node negatedLiteral;
          std::vector<TNode> assumptions;
          if (literal != d_false) {
            negatedLiteral = literal.getKind() == kind::NOT ? (Node) literal[0] : literal.notNode();
            assumptions.push_back(negatedLiteral);
          }
          explain(literal, assumptions);
          d_conflictNode = mkAnd(assumptions);
          d_conflict = true;
          break;
        } else {
          Debug("arrays") << "TheoryArrays::propagate(): already asserted" << std::endl;
        }
      }
    }
  }

}


Node TheoryArrays::explain(TNode literal)
{
  ++d_numExplain;
  Debug("arrays") << "TheoryArrays::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::addSharedTerm(TNode t) {
  Debug("arrays::sharing") << "TheoryArrays::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t);
}


EqualityStatus TheoryArrays::getEqualityStatus(TNode a, TNode b) {
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b)) {
    // The rems are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  // All other terms we interpret as dis-equal in the model
  // TODO: check this
  return EQUALITY_FALSE_IN_MODEL;
}


void TheoryArrays::computeCareGraph(CareGraph& careGraph)
{
  // TODO
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


Node TheoryArrays::getValue(TNode n)
{
  // TODO: Implement this
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}


/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::presolve()
{
  Trace("arrays")<<"Presolving \n";
  d_donePreregister = true;
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::check(Effort e) {
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  if(!d_donePreregister ) {
    // only start looking for lemmas after preregister on all input terms
    // has been called
   return;
  }

  while (!done() && !d_conflict) 
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("arrays") << "TheoryArrays::check(): processing " << fact << std::endl;

    // If the assertion doesn't have a literal, it's a shared equality, so we set it up
    if (!assertion.isPreregistered) {
      Debug("arrays") << "TheoryArrays::check(): shared equality, setting up " << fact << std::endl;
      if (fact.getKind() == kind::NOT) {
        preRegisterTerm(fact[0]);
      } else {
        preRegisterTerm(fact);
      }
    }

    // Do the work
    switch (fact.getKind()) {
      case kind::EQUAL:
        d_equalityEngine.addEquality(fact[0], fact[1], fact);
        break;
      case kind::SELECT:
        d_equalityEngine.addEquality(fact, d_true, fact);
        break;
      case kind::NOT:
        if (fact[0].getKind() == kind::SELECT) {
          d_equalityEngine.addEquality(fact[0], d_false, fact);
        } else if (!d_equalityEngine.areDisequal(fact[0][0], fact[0][1])) {
          // Assert the dis-equality
          d_equalityEngine.addDisequality(fact[0][0], fact[0][1], fact);

          // Apply ArrDiseq Rule if diseq is between arrays
          if(fact[0][0].getType().isArray()) {
            NodeManager* nm = NodeManager::currentNM();
            TypeNode indexType = fact[0][0].getType()[0];
            Node k = nm->mkVar(indexType);
            // TODO: is this needed?  Better way to do this?
            if(Dump.isOn("declarations")) {
              stringstream kss;
              kss << Expr::setlanguage(Expr::setlanguage::getLanguage(Dump("declarations"))) << k;
              string ks = kss.str();
              Dump("declarations")
                << CommentCommand(ks + " is an extensional lemma index variable "
                                  "from the theory of arrays") << endl
                << DeclareFunctionCommand(ks, indexType.toType()) << endl;
            }
            Node ak = nm->mkNode(kind::SELECT, fact[0][0], k);
            Node bk = nm->mkNode(kind::SELECT, fact[0][1], k);
            d_equalityEngine.addDisequality(ak, bk, fact);
            Trace("arrays-lem")<<"Arrays::addExtLemma "<< ak << " /= " << bk <<"\n";
            ++d_numExt;
          }
        }
        break;
      default:
        Unreachable();
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    Debug("arrays") << "TheoryArrays::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
  }

  // Otherwise we propagate
  propagate(e);

  // if(fullEffort(e)) {
  //   // generate the lemmas on the worklist
  //   //while(!d_RowQueue.empty() || ! d_extQueue.empty()) {
  //   dischargeLemmas();
  //   Trace("arrays-lem")<<"Arrays::discharged lemmas "<<d_RowQueue.size()<<"\n";
  //   //}
  // }
  Trace("arrays") << "Arrays::check(): done" << endl;
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
