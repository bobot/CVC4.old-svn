/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of algorithm suggested by Deharbe, Fontaine,
 ** Merz, and Paleo, "Exploiting symmetry in SMT problems," CADE 2011
 **
 ** Implementation of algorithm suggested by Deharbe, Fontaine,
 ** Merz, and Paleo, "Exploiting symmetry in SMT problems," CADE 2011.
 **
 ** From the paper:
 **
 ** <pre>
 **   P := guess_permutations(phi)
 **   foreach {c_0, ..., c_n} \in P do
 **     if invariant_by_permutations(phi, {c_0, ..., c_n}) then
 **       T := select_terms(phi, {c_0, ..., c_n})
 **       cts := \empty
 **       while T != \empty && |cts| <= n do
 **         t := select_most_promising_term(T, phi)
 **         T := T \ {t}
 **         cts := cts \cup used_in(t, {c_0, ..., c_n})
 **         let c \in {c_0, ..., c_n} \ cts
 **         cts := cts \cup {c}
 **         if cts != {c_0, ..., c_n} then
 **           phi := phi /\ ( \vee_{c_i \in cts} t = c_i )
 **         end
 **       end
 **     end
 **   end
 **   return phi
 ** </pre>
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__MORGAN__SYMMETRY_BREAKER_H
#define __CVC4__THEORY__UF__MORGAN__SYMMETRY_BREAKER_H

#include <vector>
#include <list>

#include "expr/node.h"
#include "expr/node_builder.h"

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

class SymmetryBreaker {
  Node d_phi;

  typedef std::vector<TNode> Permutation;
  typedef std::vector<Permutation> Permutations;
  typedef TNode Term;
  typedef std::list<Term> Terms;

  Permutations d_permutations;
  Terms d_terms;

  void guessPermutations();
  bool invariantByPermutations(const Permutation& p);
  void selectTerms(const Permutation& p);
  Terms::iterator selectMostPromisingTerm(Terms& terms);
  Node usedIn(Term& term);

public:

  SymmetryBreaker(TNode phi) : d_phi(phi) {}
  void apply(NodeBuilder<>& newClauses);

};/* class SymmetryBreaker */

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__MORGAN__SYMMETRY_BREAKER_H */
