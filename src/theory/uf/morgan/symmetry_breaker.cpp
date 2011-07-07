/*********************                                                        */
/*! \file symmetry_breaker.cpp
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
 ** Implementation of algorithm suggested by Deharbe, Fontaine, Merz,
 ** and Paleo, "Exploiting symmetry in SMT problems," CADE 2011.
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

#include "theory/uf/morgan/symmetry_breaker.h"

#include <iterator>

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

void SymmetryBreaker::apply(NodeBuilder<>& newClauses) {
  guessPermutations();
  for(Permutations::iterator i = d_permutations.begin(); i != d_permutations.end(); ++i) {
    const Permutation& p = *i;
    size_t n = p.size() - 1;
    if(invariantByPermutations(p)) {
      selectTerms(p);
      vector<Node> cts;
      while(!d_terms.empty() && cts.size() <= n) {
        Terms::iterator t = selectMostPromisingTerm(d_terms);
        d_terms.erase(t);
        cts.push_back(usedIn(*t));
        // continue here...
      }
    }
  }
}

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
