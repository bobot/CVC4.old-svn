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
#include "util/hash.h"

#include <iterator>

using namespace std;
using namespace CVC4::theory::uf::morgan;

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

SymmetryBreaker::Template::Template() :
  d_template(),
  d_assertions(kind::TUPLE),
  d_sets(),
  d_reps() {
}

TNode SymmetryBreaker::Template::find(TNode n) {
  hash_map<TNode, TNode, TNodeHashFunction>::iterator i = d_reps.find(n);
  if(i == d_reps.end()) {
    return n;
  } else {
    return d_reps[n] = find((*i).second);
  }
}

bool SymmetryBreaker::Template::matchRecursive(TNode t, TNode n) {
  IndentedScope scope(Debug("ufsymm:match"));

  Debug("ufsymm:match") << "UFSYMM matching " << t << endl
                        << "UFSYMM       to " << n << endl;

  if(t.getKind() != n.getKind() || t.getNumChildren() != n.getNumChildren()) {
    Debug("ufsymm:match") << "UFSYMM BAD MATCH on kind, #children" << endl;
    return false;
  }

  if(t.getNumChildren() == 0) {
    Assert(t.getMetaKind() == kind::metakind::VARIABLE);
    Assert(n.getMetaKind() == kind::metakind::VARIABLE);
    t = find(t);
    n = find(n);
    Debug("ufsymm:match") << "UFSYMM variable match " << t << " , " << n << endl;
    Debug("ufsymm:match") << "UFSYMM sets: " << t << " =>";
    if(d_sets.find(t) != d_sets.end()) {
      for(set<TNode>::iterator i = d_sets[t].begin(); i != d_sets[t].end(); ++i) {
        Debug("ufsymm:match") << " " << *i;
      }
    }
    Debug("ufsymm:match") << endl;
    if(t != n) {
      Debug("ufsymm:match") << "UFSYMM sets: " << n << " =>";
      if(d_sets.find(n) != d_sets.end()) {
        for(set<TNode>::iterator i = d_sets[n].begin(); i != d_sets[n].end(); ++i) {
          Debug("ufsymm:match") << " " << *i;
        }
      }
      Debug("ufsymm:match") << endl;

      if(d_sets.find(t) == d_sets.end()) {
        Debug("ufsymm:match") << "UFSYMM inserting " << t << " in with " << n << endl;
        d_reps[t] = n;
        d_sets[n].insert(t);
      } else {
        if(d_sets.find(n) != d_sets.end()) {
          Debug("ufsymm:match") << "UFSYMM merging " << n << " and " << t << " in with " << n << endl;
          d_sets[n].insert(d_sets[t].begin(), d_sets[t].end());
          d_sets[n].insert(t);
          d_reps[t] = n;
          d_sets.erase(t);
        } else {
          Debug("ufsymm:match") << "UFSYMM inserting " << n << " in with " << t << endl;
          d_sets[t].insert(n);
          d_reps[n] = t;
        }
      }
    }
    return true;
  }

  Assert(t.getMetaKind() != kind::metakind::PARAMETERIZED);
  TNode::iterator ti = t.begin();
  TNode::iterator ni = n.begin();
  while(ti != t.end()) {
    if(*ti != *ni) { // nothing to do if equal
      if(!matchRecursive(*ti, *ni)) {
        Debug("ufsymm:match") << "UFSYMM BAD MATCH, withdrawing.." << endl;
        return false;
      }
    }
    ++ti;
    ++ni;
  }

  return true;
}

bool SymmetryBreaker::Template::match(TNode n) {
  // try to "match" n and d_template
  if(d_template.isNull()) {
    Debug("ufsymm") << "UFSYMM setting template " << n << endl;
    d_template = n;
    d_assertions << n;
    return true;
  } else {
    bool good = matchRecursive(d_template, n);
    if(good) {
      d_assertions << n;
    }
    return good;
  }
}

void SymmetryBreaker::Template::reset() {
  d_template = Node::null();
  d_assertions.clear(kind::TUPLE);
  d_sets.clear();
  d_reps.clear();
}

void SymmetryBreaker::assertFormula(TNode phi) {
  // use d_phi, put into d_permutations
  Debug("ufsymm") << "UFSYMM assertFormula(): phi is " << phi << endl;
  d_phi.push_back(phi);
  if(phi.getKind() == kind::NOT) {
    // don't do anything with NOTs
    return;
  } else if(phi.getKind() == kind::OR) {
    Template t;
    TNode::iterator i = phi.begin();
    t.match(*i++);
    while(i != phi.end()) {
      if(!t.match(*i++)) {
        break;
      }
    }
    hash_map<TNode, set<TNode>, TNodeHashFunction>& ps = t.partitions();
    for(hash_map<TNode, set<TNode>, TNodeHashFunction>::iterator i = ps.begin();
        i != ps.end();
        ++i) {
      Debug("ufsymm") << "UFSYMM partition*: " << (*i).first;
      set<TNode>& p = (*i).second;
      for(set<TNode>::iterator j = p.begin();
          j != p.end();
          ++j) {
        Debug("ufsymm") << " " << *j;
      }
      Debug("ufsymm") << endl;
      p.insert((*i).first);
      Permutations::iterator pi = d_permutations.find(p);
      if(pi == d_permutations.end()) {
        d_permutations.insert(make_pair(p, phi));
      } else {
        Node n = d_permutations[p];
        if(n.getKind() == kind::OR) {
          d_permutations[p] = NodeManager::currentNM()->mkNode(kind::TUPLE, n, phi);
        } else {
          Assert(n.getKind() == kind::TUPLE);
          NodeBuilder<> b(kind::TUPLE);
          for(Node::iterator ni = n.begin(); ni != n.end(); ++ni) {
            b << *ni;
          }
          b << phi;
          d_permutations[p] = Node(b);
        }
      }
    }
  }
  if(!d_template.match(phi)) {
    // we hit a bad match, extract the partitions and reset the template
    Debug("ufsymm") << "UFSYMM hit a bad match---have partitions:" << endl;
    hash_map<TNode, set<TNode>, TNodeHashFunction>& ps = d_template.partitions();
    for(hash_map<TNode, set<TNode>, TNodeHashFunction>::iterator i = ps.begin();
        i != ps.end();
        ++i) {
      Debug("ufsymm") << "UFSYMM partition: " << (*i).first;
      set<TNode>& p = (*i).second;
      for(set<TNode>::iterator j = p.begin();
          j != p.end();
          ++j) {
        Debug("ufsymm") << " " << *j;
      }
      Debug("ufsymm") << endl;
      p.insert((*i).first);
      d_permutations.insert(make_pair(p, d_template.assertions()));
    }
    d_template.reset();
    bool good CVC4_UNUSED = d_template.match(phi);
    Assert(good);
  }
}

void SymmetryBreaker::clear() {
  d_phi.clear();
  d_permutations.clear();
  d_terms.clear();
  d_template.reset();
}

void SymmetryBreaker::apply(std::vector<Node>& newClauses) {
  guessPermutations();
  for(Permutations::iterator i = d_permutations.begin();
      i != d_permutations.end();
      ++i) {
    Debug("ufsymm") << "UFSYMM =====================================================" << endl;
    const pair<Permutation, Node>& pr = *i;
    const Permutation& p = pr.first;
    Debug("ufsymm") << "UFSYMM looking at permutation: " << p << endl;
    size_t n = p.size() - 1;
    if(invariantByPermutations(p)) {
      selectTerms(p, pr.second);
      set<Node> cts;
      while(!d_terms.empty() && cts.size() <= n) {
        Debug("ufsymm") << "UFSYMM ==== top of loop, d_terms.size() == " << d_terms.size() << " , cts.size() == " << cts.size() << " , n == " << n << endl;
        Terms::iterator ti = selectMostPromisingTerm(d_terms);
        Node t = *ti;
        Debug("ufsymm") << "UFSYMM promising term is " << t << endl;
        d_terms.erase(ti);
        insertUsedIn(t, p, cts);
        if(Debug.isOn("ufsymm")) {
          if(cts.empty()) {
            Debug("ufsymm") << "UFSYMM cts is empty" << endl;
          } else {
            for(set<Node>::iterator ctsi = cts.begin(); ctsi != cts.end(); ++ctsi) {
              Debug("ufsymm") << "UFSYMM cts: " << *ctsi << endl;
            }
          }
        }
        TNode c;
        set<TNode>::const_iterator i;
        for(i = p.begin(); i != p.end(); ++i) {
          if(cts.find(*i) == cts.end()) {
            if(c.isNull()) {
              c = *i;
              Debug("ufsymm") << "UFSYMM found first: " << c << endl;
            } else {
              Debug("ufsymm") << "UFSYMM found second: " << *i << endl;
              break;
            }
          }
        }
        Assert(!c.isNull());
        Debug("ufsymm") << "UFSYMM inserting into cts: " << c << endl;
        cts.insert(c);
        // This tests cts != p: if "i == p.end()", we got all the way
        // through p without seeing two elements not in cts (on the
        // second one, we break from the above loop).  We know we
        // found at least one (and subsequently added it to cts).  So
        // now cts == p.
        Debug("ufsymm") << "UFSYMM p == " << p << endl;
        if(i != p.end() || p.size() != cts.size()) {
          Debug("ufsymm") << "UFSYMM cts != p" << endl;
          NodeBuilder<> disj(kind::OR);
          for(set<Node>::const_iterator i = cts.begin();
              i != cts.end();
              ++i) {
            if(t != *i) {
              disj << NodeManager::currentNM()->mkNode(kind::EQUAL, t, *i);
            }
          }
          Node d;
          if(disj.getNumChildren() > 1) {
            d = disj;
            ++d_clauses;
          } else {
            d = disj[0];
            disj.clear();
            ++d_units;
          }
          Debug("ufsymm") << "UFSYMM clause: " << d << endl;
          newClauses.push_back(d);
        } else {
          Debug("ufsymm") << "UFSYMM cts == p" << endl;
        }
        Debug("ufsymm") << "UFSYMM ==== end of loop, d_terms.size() == " << d_terms.size() << " , cts.size() == " << cts.size() << " , n == " << n << endl;
      }
    }
  }

  clear();
}

void SymmetryBreaker::guessPermutations() {
  // use d_phi, put into d_permutations
  Debug("ufsymm") << "UFSYMM guessPermutations()" << endl;
}

bool SymmetryBreaker::invariantByPermutations(const Permutation& p) {
  // use d_phi
  Debug("ufsymm") << "UFSYMM invariantByPermutations(): " << p << endl;
  // FIXME
  return true;
}

void SymmetryBreaker::selectTerms(const Permutation& p, TNode reason) {
  // use d_phi, put into d_terms
  Debug("ufsymm") << "UFSYMM selectTerms(): " << p << " [" << reason << "]" << endl;
  d_terms.clear();
  set<Node> terms;
  if(reason.getKind() == kind::OR) {
    for(Node::iterator i = reason.begin(); i != reason.end(); ++i) {
      if((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF) {
        if(find(p.begin(), p.end(), (*i)[0]) == p.end()) {
          Assert(find(p.begin(), p.end(), (*i)[1]) != p.end());
          terms.insert((*i)[0]);
        } else {
          terms.insert((*i)[1]);
        }
      }
    }
  } else if(reason.getKind() == kind::TUPLE) {
    for(Node::iterator n = reason.begin(); n != reason.end(); ++n) {
      if((*n).getKind() == kind::OR) {
        for(Node::iterator i = (*n).begin(); i != (*n).end(); ++i) {
          if((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF) {
            if(find(p.begin(), p.end(), (*i)[0]) == p.end()) {
              Assert(find(p.begin(), p.end(), (*i)[1]) != p.end());
              terms.insert((*i)[0]);
            } else {
              terms.insert((*i)[1]);
            }
          }
        }
      }
    }
  }
  d_terms.insert(d_terms.end(), terms.begin(), terms.end());
  if(Debug.isOn("ufsymm")) {
    for(list<Term>::iterator i = d_terms.begin(); i != d_terms.end(); ++i) {
      Debug("ufsymm") << "UFSYMM selectTerms() returning: " << *i << endl;
    }
  }
}

SymmetryBreaker::Terms::iterator
SymmetryBreaker::selectMostPromisingTerm(Terms& terms) {
  // use d_phi
  Debug("ufsymm") << "UFSYMM selectMostPromisingTerm()" << endl;
  return terms.begin();
}

void SymmetryBreaker::insertUsedIn(Term term, const Permutation& p, set<Node>& cts) {
  // insert terms from p used in term into cts
  //Debug("ufsymm") << "UFSYMM usedIn(): " << term << " , " << p << endl;
  if(find(p.begin(), p.end(), term) != p.end()) {
    cts.insert(term);
  } else {
    for(TNode::iterator i = term.begin(); i != term.end(); ++i) {
      insertUsedIn(*i, p, cts);
    }
  }
}

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, const SymmetryBreaker::Permutation& p) {
  out << "{";
  set<TNode>::const_iterator i = p.begin();
  while(i != p.end()) {
    out << *i;
    if(++i != p.end()) {
      out << ",";
    }
  }
  out << "}";
  return out;
}

}/* CVC4 namespace */
