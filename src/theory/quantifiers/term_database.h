/**********************/
/*! \file term_database.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_TERM_DATABASE_H
#define __CVC4__QUANTIFIERS_TERM_DATABASE_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class TermArgTrie {
private:
  bool addTerm2( QuantifiersEngine* qe, Node n, int argIndex );
public:
  /** the data */
  std::map< Node, TermArgTrie > d_data;
public:
  bool addTerm( QuantifiersEngine* qe, Node n ) { return addTerm2( qe, n, 0 ); }
};/* class TermArgTrie */

class TermDb {
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** calculated no match terms */
  bool d_matching_active;
  /** terms processed */
  std::map< Node, bool > d_processed;
public:
  TermDb( QuantifiersEngine* qe ) : d_quantEngine( qe ), d_matching_active( true ){}
  ~TermDb(){}
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from APPLY_UF functions to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  /** map from APPLY_UF predicates to trie */
  std::map< Node, TermArgTrie > d_pred_map_trie[2];
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** add a term to the database */
  void addTerm( Node n, std::vector< Node >& added, bool withinQuant = false );
  /** reset (calculate which terms are active) */
  void reset( Theory::Effort effort );
  /** set active */
  void setMatchingActive( bool a ) { d_matching_active = a; }
  /** get active */
  bool getMatchingActive() { return d_matching_active; }
public:
  /** parent structure (for efficient E-matching):
      n -> op -> index -> L
      map from node "n" to a list of nodes "L", where each node n' in L
        has operator "op", and n'["index"] = n.
      for example, d_parents[n][f][1] = { f( t1, n ), f( t2, n ), ... }
  */
  std::map< Node, std::map< Node, std::map< int, std::vector< Node > > > > d_parents;
};/* class TermDb */

}
}
}

#endif
