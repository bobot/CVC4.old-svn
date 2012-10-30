/*********************                                                        */
/*! \file inst_gen.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Inst Gen classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_GEN_H
#define __CVC4__THEORY__QUANTIFIERS__INST_GEN_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/inst_match.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstGenProcess
{
private:
  //the node we are processing
  Node d_node;
  //the sub children for this node
  std::vector< InstGenProcess > d_children;
  std::vector< int > d_children_index;
  std::map< int, int > d_children_map;
  //the matches we have produced
  std::vector< InstMatch > d_matches;
  std::vector< Node > d_match_values;
  //add match value
  std::map< Node, inst::InstMatchTrie > d_inst_trie;
  void addMatchValue( QuantifiersEngine* qe, Node f, Node val, InstMatch& m );
private:
  void calculateMatchesUninterpreted( QuantifiersEngine* qe, Node f, InstMatch& curr, Node n, int childIndex, bool isSelected );
  void calculateMatchesInterpreted( QuantifiersEngine* qe, Node f, InstMatch& curr, std::vector< Node >& terms, int argIndex );
public:
  InstGenProcess( Node n );
  virtual ~InstGenProcess(){}

  void calculateMatches( QuantifiersEngine* qe, Node f, std::vector< Node >& considerVal, bool useConsider );
  int getNumMatches() { return d_matches.size(); }
  bool getMatch( EqualityQuery* q, int i, InstMatch& m );
  Node getMatchValue( int i ) { return d_match_values[i]; }
};

}
}
}

#endif
