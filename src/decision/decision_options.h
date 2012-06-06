/*********************                                                        */
/*! \file decision_options.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Decision options struct
 **
 ** This exists only because I don't want to put this in options.h
 ** and having to compile everything each time this changes. --K
 **/

namespace CVC4 {

/** DecisionOption along */
struct DecisionOptions {
  bool relevancyLeaves;
  unsigned short maxRelTimeInPermille;  /* permille = part per thousand */
};

/** default decision options */
const DecisionOptions defaultDecOpt = {
  false,
  1000
};

};/* CVC4 namespace */
