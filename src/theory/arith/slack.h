/*********************                                                        */
/*! \file slack.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

struct SlackAttrID;

typedef expr::Attribute<SlackAttrID, Node> Slack;

struct ReverseSlackAttrID;
typedef expr::Attribute<ReverseSlackAttrID, Node> ReverseSlack;


inline bool isSlack(TNode v){
  return v.hasAttribute(ReverseSlack());
}

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

