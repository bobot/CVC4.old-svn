/*********************                                                        */
/*! \file dagification_visitor.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011, 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of a dagifier for CVC4 expressions
 **
 ** Implementation of a dagifier for CVC4 expressions.
 **/

#include "printer/dagification_visitor.h"

#include "context/context.h"
#include "theory/substitutions.h"

#include <sstream>

namespace CVC4 {
namespace printer {

DagificationVisitor::DagificationVisitor(unsigned threshold, std::string letVarPrefix) :
  d_threshold(threshold),
  d_letVarPrefix(letVarPrefix),
  d_nodeCount(),
  d_top(),
  d_context(new context::Context()),
  d_substitutions(new theory::SubstitutionMap(d_context)),
  d_letVar(0),
  d_done(false),
  d_uniqueParent(),
  d_substNodes() {

  // 0 doesn't make sense
  CheckArgument(threshold > 0, threshold);
}

DagificationVisitor::~DagificationVisitor() {
  delete d_substitutions;
  delete d_context;
}

bool DagificationVisitor::alreadyVisited(TNode current, TNode parent) {
  // don't visit variables, constants, or those exprs that we've
  // already seen more than the threshold: if we've increased
  // the count beyond the threshold already, we've done the same
  // for all subexpressions, so it isn't useful to traverse and
  // increment again (they'll be dagified anyway).
  return current.getMetaKind() == kind::metakind::VARIABLE ||
         current.getMetaKind() == kind::metakind::CONSTANT ||
         ( ( current.getKind() == kind::NOT ||
             current.getKind() == kind::UMINUS ) &&
           ( current[0].getMetaKind() == kind::metakind::VARIABLE ||
             current[0].getMetaKind() == kind::metakind::CONSTANT ) ) ||
         current.getKind() == kind::SORT_TYPE ||
         d_nodeCount[current] > d_threshold;
}

void DagificationVisitor::visit(TNode current, TNode parent) {
  if(d_uniqueParent.find(current) != d_uniqueParent.end()) {
    // we've seen this expr before

    TNode& uniqueParent = d_uniqueParent[current];

    if(!uniqueParent.isNull() && uniqueParent != parent) {
      // there is not a unique parent for this expr, mark it
      uniqueParent = TNode::null();
    }

    // increase the count
    const unsigned count = ++d_nodeCount[current];

    if(count > d_threshold) {
      // candidate for a let binder
      d_substNodes.push_back(current);
    }
  } else {
    // we haven't seen this expr before
    Assert(d_nodeCount[current] == 0);
    d_nodeCount[current] = 1;
    d_uniqueParent[current] = parent;
  }
}

void DagificationVisitor::start(TNode node) {
  AlwaysAssert(!d_done, "DagificationVisitor cannot be re-used");
  d_top = node;
}

void DagificationVisitor::done(TNode node) {
  AlwaysAssert(!d_done);

  d_done = true;

  // letify subexprs before parents (cascading LETs)
  std::sort(d_substNodes.begin(), d_substNodes.end());

  for(std::vector<TNode>::iterator i = d_substNodes.begin();
      i != d_substNodes.end();
      ++i) {
    Assert(d_nodeCount[*i] > d_threshold);
    TNode parent = d_uniqueParent[*i];
    if(!parent.isNull() && d_nodeCount[parent] > d_threshold) {
      // no need to letify this expr, because it only occurs in
      // a single super-expression, and that one will be letified
      continue;
    }

    // construct the let binder
    std::stringstream ss;
    ss << d_letVarPrefix << d_letVar++;
    Node letvar = NodeManager::currentNM()->mkVar(ss.str(), (*i).getType());

    // apply previous substitutions to the rhs, enabling cascading LETs
    Node n = d_substitutions->apply(*i);
    Assert(! d_substitutions->hasSubstitution(n));
    d_substitutions->addSubstitution(n, letvar);
  }
}

const theory::SubstitutionMap& DagificationVisitor::getLets() {
  AlwaysAssert(d_done, "DagificationVisitor must be used as a visitor before getting the dagified version out!");
  return *d_substitutions;
}

Node DagificationVisitor::getDagifiedBody() {
  AlwaysAssert(d_done, "DagificationVisitor must be used as a visitor before getting the dagified version out!");
  return d_substitutions->apply(d_top);
}

}/* CVC4::printer namespace */
}/* CVC4 namespace */
