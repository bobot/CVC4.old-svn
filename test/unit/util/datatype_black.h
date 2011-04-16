/*********************                                                        */
/*! \file datatype_black.h
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
 ** \brief Black box testing of CVC4::Datatype
 **
 ** Black box testing of CVC4::Datatype.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/datatype.h"

#include "expr/expr.h"
#include "expr/expr_manager.h"

using namespace CVC4;
using namespace std;

class DatatypeBlack : public CxxTest::TestSuite {

  ExprManager* d_em;

public:

  void setUp() {
    d_em = new ExprManager();
  }

  void tearDown() {
    delete d_em;
  }

  void testTree() {
    Datatype tree("tree");

    Datatype::Constructor node("node", "is_node");
    node.addArg("left", Datatype::SelfType());
    node.addArg("right", Datatype::SelfType());
    tree.addConstructor(node);

    Datatype::Constructor leaf("leaf", "is_leaf");
    tree.addConstructor(leaf);

    cout << tree << std::endl;
    DatatypeType treeType = d_em->mkDatatypeType(tree);
    cout << treeType << std::endl;
  }

  void testNat() {
    Datatype nat("nat");

    Datatype::Constructor succ("succ", "is_succ");
    succ.addArg("pred", Datatype::SelfType());
    nat.addConstructor(succ);

    Datatype::Constructor zero("zero", "is_zero");
    nat.addConstructor(zero);

    cout << nat << std::endl;
    DatatypeType natType = d_em->mkDatatypeType(nat);
    cout << natType << std::endl;
  }

  void testList() {
    Datatype list("list");
    Type integerType = d_em->integerType();

    Datatype::Constructor cons("cons", "is_cons");
    cons.addArg("car", integerType);
    cons.addArg("cdr", Datatype::SelfType());
    list.addConstructor(cons);

    Datatype::Constructor nil("nil", "is_nil");
    list.addConstructor(nil);

    cout << list << std::endl;
    DatatypeType listType = d_em->mkDatatypeType(list);
    DatatypeType listType2 = d_em->mkDatatypeType(list);
    cout << listType << std::endl;
    TS_ASSERT(listType == listType2);
  }

};
