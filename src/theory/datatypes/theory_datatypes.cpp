/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of datatypes.
 **
 ** Implementation of the theory of datatypes.
 **/


#include "theory/datatypes/theory_datatypes.h"
#include "theory/theory_engine.h"
#include "expr/kind.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;


TheoryDatatypes::TheoryDatatypes(int id, Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict()
{
}


TheoryDatatypes::~TheoryDatatypes() {
}


RewriteResponse TheoryDatatypes::preRewrite(TNode in, bool topLevel) {
  Debug("datatypes-rewrite") << "pre-rewriting " << in
                          << " topLevel==" << topLevel << std::endl;

  return RewriteComplete(in);
}

RewriteResponse TheoryDatatypes::postRewrite(TNode in, bool topLevel) {
  Debug("datatypes-rewrite") << "post-rewriting " << in
                          << " topLevel==" << topLevel << std::endl;

  if( in.getKind()==APPLY_TESTER &&
      in[0].getKind()==APPLY_CONSTRUCTOR ){
    TypeNode testConsType = (in.getOperator().getType())[0];
    TypeNode consType = in[0].getOperator().getType();
    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial tester " << in << endl;
    //Debug("datatypes-rewrite") << testConsType << endl;
    //Debug("datatypes-rewrite") << consType << endl;
    return RewriteComplete(NodeManager::currentNM()->mkConst(testConsType==consType));
  }
  if( in.getKind()==APPLY_SELECTOR &&
      in[0].getKind()==APPLY_CONSTRUCTOR ){

    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial selector " << in << endl;
    int selIndex = -1;
    int currIndex = 0;
    TypeNode selType = in.getOperator().getType();
    TypeNode c = in[0].getOperator().getType();
    TypeNode::iterator child_it = c.begin();
    TypeNode::iterator child_it_end = c.end();
    for(; child_it != child_it_end; ++child_it) {   //possibly improve this, store index in selector type?
      if( (*child_it)==selType ){
        selIndex = currIndex;
        break;
      }
      ++currIndex;
    }
    if( selIndex==-1 ){
      Debug("datatypes-rewrite") << "Applied selector to wrong constructor" << endl;
      //return distinguished term
      NodeManager* nm = NodeManager::currentNM();
      TypeNode tyn = nm->getType( in[0] );
      ostringstream os;
      os << "_term_" << in.getOperator();
      Node tn = nm->mkVar(os.str().c_str(), selType[1]);
      Debug("datatypes-rewrite") << "Return distinguished term " << tn << " of type " << selType[1] << endl;
      return RewriteComplete(tn);
    }else{
      Debug("datatypes-rewrite") << "Applied selector to correct constructor, index = " << selIndex << endl;
      Debug("datatypes-rewrite") << "Return " << in[0][selIndex] << endl;
      return RewriteComplete(in[0][selIndex]);
    }
  }

  return RewriteComplete(in);
}

void TheoryDatatypes::addConstructorDefinitions( std::vector<std::pair<Type, std::vector<Type> > >& defs ){
  //NodeManager* nm = NodeManager::currentNM();
  //std::vector< Node > distinguishTerms;
  //for( int i=0; i<(int)defs.size(); i++ ){
  //  //std::string name;
  //  //defs[i].first.getAttribute(expr::VarNameAttr(), name);
  //  ostringstream os;
  //  os << "_term_" << defs[i].first;
  //  Debug("datatypes") << "TheoryDatatypes:: create distinguish ground term " << os.str() << endl;
  //  //distinguishTerms.push_back( nm->mkVar(os.str().c_str(), defs[i].first) );
  //}
  d_defs.insert( d_defs.begin(), defs.begin(), defs.end() );
 // d_distinguishTerms.insert( d_distinguishTerms.begin(),distinguishTerms.begin(), distinguishTerms.end() );
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                  << t << endl;
}


void TheoryDatatypes::notifyEq(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyEq(): "
                  << lhs << " = " << rhs << endl;
}

void TheoryDatatypes::notifyCongruent(TNode a, TNode b) {
  
}


void TheoryDatatypes::presolve() {
  Unimplemented();
  //check that all the types are well-founded
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

void TheoryDatatypes::check(Effort e) {
  while(!done()) {
    Node assertion = get();
    Debug("datatypes") << "TheoryDatatypes::check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      
      break;
    case kind::APPLY_TESTER:
      checkTester( e, assertion, assertion );
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()){
        case kind::EQUAL:
        case kind::IFF:

          break;
        case kind::APPLY_TESTER:
          checkTester( e, assertion[0], assertion );
          break;
        default:
          Unhandled(assertion[0].getKind());
          break;
        }
      }
      break;
    default:
      Unhandled(assertion.getKind());
      break;
    }
  }
  Debug("datatypes") << "TheoryDatatypes::check(): done" << endl;
}

void TheoryDatatypes::checkTester( Effort e, Node tassertion, Node assertion ){
  TypeNode testConsType = (tassertion.getOperator().getType())[0];

  Assert( tassertion[0].getKind()!=kind::APPLY_CONSTRUCTOR );
  ////test the constructor type
  //TypeNode consType = tassertion[0].getOperator().getType();
  //if( (testConsType==consType)==(assertion.getKind()==NOT) ){
  //  Debug("datatypes") << "TheoryDatatypes::check(): Tester fail " << (assertion.getKind()==NOT) << std::endl;
  //  //generate conflict
  //  Debug("datatypes") << "Conflict =  " << assertion << std::endl;
  //  d_out->conflict( assertion, false );
  //}else{
  //  Debug("datatypes") << "TheoryDatatypes::check(): Tester pass " << (assertion.getKind()==NOT) << std::endl;
  //}
  //Debug("datatypes") << testConsType << std::endl;
  //Debug("datatypes") << consType << endl;

  

}

Node TheoryDatatypes::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();


}

void TheoryDatatypes::appendToDiseqList(TNode of, TNode eq) {
  Debug("datatypes") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator deq_i = d_disequalities.find(of);
  EqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  //if(Debug.isOn("uf")) {
  //  Debug("uf") << "  size is now " << deq->size() << endl;
  //}
}

void TheoryDatatypes::appendToEqList(TNode of, TNode eq) {
  Debug("datatypes") << "appending " << eq << endl
              << "  to eq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator eq_i = d_equalities.find(of);
  EqList* eql;
  if(eq_i == d_equalities.end()) {
    eql = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_equalities.insertDataFromContextMemory(of, eql);
  } else {
    eql = (*eq_i).second;
  }
  eql->push_back(eq);
  //if(Debug.isOn("uf")) {
  //  Debug("uf") << "  size is now " << eql->size() << endl;
  //}
}

void TheoryDatatypes::addDisequality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToDiseqList(find(a), eq);
  appendToDiseqList(find(b), eq);
}

void TheoryDatatypes::registerEqualityForPropagation(TNode eq) {
  // should NOT be in search at this point, this must be called during
  // preregistration

  // FIXME with lemmas on demand, this could miss future propagations,
  // since we are not necessarily at context level 0, but are updating
  // context-sensitive structures.

  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToEqList(find(a), eq);
  appendToEqList(find(b), eq);
}
