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

#include <map>


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

int TheoryDatatypes::getConstructorIndex( TypeNode t, Node c )
{
  std::map<TypeNode, std::vector<Node> >::iterator it = d_cons.find( t );
  if( it != d_cons.end() ){
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( it->second[i]==c ){
        return i;
      }
    }
  }
  return -1;
}
int TheoryDatatypes::getTesterIndex( TypeNode t, Node c )
{
  std::map<TypeNode, std::vector<Node> >::iterator it = d_testers.find( t );
  if( it != d_testers.end() ){
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( it->second[i]==c ){
        return i;
      }
    }
  }
  return -1;
}

void TheoryDatatypes::checkFiniteWellFounded(){
  if( requiresCheckFiniteWellFounded ){
    Debug("datatypes-finite") << "Check finite, well-founded." << std::endl;

    //check well-founded and finite, create distinguished ground terms
    std::map<TypeNode, std::vector<Node> >::iterator it;
    std::vector<Node>::iterator itc;
    for( it = d_cons.begin(); it!=d_cons.end(); ++it ){
      d_distinguishTerms[it->first] = Node::null();
      d_finite[it->first] = false;
      d_wellFounded[it->first] = false;
      for( itc = it->second.begin(); itc!=it->second.end(); ++itc ){
        d_cons_finite[*itc] = false;
        d_cons_wellFounded[*itc] = false;
      }
    }
    bool changed;
    do{
      changed = false;
      for( it = d_cons.begin(); it!=d_cons.end(); ++it ){
        TypeNode t = it->first;
        //Debug("datatypes-finite") << "check " << t << std::endl;
        bool typeFinite = true;
        for( itc = it->second.begin(); itc!=it->second.end(); ++itc ){
          Node cn = *itc;
          TypeNode ct = cn.getType();
          //Debug("datatypes-finite") << " check cons " << ct << std::endl;
          if( !d_cons_finite[cn] ){
            int c;
            for( c=0; c<(int)ct.getNumChildren()-1; c++ ){
              //Debug("datatypes-finite") << "  check sel " << ct[c] << std::endl;
              TypeNode ts = ct[c];
              //Debug("datatypes") << "  check : " << ts << std::endl;
              if( !isDatatype( ts ) || !d_finite[ ts ] ){
                break;
              }
            }
            if( c ==(int)ct.getNumChildren()-1 ){
              changed = true;
              d_cons_finite[cn] = true;
              //Debug("datatypes-finite") << ct << " is finite" << std::endl;
            }else{
              typeFinite = false;
            }
          }
          if( !d_cons_wellFounded[cn] ){
            int c;
            for( c=0; c<(int)ct.getNumChildren()-1; c++ ){
              //Debug("datatypes") << "  check sel " << ct.d_typeNode[0][c] << std::endl;
              TypeNode ts = ct[c];
              //Debug("datatypes") << "  check : " << ts << std::endl;
              if( isDatatype( ts ) && !d_wellFounded[ ts ] ){
                break;
              }
            }
            if( c ==(int)ct.getNumChildren()-1 ){
              changed = true;
              d_cons_wellFounded[cn] = true;
              //Debug("datatypes-finite") << ct << " is well founded" << std::endl;
            }
          }
          if( d_cons_wellFounded[cn] ){
            if( !d_wellFounded[t] ){
              changed = true;
              d_wellFounded[t] = true;
              //also set distinguished ground term
              //Debug("datatypes") << "set distinguished ground term out of " << ct << std::endl;
              //Debug("datatypes-finite") << t << " is type wf" << std::endl;
              NodeManager* nm = NodeManager::currentNM();
              std::vector< NodeTemplate<true> > children;
              children.push_back( cn );
              for( int c=0; c<(int)ct.getNumChildren()-1; c++ ){
                TypeNode ts = ct[c];
                if( isDatatype( ts ) ){
                  children.push_back( d_distinguishTerms[ts] );
                }else{
                  nm->mkVar( ts );
                }
              }
              Node dgt = nm->mkNode( APPLY_CONSTRUCTOR, children );
              Debug("datatypes-finite") << "set distinguished ground term " << t << " to " << dgt << std::endl;
              d_distinguishTerms[t] = dgt;
            }
          }
        }
        if( typeFinite && !d_finite[t] ){
          changed = true;
          d_finite[t] = true;
          Debug("datatypes-finite") << t << " now type finite" << std::endl;
        }
      }
    }while( changed );
    std::map<TypeNode, bool >::iterator itb;
    for( itb=d_finite.begin(); itb!=d_finite.end(); ++itb ){
      Debug("datatypes-finite") << itb->first << " is ";
      Debug("datatypes-finite") << ( itb->second ? "" : "not ") << "finite." << std::endl;
    }
    for( itb=d_wellFounded.begin(); itb!=d_wellFounded.end(); ++itb ){
      Debug("datatypes-finite") << itb->first << " is ";
      Debug("datatypes-finite") << ( itb->second ? "" : "not ") << "well founded." << std::endl;
      if( !itb->second && isDatatype( itb->first ) ){
        //throw exception?
      }
    }
    requiresCheckFiniteWellFounded = false;
  }
}

TheoryDatatypes::TheoryDatatypes(int id, Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_drv_map(c),
  d_labels(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict(), 
  d_conflict_is_input( false )
{
  requiresCheckFiniteWellFounded = true;
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

  checkFiniteWellFounded();

  if( in.getKind()==APPLY_TESTER &&
      in[0].getKind()==APPLY_CONSTRUCTOR ){
    TypeNode testType = in.getOperator().getType();
    TypeNode consType = in[0].getOperator().getType();
    int testIndex = getTesterIndex( testType[0], in.getOperator() );
    int consIndex = getConstructorIndex( testType[0], in[0].getOperator() );
    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial tester " << in << endl;
    Debug("datatypes-rewrite") << testType << " " << in.getOperator() << " " << testIndex << endl;
    Debug("datatypes-rewrite") << consType << " " << in[0].getOperator() << " " << consIndex << endl;
    return RewriteComplete(NodeManager::currentNM()->mkConst(testIndex==consIndex));
  }
  if( in.getKind()==APPLY_SELECTOR &&
      in[0].getKind()==APPLY_CONSTRUCTOR ){

    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial selector " << in << endl;
    int selIndex = -1;
    Node sel = in.getOperator();
    TypeNode selType = sel.getType();
    Node cons = in[0].getOperator();
    for(int i=0; i<(int)d_sels[cons].size(); i++ ) {
      if( d_sels[cons][i]==sel ){
        selIndex = i;
        break;
      }
    }
    if( selIndex==-1 ){
      Debug("datatypes-rewrite") << "Applied selector to wrong constructor " << sel << endl;
      Debug("datatypes-rewrite") << "Return distinguished term ";
      Debug("datatypes-rewrite") << d_distinguishTerms[ selType[1] ] << " of type " << selType[1] << endl;
      return RewriteComplete( d_distinguishTerms[ selType[1] ] );
    }else{
      Debug("datatypes-rewrite") << "Applied selector to correct constructor, index = " << selIndex << endl;
      Debug("datatypes-rewrite") << "Return " << in[0][selIndex] << endl;
      return RewriteComplete( in[0][selIndex] );
    }
  }
  if( in.getKind()==kind::EQUAL && in[0]==in[1] ){
    return RewriteComplete(NodeManager::currentNM()->mkConst(true));
  }
  if( in.getKind()==kind::NOT && in[0].getKind()==kind::EQUAL && in[0][0]==in[0][1] ){
    return RewriteComplete(NodeManager::currentNM()->mkConst(false));
  }
  if( in.getKind()==kind::EQUAL && d_unionFind.isInconsistentConstructor( in[0], in[1] ) ){
    return RewriteComplete(NodeManager::currentNM()->mkConst(false));
  }

  return RewriteComplete(in);
}

void TheoryDatatypes::addDatatypeDefinitions( std::vector<std::pair< TypeNode, std::vector<Node> > >& cons,
                                              std::vector<std::pair< TypeNode, std::vector<Node> > >& testers,
                                              std::vector<std::pair< Node, std::vector<Node> > >& sels ){
  std::vector<std::pair< TypeNode, std::vector<Node> > >::iterator it;
  std::vector<Node>::iterator itc;
  for( it = cons.begin(); it!=cons.end(); ++it ){
    for( itc = it->second.begin(); itc!=it->second.end(); ++itc ){
      d_cons[it->first].push_back( *itc );
    }
  }
  for( it = testers.begin(); it!=testers.end(); ++it ){
    for( itc = it->second.begin(); itc!=it->second.end(); ++itc ){
      d_testers[it->first].push_back( *itc );
    }
  }
  std::vector<std::pair< Node, std::vector<Node> > >::iterator it2;
  for( it2 = sels.begin(); it2!=sels.end(); ++it2 ){
    for( itc = it2->second.begin(); itc!=it2->second.end(); ++itc ){
      d_sels[it2->first].push_back( *itc );
    }
  }
  requiresCheckFiniteWellFounded = true;
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                  << t << endl;
}


void TheoryDatatypes::notifyEq(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyEq(): "
                  << lhs << " = " << rhs << endl;
  //d_unionFind.setCanon(lhs, rhs);  //FIXME?
  //NodeManager* nm = NodeManager::currentNM();
  //Node eq = nm->mkNode(kind::EQUAL, lhs, rhs);
  //addEquality(eq);
}

void TheoryDatatypes::notifyCongruent(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyCongruent(): "
                  << lhs << " = " << rhs << endl;
  if(!d_conflict.isNull()) {
    return;
  }
  merge(lhs,rhs);
}


void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
  checkFiniteWellFounded();
}

void TheoryDatatypes::check(Effort e) {
  while(!done()) {
    Node assertion = get();
    Debug("datatypes") << "TheoryDatatypes::check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      addEquality(assertion);
      if(!d_conflict.isNull()) {
        Node conflict = constructConflict(d_conflict, d_conflict_is_input);
        d_conflict = Node::null();
        //++d_conflicts;
        d_out->conflict(conflict, false);
        return;
      }
      merge(assertion[0], assertion[1]);
      if(!d_conflict.isNull()) {
        Node conflict = constructConflict(d_conflict, d_conflict_is_input);
        d_conflict = Node::null();
        //++d_conflicts;
        d_out->conflict(conflict, false);
        return;
      }
      break;
    case kind::APPLY_TESTER:
      if( checkTester( e, assertion, assertion ) ){
        return;
      }
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()){
        case kind::EQUAL:
        case kind::IFF:
          {
            Node a = assertion[0][0];
            Node b = assertion[0][1];
            addDisequality(assertion[0]);
            d_cc.addTerm(a);
            d_cc.addTerm(b);
            if(Debug.isOn("datatypes")) {
              Debug("datatypes") << "       a  ==> " << a << endl
                          << "       b  ==> " << b << endl
                          << "  find(a) ==> " << debugFind(a) << endl
                          << "  find(b) ==> " << debugFind(b) << endl;
            }
            // There are two ways to get a conflict here.
            if(!d_conflict.isNull()) {
              // We get a conflict this way if we weren't watching a, b
              // before and we were just now notified (via
              // notifyCongruent()) when we called addTerm() above that
              // they are congruent.  We make this a separate case (even
              // though the check in the "else if.." below would also
              // catch it, so that we can clear out d_conflict.
              Node conflict = constructConflict(d_conflict, d_conflict_is_input);
              d_conflict = Node::null();
              //++d_conflicts;
              d_out->conflict(conflict, false);
              return;
            } else if(find(a) == find(b)) {
              // We get a conflict this way if we WERE previously watching
              // a, b and were notified previously (via notifyCongruent())
              // that they were congruent.
              Node conflict = constructConflict(assertion[0]);
              //++d_conflicts;
              d_out->conflict(conflict, false);
              return;
            }

            // If we get this far, there should be nothing conflicting due
            // to this disequality.
            Assert(!d_cc.areCongruent(a, b));
          }
          break;
        case kind::APPLY_TESTER:
          if( checkTester( e, assertion[0], assertion ) ){
            return;
          }
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

bool TheoryDatatypes::checkTester( Effort e, Node tassertion, Node assertion ){
  Debug("datatypes") << "check tester " << assertion << std::endl;
  Assert( tassertion[0].getKind()!=kind::APPLY_CONSTRUCTOR );

  EqLists::iterator lbl_i = d_labels.find(tassertion[0]);
  if(lbl_i == d_labels.end()) {
    EqList* lbl = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    lbl->push_back( assertion );
    d_labels.insertDataFromContextMemory(tassertion[0], lbl);
  }else{
    EqList* lbl = (*lbl_i).second;
    Debug("datatypes") << "label = " << lbl << std::endl;

    //check if empty label (no possible constructors for term)
    Node conflict = Node::null();
    bool add = true;
    int notCount = 0;
    for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
      TNode leqn = (*i);
      if( leqn.getKind()==kind::NOT ){
        if( leqn[0].getOperator()==tassertion.getOperator() ){
          if( assertion.getKind()==NOT ){
            add = false;
          }else{
            NodeBuilder<> nb(kind::AND);
            nb << leqn << assertion;
            conflict = nb;
            Debug("datatypes") << "Contradictory labels " << conflict << std::endl;
          }
          break;
        }
        notCount++;
      }else{
        if( (leqn.getOperator()==tassertion.getOperator()) == (assertion.getKind()==NOT) ){
          NodeBuilder<> nb(kind::AND);
          nb << leqn << assertion;
          conflict = nb;
          Debug("datatypes") << "Contradictory labels2 " << conflict << std::endl;
        }
        add = false;
        break;
      }
    }
    if( !conflict.isNull() ){
      d_out->conflict( conflict, false );
      return true;
    }
    if( add ){
      if( assertion.getKind()==NOT && notCount==(int)d_cons[ tassertion[0].getType() ].size()-1 ){
        NodeBuilder<> nb(kind::AND);
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          nb << (*i);
        }
        nb << assertion;
        Node conflict = nb;
        d_out->conflict( conflict, false ); 
        Debug("datatypes") << "Exhausted possibilities for labels " << conflict << std::endl;
        return true;
      }
      lbl->push_back( assertion );
      Debug("datatypes") << "Add to labels " << lbl->size() << std::endl;
    }
  }
  return false;
}

Node TheoryDatatypes::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( engine->getValue(n[0]) == engine->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryDatatypes::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());
  Debug("datatypes") << "Merge " << a << " " << b << std::endl;

  // make "a" the one with shorter diseqList
  EqLists::iterator deq_ia = d_disequalities.find(a);
  EqLists::iterator deq_ib = d_disequalities.find(b);

  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
    }
  }
  a = find(a);
  b = find(b);

  if( a == b) {
    return;
  }

  // b becomes the canon of a
  Node clash = d_unionFind.checkInconsistent( a, b );
  if( !clash.isNull() ){
    Debug("datatypes") << "Clash " << a << " " << clash << std::endl;
    d_conflict = NodeManager::currentNM()->mkNode( EQUAL, a, clash );
    d_conflict_is_input = false;
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  d_unionFind.setCanon(a, b);

  deq_ia = d_disequalities.find(a);
  map<TNode, TNode> alreadyDiseqs;
  if(deq_ia != d_disequalities.end()) {
    /*
     * Collecting the disequalities of b, no need to check for conflicts
     * since the representative of b does not change and we check all the things
     * in a's class when we look at the diseq list of find(a)
     */

    EqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      EqList* deq = (*deq_ib).second;
      for(EqList::const_iterator j = deq->begin(); j!=deq->end(); j++) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b);
        if(sp == b) {
          alreadyDiseqs[tp] = deqn;
        } else {
          alreadyDiseqs[sp] = deqn;
        }
      }
    }

    /*
     * Looking for conflicts in the a disequality list. Note
     * that at this point a and b are already merged. Also has
     * the side effect that it adds them to the list of b (which
     * became the canonical representative)
     */

    EqList* deqa = (*deq_ia).second;
    for(EqList::const_iterator i = deqa->begin(); i!= deqa->end(); i++) {
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      TNode sp = deqn[0];
      TNode tp = deqn[1];

      if(find(s) == find(t)) {
        d_conflict = deqn;
        d_conflict_is_input = true;
        return;
      }
      Assert( sp == b || tp == b);

      // make sure not to add duplicates

      if(sp == b) {
        if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[tp] = deqn;
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[sp] = deqn;
        }
      }

    }
  }

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

void TheoryDatatypes::addEquality(TNode eq){
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  d_cc.addEquality(eq);
  //do unification
  if( eq[0].getKind()==APPLY_CONSTRUCTOR && eq[1].getKind()==APPLY_CONSTRUCTOR &&
    eq[0].getOperator()==eq[1].getOperator() ){
    Debug("datatypes") << "Unification: " << eq[0] << " and " << eq[1] << "." << std::endl;
    for( int i=0; i<(int)eq[0].getNumChildren(); i++ ) {
      if( find( eq[0][i] )!=find( eq[1][i] ) ){
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, eq[0][i], eq[1][i] );
        Debug("datatypes") << "UEqual: " << newEq << "." << std::endl;
        d_drv_map[ newEq ] = eq;
        addEquality( newEq );
      }
    }
  }
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

Node TheoryDatatypes::constructConflict(TNode diseq, bool incDisequality ) {
  Debug("datatypes") << "datatypes: begin constructConflict()" << endl;
  Debug("datatypes") << "datatypes:   using diseq == " << diseq << endl;

  // returns the reason the two terms are equal
  Node explanation = d_cc.explain(diseq[0], diseq[1]);
  // should either be a conjunction or one equality
  Assert(explanation.getKind() == kind::EQUAL ||
         explanation.getKind() == kind::IFF ||
         explanation.getKind() == kind::AND);

  //map derived equalities back to their original
  NodeBuilder<> nb(kind::AND);
  if( explanation.getKind()==kind::AND ){
    for( int i=0; i<(int)explanation.getNumChildren(); i++ ){
      while( !d_drv_map[ explanation[i] ].get().isNull() ){
        explanation[i] = d_drv_map[ explanation[i] ].get();
      }
      nb << explanation[i];
    }
  }else{
    while( !d_drv_map[ explanation ].get().isNull() ){
      explanation = d_drv_map[ explanation ].get();
    }
    nb << explanation;
  }
  if( incDisequality ){
    nb << diseq.notNode();
  }
  if( explanation.getKind()==kind::AND || incDisequality ){
    explanation = nb;
  }

  Debug("datatypes") << "conflict constructed : " << explanation << endl;
  return explanation;
}
