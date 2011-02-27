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

int TheoryDatatypes::getDatatypeIndex( TypeNode t )
{
  for( int a=0; a<(int)d_defs.size(); a++ ){
    if( *(d_defs[a].first.d_typeNode)==t ){
      return a;
    }
  }
  return -1;
}

int TheoryDatatypes::getConstructorIndex( int typeIndex, TypeNode t )
{
  for( int a=0; a<(int)d_defs[typeIndex].second.size(); a++ ){
    if( *(d_defs[typeIndex].second[a].d_typeNode)==t ){
      return a;
    }
  }
  return -1;
}

bool TheoryDatatypes::isFiniteDatatype( TypeNode t ){
  for( int a=0; a<(int)d_defs.size(); a++ ){
    if( *(d_defs[a].first.d_typeNode)==t ){
      return is_finite[a].first;
    }
  }
  return false;
}

bool TheoryDatatypes::isWellFoundedDatatype( TypeNode t ){
  for( int a=0; a<(int)d_defs.size(); a++ ){
    if( *(d_defs[a].first.d_typeNode)==t ){
      return is_wellFounded[a].first;
    }
  }
  return false;
}

void TheoryDatatypes::checkFiniteWellFounded(){
  if( requiresCheckFiniteWellFounded ){
    //check well-founded and finite, create distinguished ground terms
    d_distinguishTerms.clear();
    d_distinguishTerms.resize( (int)d_defs.size() );
    is_wellFounded.clear();
    is_finite.clear();
    is_wellFounded.resize( (int)d_defs.size() );
    is_finite.resize( (int)d_defs.size() );
    for( int a=0; a<(int)d_defs.size(); a++ ){
      is_wellFounded[a].first = false;
      is_finite[a].first = false;
      is_wellFounded[a].second.resize( (int)d_defs[a].second.size(), false );
      is_finite[a].second.resize( (int)d_defs[a].second.size(), false );
    }
    bool changed;
    do{
      changed = false;
      for( int a=0; a<(int)d_defs.size(); a++ ){
        Type t = d_defs[a].first;
        //Debug("datatypes") << "check " << t << std::endl;
        bool typeFinite = true;
        for( int b=0; b<(int)d_defs[a].second.size(); b++ ){
          ConstructorType ct = (ConstructorType)d_defs[a].second[b];
          //Debug("datatypes") << " check cons " << ct << std::endl;
          if( !is_finite[a].second[b] ){
            int c;
            for( c=0; c<(int)ct.d_typeNode->getNumChildren()-1; c++ ){
              //Debug("datatypes") << "  check sel " << ct.d_typeNode[0][c] << std::endl;
              TypeNode ts = ct.d_typeNode[0][c][1];
              //Debug("datatypes") << "  check : " << ts << std::endl;
              if( !isDatatype( ts ) || !isFiniteDatatype( ts ) ){
                break;
              }
            }
            if( c ==(int)ct.d_typeNode->getNumChildren()-1 ){
              changed = true;
              is_finite[a].second[b] = true;
              Debug("datatypes") << ct << " now finite" << std::endl;
            }else{
              typeFinite = false;
            }
          }
          if( !is_wellFounded[a].second[b] ){
            int c;
            for( c=0; c<(int)ct.d_typeNode->getNumChildren()-1; c++ ){
              //Debug("datatypes") << "  check sel " << ct.d_typeNode[0][c] << std::endl;
              TypeNode ts = ct.d_typeNode[0][c][1];
              //Debug("datatypes") << "  check : " << ts << std::endl;
              if( isDatatype( ts ) && !isWellFoundedDatatype( ts ) ){
                break;
              }
            }
            if( c ==(int)ct.d_typeNode->getNumChildren()-1 ){
              changed = true;
              is_wellFounded[a].second[b] = true;
              Debug("datatypes") << ct << " now well founded" << std::endl;
            }
          }
          if( is_wellFounded[a].second[b] ){
            if( !is_wellFounded[a].first ){
              changed = true;
              is_wellFounded[a].first = true;
              //also set distinguished ground term
              //Debug("datatypes") << "set distinguished ground term out of " << ct << std::endl;
              Debug("datatypes") << a << " now type wf" << std::endl;
              NodeManager* nm = NodeManager::currentNM();
              std::vector< NodeTemplate<true> > children;
              children.push_back( nm->mkVar( *d_defs[a].second[b].d_typeNode ) );
              for( int c=0; c<(int)ct.d_typeNode->getNumChildren()-1; c++ ){
                TypeNode ts = ct.d_typeNode[0][c][1];
                int dindex = getDatatypeIndex( ts );
                if( dindex!=-1 ){
                  children.push_back( d_distinguishTerms[dindex] );
                }else{
                  nm->mkVar( ts );
                }
              }
              Node dgt = nm->mkNode( APPLY_CONSTRUCTOR, children );
              Debug("datatypes") << "set distinguished ground term " << a << " to " << dgt << std::endl;
              d_distinguishTerms[a] = dgt;
            }
          }
        }
        if( typeFinite && !is_finite[a].first ){
          changed = true;
          is_finite[a].first = true;
          Debug("datatypes") << a << " now type finite" << std::endl;
        }
      }
    }while( changed );
    for( int a=0; a<(int)d_defs.size(); a++ ){
      if( !is_finite[a].first ){
        Debug("datatypes") << d_defs[a].first << " is not finite." << std::endl;
      }
      if( !is_wellFounded[a].first ){
        Debug("datatypes") << d_defs[a].first << " is not well-founded." << std::endl;
        //throw exception?
      }
      for( int b=0; b<(int)d_defs[a].second.size(); b++ ){
        if( !is_finite[a].second[b] ){
          Debug("datatypes") << d_defs[a].second[b] << " is not finite." << std::endl;
        }
        if( !is_wellFounded[a].second[b] ){
          Debug("datatypes") << d_defs[a].second[b] << " is not well-founded." << std::endl;
        }
      }
    }
    requiresCheckFiniteWellFounded = false;
  }
}

TheoryDatatypes::TheoryDatatypes(int id, Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict()
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
    TypeNode testConsType = (in.getOperator().getType())[0];
    TypeNode consType = in[0].getOperator().getType();
    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial tester " << in << endl;
    Debug("datatypes-rewrite") << in.getOperator().getType() << " " << in.getOperator() << endl;
    Debug("datatypes-rewrite") << in[0].getOperator().getType() << " " << in[0].getOperator() << endl;
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
      Debug("datatypes-rewrite") << "Applied selector to wrong constructor " << selType[1] << endl;
      int index = getDatatypeIndex( selType[1] );
      if( index==-1 ){
        Debug("datatypes-rewrite") << "Bad index for type " << selType[1] << endl;
      }else{
        Debug("datatypes-rewrite") << "Return distinguished term " << d_distinguishTerms[index] << " of type " << selType[1] << endl;
        return RewriteComplete( d_distinguishTerms[index] );
      }
    }else{
      Debug("datatypes-rewrite") << "Applied selector to correct constructor, index = " << selIndex << endl;
      Debug("datatypes-rewrite") << "Return " << in[0][selIndex] << endl;
      return RewriteComplete( in[0][selIndex] );
    }
  }

  return RewriteComplete(in);
}

void TheoryDatatypes::addConstructorDefinitions( std::vector<std::pair<Type, std::vector<Type> > >& defs ){
  d_defs.insert( d_defs.begin(), defs.begin(), defs.end() );
  requiresCheckFiniteWellFounded = true;
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                  << t << endl;
}


void TheoryDatatypes::notifyEq(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyEq(): "
                  << lhs << " = " << rhs << endl;
  //do unification?

}

void TheoryDatatypes::notifyCongruent(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyCongruent(): "
                  << lhs << " = " << rhs << endl;
  //do unification?
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
      //Debug("datatypes") << "Equality" << endl;
      d_cc.addEquality(assertion);
      //Debug("datatypes") << "Done Equality" << endl;
      //if(!d_conflict.isNull()) {
      //  Node conflict = constructConflict(d_conflict);
      //  d_conflict = Node::null();
      //  //++d_conflicts;
      //  d_out->conflict(conflict, false);
      //  return;
      //}
      //merge(assertion[0], assertion[1]);
      break;
    case kind::APPLY_TESTER:
      checkTester( e, assertion, assertion );
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()){
        case kind::EQUAL:
        case kind::IFF:
          {
            //Node a = assertion[0][0];
            //Node b = assertion[0][1];
            //addDisequality(assertion[0]);
            //d_cc.addTerm(a);
            //d_cc.addTerm(b);
            //if(Debug.isOn("datatypes")) {
            //  Debug("datatypes") << "       a  ==> " << a << endl
            //              << "       b  ==> " << b << endl
            //              << "  find(a) ==> " << debugFind(a) << endl
            //              << "  find(b) ==> " << debugFind(b) << endl;
            //}
            //// There are two ways to get a conflict here.
            //if(!d_conflict.isNull()) {
            //  // We get a conflict this way if we weren't watching a, b
            //  // before and we were just now notified (via
            //  // notifyCongruent()) when we called addTerm() above that
            //  // they are congruent.  We make this a separate case (even
            //  // though the check in the "else if.." below would also
            //  // catch it, so that we can clear out d_conflict.
            //  Node conflict = constructConflict(d_conflict);
            //  d_conflict = Node::null();
            //  //++d_conflicts;
            //  d_out->conflict(conflict, false);
            //  return;
            //} else if(find(a) == find(b)) {
            //  // We get a conflict this way if we WERE previously watching
            //  // a, b and were notified previously (via notifyCongruent())
            //  // that they were congruent.
            //  Node conflict = constructConflict(assertion[0]);
            //  //++d_conflicts;
            //  d_out->conflict(conflict, false);
            //  return;
            //}

            //// If we get this far, there should be nothing conflicting due
            //// to this disequality.
            //Assert(!d_cc.areCongruent(a, b));
          }
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
  Debug("datatypes") << "check tester " << assertion << std::endl;

  //tassertion[0] should be a variable
  Assert( tassertion[0].getKind()!=kind::APPLY_CONSTRUCTOR );

  int datatypeIndex = getDatatypeIndex( tassertion[0].getType() );
  Assert( datatypeIndex!= -1 );
  //check if empty label (no possible constructors remain)
  if( assertion.getKind()==NOT ){
    int notCount = 0;
    bool add = true;
    for( int a=d_labels[ tassertion[0] ].size()-1; a>=0; a-- ){
      if( d_labels[ tassertion[0] ][a].getKind()==kind::NOT ){
        if( d_labels[ tassertion[0] ][a][0].getOperator()==tassertion.getOperator() ){
          add = false;
          break;
        }
        notCount++;
      }else{
        add = false;
        if( d_labels[ tassertion[0] ][a].getOperator()==tassertion.getOperator() ){
          NodeBuilder<> nb(kind::AND);
          nb << d_labels[ tassertion[0] ][a] << assertion;
          Node conflict = nb;
          d_out->conflict( conflict, false );
          Debug("datatypes") << "Contradictory labels1 " << conflict << std::endl;
        }
        break;
      }
    }
    if( add ){
      if( notCount==(int)d_defs[datatypeIndex].second.size()-1 ){
        NodeBuilder<> nb(kind::AND);
        for( int a=d_labels[ tassertion[0] ].size()-1; a>=0; a-- ){
          nb << d_labels[ tassertion[0] ][a];
        }
        nb << assertion;
        Node conflict = nb;
        d_out->conflict( conflict, false ); 
        Debug("datatypes") << "Exhausted possibilities for labels " << conflict << std::endl;
      }else{
        d_labels[ tassertion[0] ].push_back( assertion );
        Debug("datatypes") << "Add to labels " << d_labels[ tassertion[0] ].size() << std::endl;
      }
    }
  }else{
    bool add = true;
    for( int a=d_labels[ tassertion[0] ].size()-1; a>=0; a-- ){
      if( d_labels[ tassertion[0] ][a].getKind()==kind::NOT ){
        if( d_labels[ tassertion[0] ][a][0].getOperator()==tassertion.getOperator() ){
          NodeBuilder<> nb(kind::AND);
          nb << d_labels[ tassertion[0] ][a] << assertion;
          Node conflict = nb;
          d_out->conflict( conflict, false ); 
          Debug("datatypes") << "Contradictory labels2 " << conflict << std::endl;
        }
      }else{
        if( d_labels[ tassertion[0] ][a].getOperator()!=tassertion.getOperator() ){
          NodeBuilder<> nb(kind::AND);
          nb << d_labels[ tassertion[0] ][a] << assertion;
          Node conflict = nb;
          d_out->conflict( conflict, false ); 
          Debug("datatypes") << "Contradictory labels3 " << conflict << std::endl;
        }
        add = false;
        break;
      }
    }
    if( add ){
      d_labels[ tassertion[0] ].push_back( assertion );
      Debug("datatypes") << "Add to labels " << d_labels[ tassertion[0] ].size() << std::endl;
    }
  }
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

Node TheoryDatatypes::constructConflict(TNode diseq) {
  Debug("datatypes") << "datatypes: begin constructConflict()" << endl;
  Debug("datatypes") << "datatypes:   using diseq == " << diseq << endl;

  // returns the reason the two terms are equal
  Node explanation = d_cc.explain(diseq[0], diseq[1]);
  // should either be a conjunction or one equality
  Assert(explanation.getKind() == kind::EQUAL ||
         explanation.getKind() == kind::IFF ||
         explanation.getKind() == kind::AND);

  Debug("datatypes") << "conflict constructed : " << explanation << endl;
  return explanation;
}
