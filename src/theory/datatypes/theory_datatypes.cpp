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
  d_inst_map(c),
  d_labels(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_cons_rep_map(c),
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

  if( in.getKind()==APPLY_TESTER ){
    if( in[0].getKind()==APPLY_CONSTRUCTOR ){
      TypeNode testType = in.getOperator().getType();
      TypeNode consType = in[0].getOperator().getType();
      int testIndex = getTesterIndex( testType[0], in.getOperator() );
      int consIndex = getConstructorIndex( testType[0], in[0].getOperator() );
      Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial tester " << in << endl;
      Debug("datatypes-rewrite") << testType << " " << in.getOperator() << " " << testIndex << endl;
      Debug("datatypes-rewrite") << consType << " " << in[0].getOperator() << " " << consIndex << endl;
      return RewriteComplete(NodeManager::currentNM()->mkConst(testIndex==consIndex));
    }else if( d_cons[in[0].getType()].size()==1 ){
      return RewriteComplete(NodeManager::currentNM()->mkConst(true));  //only one constructor, so it must be
    }
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
  if( in.getKind()==kind::EQUAL && d_unionFind.isInconsistentConstructor( in[0], in[1], true ) ){
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
  //if(!d_conflict.isNull()) {
  //  return;
  //}
  //merge(lhs,rhs);
  //FIXME
  //Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
  //addEquality(eq);
  //d_drv_map[eq] = d_cc.explain( lhs, rhs );
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

    //clear from the derived map
    d_drv_map[assertion] = Node::null();

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      addEquality(assertion);
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
            if(d_conflict.isNull()) {
              if(find(a) == find(b)) {
                // We get a conflict this way if we WERE previously watching
                // a, b and were notified previously (via notifyCongruent())
                // that they were congruent.
                NodeBuilder<> nb(kind::AND);
                nb << d_cc.explain( assertion[0][0], assertion[0][1] );
                nb << assertion;
                d_conflict = nb;
                Debug("datatypes") << "Disequality conflict " << d_conflict << std::endl;
              }else{

                // If we get this far, there should be nothing conflicting due
                // to this disequality.
                Assert(!d_cc.areCongruent(a, b));
              }
            }
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
    if(!d_conflict.isNull()) {
      throwConflict();
      return;
    }
    //if( e==FULL_EFFORT ){
    //  //do splitting
    //  std::vector< Node > nodes;
    //  Node tassertion;
    //  switch( assertion.getKind() ){
    //  case kind::APPLY_TESTER:
    //    tassertion = assertion[0];
    //    break;
    //  case kind::NOT:
    //    tassertion = assertion[0];
    //    if( tassertion.getKind()==kind::APPLY_TESTER )
    //      tassertion = tassertion[0];
    //    break;
    //  }
    //  //tassertion has all terms for children
    //  for( int i=0; i<(int)tassertion.getNumChildren(); i++ ){
    //    Node n = tassertion[i];
    //    if( n.getKind()==kind::APPLY_SELECTOR ){
    //      //d_out->lemma(
    //    }else if( n.getKind()!=kind::APPLY_CONSTRUCTOR ){
    //      
    //    }
    //  }
    //}
  }
  Debug("datatypes") << "TheoryDatatypes::check(): done" << endl;
}

void TheoryDatatypes::checkTester( Effort e, Node tassertion, Node assertion ){
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
          Debug("datatypes") << "Contradictory labels(2) " << conflict << std::endl;
        }
        add = false;
        break;
      }
    }
    if( !conflict.isNull() ){
      d_conflict = conflict;
      return;
    }
    if( add ){
      if( assertion.getKind()==NOT && notCount==(int)d_cons[ tassertion[0].getType() ].size()-1 ){
        NodeBuilder<> nb(kind::AND);
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          nb << (*i);
        }
        nb << assertion;
        d_conflict = nb;
        Debug("datatypes") << "Exhausted possibilities for labels " << d_conflict << std::endl;
        return;
      }
      lbl->push_back( assertion );
      Debug("datatypes") << "Add to labels " << lbl->size() << std::endl;
    }
  }
  //check to see if this is a conflict according to equivalence class
  Node tr = d_unionFind.find( tassertion[0] );
  //Debug("datatypes") << "Equiv class = " << tr << std::endl;
  if( tr.getKind()==APPLY_CONSTRUCTOR ){
    TypeNode typ = tassertion[0].getType();
    int cIndex = getConstructorIndex( typ, tr.getOperator() );
    int tIndex = getTesterIndex( typ, tassertion.getOperator() );
    Assert( cIndex!=-1 && tIndex!=-1 );
    //Debug("datatypes") << tr.getOperator() << " " << tassertion.getOperator() << std::endl;
    //Debug("datatypes") << "indicies = " << cIndex << " " << tIndex << std::endl;
    if( (cIndex==tIndex) == (assertion.getKind()==NOT) ){
      Node explanation = d_cc.explain(tassertion[0], tr);
      NodeBuilder<> nb(kind::AND);
      nb << assertion;
      nb << explanation;
      d_conflict = nb;
      Debug("datatypes") << "Cannot add label due to equiv class " << assertion << " " << tr << std::endl;
      Debug("datatypes") << "Conflict = " << d_conflict << std::endl;
      return;
    }
  }
  checkInstantiate( tassertion[0] );
  return;
}

void TheoryDatatypes::checkInstantiate( Node t ){
  Debug("datatypes") << "Apply instantiation? " << t << std::endl;

  EqLists::iterator lbl_i = d_labels.find( t );
  EqList* lbl;
  if(lbl_i == d_labels.end()) {
    lbl = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_labels.insertDataFromContextMemory( t, lbl );
  }else{
    lbl = (*lbl_i).second;
  }
 
  //there is one remaining constructor, and t has not been instantiated
  if( d_inst_map.find( t )==d_inst_map.end() ){
    TypeNode typ = t.getType();
    Node cons = Node::null();
    //if ended by one positive tester
    if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind()!=NOT ){
      Assert( getTesterIndex( typ, (*lbl)[ lbl->size()-1 ].getOperator() )!=-1 );
      cons = d_cons[typ][ getTesterIndex( typ, (*lbl)[ lbl->size()-1 ].getOperator() ) ];
    //if (n-1) negative testers
    }else if( (*lbl)[ lbl->size()-1 ].getKind()==NOT && (int)lbl->size()==(int)d_cons[ t.getType() ].size()-1 ){
      std::vector< bool > possibleCons;
      possibleCons.resize( (int)d_cons[ t.getType() ].size(), true );
      for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
        TNode leqn = (*i);
        Assert( getTesterIndex( typ, leqn[0].getOperator() )!=-1 );
        possibleCons[ getTesterIndex( typ, leqn[0].getOperator() ) ] = false;
      }
      for( int i=0; i<(int)possibleCons.size(); i++ ){
        if( possibleCons[i] ){
          Assert( cons.isNull() );
          cons = d_cons[typ][ i ];
        }
      }
      Assert( !cons.isNull() );
    }

    if( !cons.isNull() ){
      //only one constructor possible for term (label is singleton), apply instantiation rule
      bool consFinite = d_cons_finite[cons];
      //find if selectors have been applied to t
      std::vector< Node > selectorVals;
      selectorVals.push_back( cons );
      NodeBuilder<> justifyEq(kind::AND);
      for( int i=0; i<(int)d_sels[cons].size(); i++ ){
        Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, d_sels[cons][i], t );
        Debug("datatypes") << "Selector[" << i << "] = " << s << std::endl;
        Node sf = d_unionFind.find( s );
        if( ( sf==s || sf.getKind()==SKOLEM ) && !consFinite ){
          Debug("datatypes") << "infinite constructor, no selector " << s << std::endl;
          return;
        }else{
          Debug("datatypes") << "Selector value[" << i << "] = " << sf << " " << sf.getKind() << std::endl;
          if( sf!=s && sf.getKind()!=SKOLEM ){
            justifyEq << d_cc.explain( sf, s );
          }
          selectorVals.push_back( sf );
        }
      }
      d_inst_map[ t ] = true;
      //instantiate, add equality
      Node val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
      if( find( val )!=find( t ) ){
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, val, t );
        Debug("datatypes") << "Instantiate Equal: " << newEq << "." << std::endl;
        Assert( !lbl->empty() );
        if( lbl->size()==1 || (*lbl)[ lbl->size()-1 ].getKind()!=NOT ){
          justifyEq << (*lbl)[ lbl->size()-1 ];
        }else{
          for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
            justifyEq << (*i);
          }
        }
        Node jeq;
        if( justifyEq.getNumChildren()==1 ){
          jeq = justifyEq.getChild( 0 );
        }else{
          jeq = justifyEq;
        }
        Debug("datatypes") << "Justification is: " << jeq << "." << std::endl;
        d_drv_map[ newEq ] = jeq;
        addEquality( newEq );
      }
    }
  }
}

Node TheoryDatatypes::checkCanBeConstructor( Node t, Node cons ){
  EqLists::iterator lbl_i = d_labels.find( t );
  if(lbl_i != d_labels.end()) {
    EqList* lbl = (*lbl_i).second;
    if( !lbl->empty() ){
      TypeNode tn = t.getType();
      int cIndex = getConstructorIndex( tn, cons );
      Assert( cIndex!=-1 );
      if( (*lbl)[ lbl->size()-1 ].getKind()!=NOT ){
        int tIndex = getTesterIndex( tn, (*lbl)[ lbl->size()-1 ].getOperator() );
        Assert( tIndex!=-1 );
        if( tIndex!=cIndex ){
          return (*lbl)[ lbl->size()-1 ];
        }
      }else{
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          int tIndex = getTesterIndex( tn, (*i)[0].getOperator() );
          Assert( tIndex!=-1 );
          if( tIndex==cIndex ){
            return (*i);
          }
        }
      }
    }
  }
  return Node::null();
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
  Debug("datatypes") << "Merge "<< a << " " << b << std::endl;

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
  //if b is a selector, swap a and b
  if( b.getKind()==APPLY_SELECTOR && a.getKind()!=APPLY_SELECTOR ){
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  Node ac = d_cons_rep_map.find( a );
  Node bc = d_cons_rep_map.find( b );
  //make constructors the representatives
  if( ac.getKind()==APPLY_CONSTRUCTOR ){
    TNode tmp = ac;
    ac = bc;
    bc = tmp;
  }
  d_cons_rep_map.setCanon( ac, bc );
  if( bc.getKind()==APPLY_CONSTRUCTOR ){
    for( int i=0; i<2; i++ ){
      Node node = (i==0) ? a : b;
      //make sure it agrees with the labels
      Node consConflict = checkCanBeConstructor( node, bc.getOperator() );
      if( !consConflict.isNull() ){
        Debug("datatypes") << "Cannot be added to equivalence class due to labels " << node << " " << bc << std::endl;
        NodeBuilder<> nb(kind::AND);
        nb << d_cc.explain( node, bc );
        nb << consConflict;
        d_conflict = nb;
        Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
        return;
      }
    }
  }


  a = find(a);
  b = find(b);

  if( a == b) {
    return;
  }

  //Assert( a.getKind()!=SKOLEM && b.getKind()!=SKOLEM );

  // b becomes the canon of a
  d_unionFind.setCanon(a, b);
  // FIXME : find if any node in the equivalence class of b conflicts with a, or
  // if any node in the equivalence class of a conflicts with b
  //TODO:  the test for "a" might not be necessary
  if( d_unionFind.isInconsistentConstructor( a, b ) ){
    Debug("datatypes") << "Clash " << a << " " << b << std::endl;
    d_conflict = d_cc.explain( a, b );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  Node clash = d_unionFind.checkInconsistent( a );
  if( !clash.isNull() ){
    Assert( false );
    Debug("datatypes") << "ClashA " << a << " " << clash << std::endl;
    d_conflict = d_cc.explain( a, clash );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  clash = d_unionFind.checkInconsistent( b );
  if( !clash.isNull() ){
    Assert( false );
    Debug("datatypes") << "ClashB " << b << " " << clash << std::endl;
    d_conflict = d_cc.explain( b, clash );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }

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
        Assert(sp == b || tp == b, "test1");
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

      TNode sp = find(s);
      TNode tp = find(t);
      if(sp == tp) {
        Debug("datatypes") << "Construct standard conflict " << deqn << std::endl;
        Node explanation = d_cc.explain(deqn[0], deqn[1]);
        d_conflict = NodeManager::currentNM()->mkNode( kind::AND, explanation, deqn.notNode() );
        Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
        return;
      }
      Assert( sp == b || tp == b, "test2");

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
  if( d_conflict.isNull() ){
    merge(eq[0], eq[1]);
    //do unification
    if( d_conflict.isNull() ){
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

//Node TheoryDatatypes::constructConflict(TNode diseq, bool incDisequality ) {
//  Debug("datatypes") << "datatypes: begin constructConflict()" << endl;
//  Debug("datatypes") << "datatypes:   using diseq == " << diseq << endl;
//
//  // returns the reason the two terms are equal
//  Node explanation = d_cc.explain(diseq[0], diseq[1]);
//  // should either be a conjunction or one equality
//  Assert(explanation.getKind() == kind::EQUAL ||
//         explanation.getKind() == kind::IFF ||
//         explanation.getKind() == kind::AND);
//
//  if( incDisequality ){
//    explanation = NodeManager::currentNM()->mkNode( kind::AND, explanation, diseq.notNode() );
//  }
//
//  explanation = convertDerived( explanation );
//
//  Debug("datatypes") << "conflict constructed : " << explanation << endl;
//  return explanation;
//}

void TheoryDatatypes::throwConflict(){
  Debug("datatypes") << "Convert conflict : " << d_conflict << endl;
  NodeBuilder<> nb(kind::AND);
  convertDerived( d_conflict, nb );
  if( nb.getNumChildren()==1 ){
    d_conflict = nb.getChild( 0 );
  }else{
    d_conflict = nb;
  }
  Debug("datatypes") << "Conflict constructed : " << d_conflict << endl;
  d_out->conflict( d_conflict, false );
  d_conflict = Node::null();
}

void TheoryDatatypes::convertDerived(Node n, NodeBuilder<>& nb){
  if( n.getKind()==kind::AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      convertDerived( n[i], nb );
    }
  }else if( !d_drv_map[ n ].get().isNull() ){
    convertDerived( d_drv_map[ n ].get(), nb );
  }else{
    nb << n;
  }
}
