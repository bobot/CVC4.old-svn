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
  d_axioms(c),
  d_selectors(c),
  d_inst_map(c),
  d_labels(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict(),
  d_noMerge(false)
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
      bool result = checkTrivialTester( in );
      Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial tester " << in << " " << result << endl;
      return RewriteComplete(NodeManager::currentNM()->mkConst(result));
    }else if( d_cons[in[0].getType()].size()==1 ){
      return RewriteComplete(NodeManager::currentNM()->mkConst(true));  //only one constructor, so it must be
    }
  }
  if( in.getKind()==APPLY_SELECTOR &&
      in[0].getKind()==APPLY_CONSTRUCTOR ){
    Debug("datatypes-rewrite") << "TheoryDatatypes::postRewrite: Rewrite trivial selector " << in << endl;
    return RewriteComplete( collapseSelector( in, Node::null() ) );
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
    if( d_drv_map[assertion].get().isNull() ){
      d_drv_map[assertion] = Node::null();
    }else{
      collectSelectors( assertion );
      switch(assertion.getKind()) {
      case kind::EQUAL:
      case kind::IFF:
        addEquality(assertion);
        break;
      case kind::APPLY_TESTER:
        checkTester( assertion );
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
              a = collapseSelector( a, Node::null(), true );
              b = collapseSelector( b, Node::null(), true );
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
            checkTester( assertion );
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
      //  for( context::CDList< Node >::const_iterator i = d_selectors.begin(); i!= d_selectors.end(); i++ ){
      //    Node sf = find( *i );
      //    //examine labels for sf
      //    
      //  }
      //}
    }
  }
  Debug("datatypes") << "TheoryDatatypes::check(): done" << endl;
}

void TheoryDatatypes::checkTester( Node assertion ){
  Debug("datatypes") << "Check tester " << assertion << std::endl;

  Node tassertion = ( assertion.getKind()==NOT ) ? assertion[0] : assertion;

  //add the term into congruence closure consideration
  d_cc.addTerm( tassertion[0] );

  Node assertionRep = assertion;
  Node tassertionRep = tassertion;
  Node tRep = tassertion[0];
  tRep = collapseSelector( tRep, Node::null(), true );
  tRep = find( tRep );
  Debug("datatypes") << "tRep is " << tRep << " " << tassertion[0] << std::endl;
  //add label instead for the representative (if it is different)
  if( tRep!=tassertion[0] ){
    tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
    assertionRep = ( assertion.getKind()==NOT ) ? tassertionRep.notNode() : tassertionRep;
    //add explanation
    Node explanation = d_cc.explain( tRep, tassertion[0] );
    NodeBuilder<> nb(kind::AND);
    nb << explanation << assertion;
    explanation = nb;
    Debug("datatypes") << "Check derived tester " << assertionRep << std::endl;
    Debug("datatypes") << "  Justification is " << explanation << std::endl;
    d_drv_map[assertionRep] = explanation;
  }

  //if tRep is a constructor, it is trivial
  if( tRep.getKind()==APPLY_CONSTRUCTOR ){
    if( checkTrivialTester( tassertionRep )==(assertionRep.getKind()==NOT) ){
      d_conflict = assertionRep;
      Debug("datatypes") << "Trivial conflict " << assertionRep << std::endl;
    }
    return;
  }

  EqLists::iterator lbl_i = d_labels.find(tRep);
  EqList* lbl;
  if(lbl_i == d_labels.end()) {
    //add to labels
    lbl = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    lbl->push_back( assertionRep );
    d_labels.insertDataFromContextMemory(tRep, lbl);
  }else{
    lbl = (*lbl_i).second;
    Debug("datatypes") << "label = " << lbl << std::endl;

    //check if empty label (no possible constructors for term)
    bool add = true;
    int notCount = 0;
    for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
      TNode leqn = (*i);
      if( leqn.getKind()==kind::NOT ){
        if( leqn[0].getOperator()==tassertionRep.getOperator() ){
          if( assertionRep.getKind()==NOT ){
            add = false;
          }else{
            NodeBuilder<> nb(kind::AND);
            nb << leqn << assertionRep;
            d_conflict = nb;
            Debug("datatypes") << "Contradictory labels " << d_conflict << std::endl;
            return;
          }
          break;
        }
        notCount++;
      }else{
        if( (leqn.getOperator()==tassertionRep.getOperator()) == (assertionRep.getKind()==NOT) ){
          NodeBuilder<> nb(kind::AND);
          nb << leqn << assertionRep;
          d_conflict = nb;
          Debug("datatypes") << "Contradictory labels(2) " << d_conflict << std::endl;
          return;
        }
        add = false;
        break;
      }
    }
    if( add ){
      if( assertionRep.getKind()==NOT && notCount==(int)d_cons[ tRep.getType() ].size()-1 ){
        NodeBuilder<> nb(kind::AND);
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          nb << (*i);
        }
        nb << assertionRep;
        d_conflict = nb;
        Debug("datatypes") << "Exhausted possibilities for labels " << d_conflict << std::endl;
        return;
      }
      lbl->push_back( assertionRep );
      Debug("datatypes") << "Add to labels " << lbl->size() << std::endl;
    }
  }
  checkInstantiate( tRep );
  return;
}

bool TheoryDatatypes::checkTrivialTester( Node assertion )
{
  Assert( assertion.getKind()==APPLY_TESTER && assertion[0].getKind()==APPLY_CONSTRUCTOR );
  TypeNode typ = assertion[0].getType();
  int testIndex = getTesterIndex( typ, assertion.getOperator() );
  int consIndex = getConstructorIndex( typ, assertion[0].getOperator() );
  Assert( testIndex!=-1 && consIndex!=-1 );
  return testIndex==consIndex;
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
      bool foundSel = false;
      for( int i=0; i<(int)d_sels[cons].size(); i++ ){
        Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, d_sels[cons][i], t );
        Debug("datatypes") << "Selector[" << i << "] = " << s << std::endl;
        Node sf = d_unionFind.find( s );
        Debug("datatypes") << "Selector value[" << i << "] = " << sf << " " << sf.getKind() << std::endl;
        if( sf!=s && sf.getKind()!=SKOLEM ){
          justifyEq << d_cc.explain( sf, s );
          foundSel = true;
        }
        selectorVals.push_back( sf );
      }
      if( !consFinite && !foundSel ){
        Debug("datatypes") << "infinite constructor, no selectors " << cons << std::endl;
        return;
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
  if( d_noMerge ){
    d_merge_pending[d_merge_pending.size()-1].push_back( std::pair< Node, Node >( a, b ) );
    return;
  }
  Assert(d_conflict.isNull());
  Debug("datatypes") << "Merge "<< a << " " << b << std::endl;

  //purify selectors
  Node atmp = a;
  Node ac = collapseSelector( a, b, true );
  Node bc = collapseSelector( b, atmp, true );

  Debug("datatypes") << "After collapse: "<< ac << " " << bc << std::endl;

  // make "a" the one with shorter diseqList
  EqLists::iterator deq_ia = d_disequalities.find(a);
  EqLists::iterator deq_ib = d_disequalities.find(b);

  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      Node tmp = ac;
      ac = bc;
      bc = tmp;
    }
  }


  a = find(ac);
  b = find(bc);

  Debug("datatypes") << "After find: "<< a << " " << b << std::endl;

  if( a == b) {
    return;
  }
  //if b is a selector, swap a and b
  if( b.getKind()==APPLY_SELECTOR && a.getKind()!=APPLY_SELECTOR ){
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make constructors the representatives
  if( a.getKind()==APPLY_CONSTRUCTOR ){
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make sure skolem variable is not representative
  if( b.getKind()==SKOLEM ){
    TNode tmp = a;
    a = b;
    b = tmp;
  }

 Debug("datatypes") << "After swap: "<< a << " " << b << std::endl;

  // b becomes the canon of a
  d_unionFind.setCanon(a, b);

  if( d_unionFind.isInconsistentConstructor( a, b ) ){
    Debug("datatypes") << "Clash " << a << " " << b << std::endl;
    d_conflict = d_cc.explain( a, b );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  //these tests should be unnecessary
  Node clash = d_unionFind.checkInconsistent( a );
  if( !clash.isNull() ){
    Debug("datatypes") << "ClashA " << a << " " << clash << std::endl;
    d_conflict = d_cc.explain( a, clash );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  clash = d_unionFind.checkInconsistent( b );
  if( !clash.isNull() ){
    Debug("datatypes") << "ClashB " << b << " " << clash << std::endl;
    d_conflict = d_cc.explain( b, clash );
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  //merge labels
  EqLists::iterator lbl_i = d_labels.find( a );
  if(lbl_i != d_labels.end()) {
    EqList* lbl = (*lbl_i).second;
    if( !lbl->empty() ){
      for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
        checkTester( *i );
        if( !d_conflict.isNull() ){
          return;
        }
      }
    }
  }


 Debug("datatypes") << "After check 1" << std::endl;

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
        Debug("datatypes") << "Construct standard conflict " << deqn << " " << sp << std::endl;
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
 Debug("datatypes") << "Merge Done" << std::endl;
}

Node TheoryDatatypes::collapseSelector( TNode t, TNode tc, bool useContext ){
  if( t.getKind()==APPLY_SELECTOR ){
    Debug("datatypes") << "Collapse selector? " << t << endl;
    Node nt = t;
    if( useContext ){
      TNode targ = find( t[0] );
      if( targ!=t[0] ){
        nt = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, t.getOperator(), targ );
      }
    }
    Debug("datatypes") << "Done first" << endl;
    //collapse constructor
    if( nt[0].getKind()==APPLY_CONSTRUCTOR ){
      int selIndex = -1;
      Node sel = nt.getOperator();
      TypeNode selType = sel.getType();
      Node cons = nt[0].getOperator();
      for(int i=0; i<(int)d_sels[cons].size(); i++ ) {
        if( d_sels[cons][i]==sel ){
          selIndex = i;
          break;
        }
      }
      Node retNode;
      if( selIndex==-1 ){
        Debug("datatypes") << "Applied selector to wrong constructor " << sel << endl;
        Debug("datatypes") << "Return distinguished term ";
        Debug("datatypes") << d_distinguishTerms[ selType[1] ] << " of type " << selType[1] << endl;
        retNode = d_distinguishTerms[ selType[1] ];
      }else{
        Debug("datatypes") << "Applied selector to correct constructor, index = " << selIndex << endl;
        Debug("datatypes") << "Return " << nt[0][selIndex] << endl;
        retNode = nt[0][selIndex];
      }
      if( useContext && find( retNode )!=find( tc ) ){
        Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, nt );
        addEquality( neq, false );
        d_axioms[neq] = true;
      }
      Debug("datatypes") << "Done second" << endl;
      return retNode;
    }
    return nt;
  }
  return t;
}

void TheoryDatatypes::collectSelectors( TNode t ){
  if( t.getKind()==APPLY_SELECTOR ){
    d_selectors.push_back( t );
  }
  for( int i=0; i<(int)t.getNumChildren(); i++ ) {
    collectSelectors( t[i] );
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

void TheoryDatatypes::addEquality(TNode eq, bool collapseSel){
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Debug("datatypes") << "Add equality " << eq << "." << std::endl;
  Node teq = eq;
  if( collapseSel ){
    //Node a = collapseSelector( a, b, true );
    //Node b = collapseSelector( a, b, true );
    //teq = NodeManager::currentNM()->mkNode( EQUAL, a, b );
  }
  d_merge_pending.push_back( std::vector< std::pair< Node, Node > >() );
  d_noMerge = true;
  d_cc.addEquality(eq);
  d_noMerge = false;
  unsigned int mpi = d_merge_pending.size()-1;
  for( int i=0; i<(int)d_merge_pending[mpi].size(); i++ ){
    if( d_conflict.isNull() ){
      merge( d_merge_pending[mpi][i].first, d_merge_pending[mpi][i].second );
    }
  }
  d_merge_pending.pop_back();
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
  }else if( d_axioms.find( n )==d_axioms.end() ){
    nb << n;
  }
}
