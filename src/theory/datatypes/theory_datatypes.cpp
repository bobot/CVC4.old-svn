/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of datatypes
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

TheoryDatatypes::TheoryDatatypes(Context* c, OutputChannel& out) :
  Theory(THEORY_DATATYPES, c, out),
  d_currAsserts(c),
  d_currEqualities(c),
  d_drv_map(c),
  d_axioms(c),
  d_selectors(c),
  d_reps(c),
  d_selector_eq(c),
  d_equivalence_class(c),
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


void TheoryDatatypes::addDatatypeDefinitions( std::vector<std::pair< TypeNode, std::vector<Node> > >& cons,
                                              std::vector<std::pair< TypeNode, std::vector<Node> > >& testers,
                                              std::vector<std::pair< Node, std::vector<Node> > >& sels ) {
  Debug("datatypes") << "TheoryDatatypes::addDataTypeDefinitions()" << std::endl;
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
      d_sel_cons[ *itc ] = it2->first;
    }
  }
  requiresCheckFiniteWellFounded = true;
  checkFiniteWellFounded();
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
  if(d_conflict.isNull()) {
    merge(lhs,rhs);
  }
  Debug("datatypes-debug") << "TheoryDatatypes::notifyCongruent(): done." << std::endl;
}


void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
  checkFiniteWellFounded();
}

void TheoryDatatypes::check(Effort e) {
  for( int i=0; i<(int)d_currAsserts.size(); i++ ){
    Debug("datatypes") << "currAsserts[" << i << "] = " << d_currAsserts[i] << std::endl;
  }
  for( int i=0; i<(int)d_currEqualities.size(); i++ ){
    Debug("datatypes") << "currEqualities[" << i << "] = " << d_currEqualities[i] << std::endl;
  }
  for( BoolMap::iterator i = d_inst_map.begin(); i!=d_inst_map.end(); i++ ){
    Debug("datatypes") << "inst_map = " << (*i).first << std::endl;
  }
  for( EqListsN::iterator i = d_selector_eq.begin(); i!= d_selector_eq.end(); i++ ){
    EqListN* m = (*i).second;
    Debug("datatypes") << "selector_eq " << (*i).first << ":" << std::endl;
    for( EqListN::const_iterator j = m->begin(); j!=m->end(); j++ ){
      Debug("datatypes") << "  : " << (*j) << std::endl;
    }
  }
  while(!done()) {
    Node assertion = get();
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ){
      cout << "*** TheoryDatatypes::check(): " << assertion << endl;
    }
    d_currAsserts.push_back( assertion );

    //clear from the derived map
    if( !d_drv_map[assertion].get().isNull() ){
      Debug("datatypes") << "Assertion has already been derived" << endl;
      d_drv_map[assertion] = Node::null();
    }else{
      collectTerms( assertion );
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
              Debug("datatypes") << "hello." << std::endl;
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
    }
  }

  if( e==FULL_EFFORT ){
    Debug("datatypes-split") << "Check for splits " << e << std::endl;
    //do splitting
    for( EqLists::iterator i = d_labels.begin(); i!= d_labels.end(); i++ ){
      Node sf = find( (*i).first );
      if( sf==(*i).first || sf.getKind()!=APPLY_CONSTRUCTOR ){
        Debug("datatypes-split") << "Check for splitting " << (*i).first << ", ";
        EqList* lbl = (sf==(*i).first) ? (*i).second : (*d_labels.find( sf )).second;
        if( lbl->empty() )
          Debug("datatypes-split") << "empty label" << std::endl;
        else
          Debug("datatypes-split") << "label size = " << lbl->size() << std::endl;
        Node cons = getPossibleCons( (*i).first, false );
        if( !cons.isNull() ){
          Debug("datatypes-split") << "*************Split for possible constructor " << cons << std::endl;
          TypeNode typ = (*i).first.getType();
          int cIndex = getConstructorIndex( typ, cons );
          Assert( cIndex!=-1 );
          Node test = NodeManager::currentNM()->mkNode( APPLY_TESTER, d_testers[typ][cIndex], (*i).first );
          NodeBuilder<> nb(kind::OR);
          nb << test << test.notNode();
          Node lemma = nb;
          Debug("datatypes-split") << "Lemma is " << lemma << std::endl;
          d_out->lemma( lemma );
          return;
        }
      }else{
        Debug("datatypes-split") << (*i).first << " is " << sf << std::endl;
      }
    }
  }
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ){
    cout << "TheoryDatatypes::check(): done" << endl;
  }
}

void TheoryDatatypes::checkTester( Node assertion, bool doAdd ){
  Debug("datatypes") << "Check tester " << assertion << std::endl;

  Node tassertion = ( assertion.getKind()==NOT ) ? assertion[0] : assertion;

  //add the term into congruence closure consideration
  d_cc.addTerm( tassertion[0] );

  Node assertionRep = assertion;
  Node tassertionRep = tassertion;
  Node tRep = tassertion[0];
  //tRep = collapseSelector( tRep, Node::null(), true );
  tRep = find( tRep );
  Debug("datatypes") << "tRep is " << tRep << " " << tassertion[0] << std::endl;
  //add label instead for the representative (if it is different)
  if( tRep!=tassertion[0] ){
    tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
    assertionRep = ( assertion.getKind()==NOT ) ? tassertionRep.notNode() : tassertionRep;
    //add explanation
    if( doAdd ){
      Node explanation = d_cc.explain( tRep, tassertion[0] );
      NodeBuilder<> nb(kind::AND);
      nb << explanation << assertion;
      explanation = nb;
      Debug("datatypes-drv") << "Check derived tester " << assertionRep << std::endl;
      Debug("datatypes-drv") << "  Justification is " << explanation << std::endl;
      d_drv_map[assertionRep] = explanation;
    }
  }

  //if tRep is a constructor, it is trivial
  if( tRep.getKind()==APPLY_CONSTRUCTOR ){
    if( checkTrivialTester( tassertionRep )==(assertionRep.getKind()==NOT) ){
      d_conflict = doAdd ? assertionRep : NodeManager::currentNM()->mkConst(true);
      Debug("datatypes") << "Trivial conflict " << assertionRep << std::endl;
    }
    return;
  }

  addTermToLabels( tRep );
  EqLists::iterator lbl_i = d_labels.find(tRep);
  //Debug("datatypes") << "Found " << (lbl_i == d_labels.end()) << std::endl;
  Assert( lbl_i != d_labels.end() );

  EqList* lbl = (*lbl_i).second;
  //Debug("datatypes") << "Check lbl = " << lbl << ", size = " << lbl->size() << std::endl;

  //check if empty label (no possible constructors for term)
  bool add = true;
  int notCount = 0;
  if( !lbl->empty() ){
    for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
      Node leqn = (*i);
      if( leqn.getKind()==kind::NOT ){
        if( leqn[0].getOperator()==tassertionRep.getOperator() ){
          if( assertionRep.getKind()==NOT ){
            add = false;
          }else{
            NodeBuilder<> nb(kind::AND);
            nb << leqn;
            if( doAdd ) nb << assertionRep;
            d_conflict = nb.getNumChildren()==1 ? nb.getChild( 0 ) : nb;
            Debug("datatypes") << "Contradictory labels " << d_conflict << std::endl;
            return;
          }
          break;
        }
        notCount++;
      }else{
        if( (leqn.getOperator()==tassertionRep.getOperator()) == (assertionRep.getKind()==NOT) ){
          NodeBuilder<> nb(kind::AND);
          nb << leqn;
          if( doAdd ) nb << assertionRep;
          d_conflict = nb.getNumChildren()==1 ? nb.getChild( 0 ) : nb;
          Debug("datatypes") << "Contradictory labels(2) " << d_conflict << std::endl;
          return;
        }
        add = false;
        break;
      }
    }
  }
  if( add ){
    if( assertionRep.getKind()==NOT && notCount==(int)d_cons[ tRep.getType() ].size()-1 ){
      NodeBuilder<> nb(kind::AND);
      if( !lbl->empty() ){
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          nb << (*i);
        }
      }
      if( doAdd ) nb << assertionRep;
      d_conflict = nb.getNumChildren()==1 ? nb.getChild( 0 ) : nb;
      Debug("datatypes") << "Exhausted possibilities for labels " << d_conflict << std::endl;
      return;
    }
    if( doAdd ){
      lbl->push_back( assertionRep );
      Debug("datatypes") << "Add to labels " << lbl->size() << std::endl;
    }
  }
  if( doAdd ){
    checkInstantiate( tRep );
    if( !d_conflict.isNull() ){
      return;
    }
    //inspect selectors
    updateSelectors( tRep );
  }
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
  Debug("datatypes") << "TheoryDatatypes::checkInstantiate() " << t << std::endl;
  Assert( t == find( t ) );

  //if labels were created for t, and t has not been instantiated
  if( t.getKind()!=APPLY_CONSTRUCTOR ){
    //for each term in equivalance class
    initializeEqClass( t );
    EqListN* eqc = (*d_equivalence_class.find( t )).second;
    for( EqListN::const_iterator iter = eqc->begin(); iter!=eqc->end(); iter++ ){
      Node te = *iter;
      Assert( find( te )==t );
      if( d_inst_map.find( te )==d_inst_map.end() ){
        Node cons = getPossibleCons( te, true );
        EqLists::iterator lbl_i = d_labels.find( t );
        //there is one remaining constructor
        if( !cons.isNull() && lbl_i != d_labels.end() ){
          EqList* lbl = (*lbl_i).second;
          //only one constructor possible for term (label is singleton), apply instantiation rule
          bool consFinite = d_cons_finite[cons];
          //find if selectors have been applied to t
          std::vector< Node > selectorVals;
          selectorVals.push_back( cons );
          NodeBuilder<> justifyEq(kind::AND);
          bool foundSel = false;
          for( int i=0; i<(int)d_sels[cons].size(); i++ ){
            Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, d_sels[cons][i], te );
            Debug("datatypes") << "Selector[" << i << "] = " << s << std::endl;
            if( d_selectors.find( s )!=d_selectors.end() ){
              Node sf = find( s );
              if( sf!=s && sf.getKind()!=SKOLEM ){
                justifyEq << d_cc.explain( sf, s );
              }
              foundSel = true;
              s = sf;
            }
            selectorVals.push_back( s );
          }
          if( consFinite || foundSel ){
            d_inst_map[ te ] = true;
            //instantiate, add equality
            Node val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
            if( find( val )!=find( te ) ){
              Node newEq = NodeManager::currentNM()->mkNode( EQUAL, val, te );
              Debug("datatypes") << "Instantiate Equal: " << newEq << "." << std::endl;
              if( lbl->size()==1 || (*lbl)[ lbl->size()-1 ].getKind()!=NOT ){
                justifyEq << (*lbl)[ lbl->size()-1 ];
              }else{
                if( !lbl->empty() ){
                  for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
                    justifyEq << (*i);
                  }
                }
              }
              Node jeq;
              if( justifyEq.getNumChildren()==1 ){
                jeq = justifyEq.getChild( 0 );
              }else{
                jeq = justifyEq;
              }
              Debug("datatypes-split") << "Instantiate " << newEq << std::endl;
              addDerivedEquality( newEq, jeq );
              return;
            }
          }else{
            Debug("datatypes") << "infinite constructor, no selectors " << cons << std::endl;
          }
        }
      }
    }
  }
}

//checkInst = true is for checkInstantiate, checkInst = false is for splitting
Node TheoryDatatypes::getPossibleCons( Node t, bool checkInst )
{
  Node tf = find( t );
  EqLists::iterator lbl_i = d_labels.find( tf );
  if( lbl_i != d_labels.end() ){
    EqList* lbl = (*lbl_i).second;
    TypeNode typ = t.getType();

    //if ended by one positive tester
    if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind()!=NOT ){
      if( checkInst ){
        Assert( getTesterIndex( typ, (*lbl)[ lbl->size()-1 ].getOperator() )!=-1 );
        return d_cons[typ][ getTesterIndex( typ, (*lbl)[ lbl->size()-1 ].getOperator() ) ];
      }
    //if (n-1) negative testers
    }else if( !checkInst || (int)lbl->size()==(int)d_cons[ t.getType() ].size()-1 ){
      std::vector< bool > possibleCons;
      possibleCons.resize( (int)d_cons[ t.getType() ].size(), true );
      if( !lbl->empty() ){
        for( EqList::const_iterator i = lbl->begin(); i!= lbl->end(); i++ ){
          TNode leqn = (*i);
          Assert( getTesterIndex( typ, leqn[0].getOperator() )!=-1 );
          possibleCons[ getTesterIndex( typ, leqn[0].getOperator() ) ] = false;
        }
      }
      Node cons = Node::null();
      for( int i=0; i<(int)possibleCons.size(); i++ ){
        if( possibleCons[i] ){
          cons = d_cons[typ][ i ];
          if( !checkInst ){
            //if there is a selector, split
            for( int i=0; i<(int)d_sels[cons].size(); i++ ){
              Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, d_sels[cons][i], tf );
              if( d_selectors.find( s )!=d_selectors.end() ){
                Debug("datatypes") << "  getPosCons: found selector " << s << std::endl;
                return cons;
              }
            }
          }
        }
      }
      if( !checkInst ){
        for( int i=0; i<(int)possibleCons.size(); i++ ){
          if( possibleCons[i] && !d_cons_finite[ d_cons[typ][ i ] ] ){
            Debug("datatypes") << "Did not find selector for " << tf;
            Debug("datatypes") << " and " << d_cons[typ][ i ] << " is not finite." << std::endl;
            return Node::null();
          }
        }
      }else{
        Assert( !cons.isNull() );
      }
      return cons;
    }
  }
  return Node::null();
}

Node TheoryDatatypes::getValue(TNode n, Valuation* valuation) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( valuation->getValue(n[0]) == valuation->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryDatatypes::merge(TNode a, TNode b) {
  if( d_noMerge ){
    Debug("datatypes") << "Append to merge pending list " << d_merge_pending.size() << std::endl;
    d_merge_pending[d_merge_pending.size()-1].push_back( std::pair< Node, Node >( a, b ) );
    return;
  }
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

  a = find(a);
  b = find(b);

  //Debug("datatypes") << "After find: "<< a << " " << b << std::endl;

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


  NodeBuilder<> explanation(kind::AND);
  if( checkClash( a, b, explanation ) ){
    explanation << d_cc.explain( a, b );
    d_conflict = explanation.getNumChildren()==1 ? explanation.getChild( 0 ) : explanation;
    Debug("datatypes") << "Clash " << a << " " << b << std::endl;
    Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
    return;
  }
  Debug("datatypes-debug") << "Done clash" << std::endl;

  Debug("datatypes") << "Set canon: "<< a << " " << b << std::endl;

  // b becomes the canon of a
  d_unionFind.setCanon(a, b);
  d_reps[a] = false;
  d_reps[b] = true;
  //merge equivalence classes
  initializeEqClass( a );
  initializeEqClass( b );
  EqListN* eqc_a = (*d_equivalence_class.find( a )).second;
  EqListN* eqc_b = (*d_equivalence_class.find( b )).second;
  for( EqListN::const_iterator i = eqc_a->begin(); i!= eqc_a->end(); i++ ){
    eqc_b->push_back( *i );
  }

 //Debug("datatypes") << "After check 1" << std::endl;

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

  //Debug("datatypes-debug") << "Done clash" << std::endl;
  checkCycles();
  if( !d_conflict.isNull() ){
    return;
  }
  Debug("datatypes-debug") << "Done cycles" << std::endl;

  //merge selector lists
  updateSelectors( a );
  Debug("datatypes-debug") << "Done collapse" << std::endl;

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
  Debug("datatypes-debug") << "Done merge labels" << std::endl;

  //do unification
  if( d_conflict.isNull() ){
    if( a.getKind()==APPLY_CONSTRUCTOR && b.getKind()==APPLY_CONSTRUCTOR &&
        a.getOperator()==b.getOperator() ){
      Debug("datatypes") << "Unification: " << a << " and " << b << "." << std::endl;
      for( int i=0; i<(int)a.getNumChildren(); i++ ) {
        if( find( a[i] )!=find( b[i] ) ){
          Node newEq = NodeManager::currentNM()->mkNode( EQUAL, a[i], b[i] );
          Node jEq = d_cc.explain(a, b);
          Debug("datatypes-drv") << "UEqual: " << newEq << ", justification: " << jEq << " from " << a << " " << b << std::endl;
          Debug("datatypes-drv") << "UEqual find: " << find( a[i] ) << " " << find( b[i] ) << std::endl;
          addDerivedEquality( newEq, jEq );
        }
      }
    }
  }

  Debug("datatypes-debug") << "merge(): Done" << std::endl;
}

Node TheoryDatatypes::collapseSelector( TNode t, bool useContext ){
  if( t.getKind()==APPLY_SELECTOR ){
    //collapse constructor
    TypeNode typ = t[0].getType();
    Node sel = t.getOperator();
    TypeNode selType = sel.getType();
    Node cons = d_sel_cons[sel];
    Node tmp = find( t[0] );
    Node retNode = t;
    if( tmp.getKind()==APPLY_CONSTRUCTOR ){
      if( tmp.getOperator()==cons ){
        int selIndex = -1;
        for(int i=0; i<(int)d_sels[cons].size(); i++ ) {
          if( d_sels[cons][i]==sel ){
            selIndex = i;
            break;
          }
        }
        Assert( selIndex!=-1 );
        Debug("datatypes") << "Applied selector " << t << " to correct constructor, index = " << selIndex << endl;
        Debug("datatypes") << "Return " << tmp[selIndex] << endl;
        retNode = tmp[selIndex];
      }else{
        Debug("datatypes") << "Applied selector " << t << " to wrong constructor " << endl;
        Debug("datatypes") << "Return distinguished term ";
        Debug("datatypes") << d_distinguishTerms[ selType[1] ] << " of type " << selType[1] << endl;
        retNode = d_distinguishTerms[ selType[1] ];
      }
      if( useContext ){
        Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
        d_axioms[neq] = true;
        Debug("datatypes-split") << "Collapse selector " << neq << std::endl;
        addEquality( neq );
      }
    }else{
      if( useContext ){
        int cIndex = getConstructorIndex( typ, cons );
        Assert( cIndex!=-1 );
        //check labels
        Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, d_testers[typ][cIndex], tmp );
        checkTester( tester, false );
        if( !d_conflict.isNull() ){
          Debug("datatypes") << "Applied selector " << t << " to provably wrong constructor." << endl;
          retNode = d_distinguishTerms[ selType[1] ];

          Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
          NodeBuilder<> nb(kind::AND);
          Node trueNode = NodeManager::currentNM()->mkConst(true);
          if( d_conflict!=trueNode ){
            nb << d_conflict;
          }
          d_conflict = Node::null();
          tmp = find( tmp );
          if( tmp!=t[0] ){
            nb << d_cc.explain( tmp, t[0] );
          }
          Assert( nb.getNumChildren()>0 );
          Node jEq = nb.getNumChildren()==1 ? nb.getChild( 0 ) : nb;
          Debug("datatypes-drv") << "Collapse selector " << neq << std::endl;
          addDerivedEquality( neq, jEq );
        }
      }
    }
    return retNode;
  }
  return t;
}

void TheoryDatatypes::updateSelectors( Node a ){
  EqListsN::iterator sel_a_i = d_selector_eq.find( a );
  if( sel_a_i!=d_selector_eq.end() ){
    EqListN* sel_a = (*sel_a_i).second;
    Debug("datatypes") << a << " has " << sel_a->size() << " selectors" << std::endl;
    if( !sel_a->empty() ){
      EqListN* sel_b = NULL;
      for( EqListN::const_iterator i = sel_a->begin(); i!= sel_a->end(); i++ ){
        Node s = (*i);
        Node b = find( a );
        if( b!=a ){
          EqListsN::iterator sel_b_i = d_selector_eq.find( b );
          if( sel_b_i==d_selector_eq.end() ){
            sel_b = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                                  ContextMemoryAllocator<Node>(getContext()->getCMM()));
            d_selector_eq.insertDataFromContextMemory(b, sel_b);
          }else{
            sel_b = (*sel_b_i).second;
          }
          a = b;
        }
        Debug("datatypes") << "Merge selector " << s << " into " << b << std::endl;
        Debug("datatypes") << "Find is " << find( s[0] ) << std::endl;
        Assert( s.getKind()==APPLY_SELECTOR &&
                find( s[0] )==b );
        if( b!=s[0] ){
          Node t = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, s.getOperator(), b );
          //add to labels
          addTermToLabels( t );
          merge( s, t );
          s = t;
          d_selectors[s] = true;
        }
        s = collapseSelector( s, true );
        if( !d_conflict.isNull() ){
          return;
        }
        if( sel_b && s.getKind()==APPLY_SELECTOR ){
          sel_b->push_back( s );
        }
      }
    }
  }else{
    Debug("datatypes") << a << " has no selectors" << std::endl;
  }
}

void TheoryDatatypes::collectTerms( TNode t ){
  for( int i=0; i<(int)t.getNumChildren(); i++ ) {
    collectTerms( t[i] );
  }
  if( t.getKind()==APPLY_SELECTOR ){
    if( d_selectors.find( t )==d_selectors.end() ){
      Debug("datatypes-split") << "  Found selector " << t << std::endl;
      d_selectors[ t ] = true;
      Node tmp = find( t[0] );
      checkInstantiate( tmp );

      Node s = t;
      if( tmp!=t[0] ){
        s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, t.getOperator(), tmp );
      }
      Debug("datatypes-split") << "  Before collapse: " << s << std::endl;
      s = collapseSelector( s, true );
      Debug("datatypes-split") << "  After collapse: " << s << std::endl;
      if( s.getKind()==APPLY_SELECTOR ){
        //add selector to selector eq list
        Debug("datatypes") << "  Add selector to list " << tmp << " " << t << std::endl;
        EqListsN::iterator sel_i = d_selector_eq.find( tmp );
        EqListN* sel;
        if( sel_i==d_selector_eq.end() ){
          sel = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                            ContextMemoryAllocator<Node>(getContext()->getCMM()));
          d_selector_eq.insertDataFromContextMemory(tmp, sel);
        }else{
          sel = (*sel_i).second;
        }
        sel->push_back( s );
      }else{
        Debug("datatypes") << "  collapsed selector to " << s << std::endl;
      }
    }
  }
  addTermToLabels( t );
}

void TheoryDatatypes::addTermToLabels( Node t ){
  if( t.getKind()==APPLY_SELECTOR ){

  }
  if( t.getKind()==VARIABLE || t.getKind()==APPLY_SELECTOR ){
    Node tmp = find( t );
    if( tmp==t ){
      //add to labels
      EqLists::iterator lbl_i = d_labels.find(t);
      if(lbl_i == d_labels.end()) {
        EqList* lbl = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                                ContextMemoryAllocator<TNode>(getContext()->getCMM()));
        d_labels.insertDataFromContextMemory(tmp, lbl);
      }
    }
  }
}

void TheoryDatatypes::initializeEqClass( Node t ){
  EqListsN::iterator eqc_i = d_equivalence_class.find( t );
  if( eqc_i==d_equivalence_class.end() ){
    EqListN* eqc = new(getContext()->getCMM()) EqListN(true, getContext(), false,
                                          ContextMemoryAllocator<Node>(getContext()->getCMM()));
    eqc->push_back( t );
    d_equivalence_class.insertDataFromContextMemory(t, eqc);
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

void TheoryDatatypes::addDerivedEquality(TNode eq, TNode jeq){
  Debug("datatypes-drv") << "Justification for " << eq << "is: " << jeq << "." << std::endl;
  d_drv_map[eq] = jeq;
  addEquality( eq );
}

void TheoryDatatypes::addEquality(TNode eq){
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  if( eq[0]!=eq[1] ){
    Debug("datatypes") << "Add equality " << eq << "." << std::endl;
    d_merge_pending.push_back( std::vector< std::pair< Node, Node > >() );
    bool prevNoMerge = d_noMerge;
    d_noMerge = true;
    d_cc.addTerm(eq[0]);
    d_cc.addTerm(eq[1]);
    d_cc.addEquality(eq);
    d_currEqualities.push_back(eq);
    d_noMerge = prevNoMerge;
    unsigned int mpi = d_merge_pending.size()-1;
    std::vector< std::pair< Node, Node > > mp;
    mp.insert( mp.begin(), d_merge_pending[mpi].begin(), d_merge_pending[mpi].end() );
    d_merge_pending.pop_back();
    if( d_conflict.isNull() ){
      merge(eq[0], eq[1]);
    }
    for( int i=0; i<(int)mp.size(); i++ ){
      if( d_conflict.isNull() ){
        merge( mp[i].first, mp[i].second );
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
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ){
    cout << "Conflict constructed : " << d_conflict << endl;
  }
  if( d_conflict.getKind()!=kind::AND ){
    NodeBuilder<> nb(kind::AND);
    nb << d_conflict << d_conflict;
    d_conflict = nb;
  }
  d_out->conflict( d_conflict, false );
  d_conflict = Node::null();
}

void TheoryDatatypes::convertDerived(Node n, NodeBuilder<>& nb){
  if( n.getKind()==kind::AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      convertDerived( n[i], nb );
    }
  }else if( !d_drv_map[ n ].get().isNull() ){
    //Debug("datatypes") << "Justification for " << n << " is " << d_drv_map[ n ].get() << std::endl;
    convertDerived( d_drv_map[ n ].get(), nb );
  }else if( d_axioms.find( n )==d_axioms.end() ){
    nb << n;
  }
}

void TheoryDatatypes::checkCycles()
{
  for( BoolMap::iterator i = d_reps.begin(); i!= d_reps.end(); i++ ){
    if( (*i).second ){
      std::map< Node, bool > visited;
      NodeBuilder<> explanation(kind::AND);
      if( searchForCycle( (*i).first, (*i).first, visited, explanation ) ){
        Assert( explanation.getNumChildren()>0 );
        d_conflict = explanation.getNumChildren()==1 ? explanation.getChild( 0 ) : explanation;
        Debug("datatypes") << "Detected cycle for " << (*i).first << std::endl;
        Debug("datatypes") << "Conflict is " << d_conflict << std::endl;
        return;
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
bool TheoryDatatypes::searchForCycle( Node n, Node on,
                                      std::map< Node, bool >& visited,
                                      NodeBuilder<>& explanation )
{
  //Debug("datatypes") << "Search for cycle " << n << " " << on << std::endl;
  if( n.getKind()==APPLY_CONSTRUCTOR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nn = find( n[i] );
      if( visited.find( nn )==visited.end() ){
        visited[nn] = true;
        if( nn==on || searchForCycle( nn, on, visited, explanation ) ){
          if( nn!=n[i] ){
            explanation << d_cc.explain( nn, n[i] );
          }
          return true;
        }
      }
    }
  }
  return false;
}

//should be called initially with explanation of why n1 and n2 are equal
bool TheoryDatatypes::checkClash( Node n1, Node n2, NodeBuilder<>& explanation )
{
  //Debug("datatypes") << "Check clash " << n1 << " " << n2 << std::endl;
  Node n1f = find( n1 );
  Node n2f = find( n2 );
  bool retVal = false;
  if( n1f!=n2f ){
    if( n1f.getKind()==kind::APPLY_CONSTRUCTOR && n2f.getKind()==kind::APPLY_CONSTRUCTOR ){
      if( n1f.getOperator()!=n2f.getOperator() ){
        retVal =true;
      }else{
        Assert( n1f.getNumChildren()==n2f.getNumChildren() );
        for( int i=0; i<(int)n1f.getNumChildren(); i++ ){
          if( checkClash( n1f[i], n2f[i], explanation ) ){
            retVal = true;
            break;
          }
        }
      }
    }
    if( retVal ){
      if( n1f!=n1 ){
        explanation << d_cc.explain( n1f, n1 );
      }
      if( n2f!=n2 ){
        explanation << d_cc.explain( n2f, n2 );
      }
    }
  }
  return retVal;
}

bool TheoryDatatypes::checkClashSimple( Node n1, Node n2 )
{
  if( n1.getKind()==kind::APPLY_CONSTRUCTOR && n2.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( n1.getOperator()!=n2.getOperator() ){
      return true;
    }else{
      Assert( n1.getNumChildren()==n2.getNumChildren() );
      for( int i=0; i<(int)n1.getNumChildren(); i++ ){
        if( checkClashSimple( n1[i], n2[i] ) ){
          return true;
        }
      }
    }
  }
  return false;
}
