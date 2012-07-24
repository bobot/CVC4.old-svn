/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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
#include "theory/valuation.h"
#include "expr/kind.h"
#include "util/datatype.h"
#include "util/Assert.h"
#include "theory/datatypes/theory_datatypes_instantiator.h"
#include "theory/model.h"

#include <map>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

#if 1

const DatatypeConstructor& TheoryDatatypes::getConstructor( Node cons )
{
  Expr consExpr = cons.toExpr();
  return Datatype::datatypeOf(consExpr)[ Datatype::indexOf(consExpr) ];
}

Node TheoryDatatypes::getConstructorForSelector( Node sel )
{
  size_t selIndex = Datatype::indexOf( sel.toExpr() );
  const Datatype& dt = ((DatatypeType)((sel.getType()[0]).toType())).getDatatype();
  for( unsigned i = 0; i<dt.getNumConstructors(); i++ ){
    if( dt[i].getNumArgs()>selIndex &&
        Node::fromExpr( dt[i][selIndex].getSelector() )==sel ){
      return Node::fromExpr( dt[i].getConstructor() );
    }
  }
  Assert( false );
  return Node::null();
}










///--------------------------------new

TheoryDatatypes::TheoryDatatypes(Context* c, UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  Theory(THEORY_DATATYPES, c, u, out, valuation, logicInfo, qe),
  d_inst_map(c),
  d_cycle_check(c),
  d_hasSeenCycle(c, false),
  d_notify( *this ),
  d_equalityEngine(d_notify, c, "theory::datatypes::TheoryDatatypes"),
  d_conflict( c, false ){

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
}


TheoryDatatypes::~TheoryDatatypes() {
}


TheoryDatatypes::EqcInfo* TheoryDatatypes::getOrMakeEqcInfo( Node n ){
  n = getRepresentative( n );
  std::map< Node, EqcInfo* >::iterator it = d_eqc_info.find( n );
  if( it!=d_eqc_info.end() ){
    return it->second;
  }else{
    EqcInfo* ei = new EqcInfo( getSatContext() );
    d_eqc_info[ n ] = ei;
    if( n.getKind()==APPLY_CONSTRUCTOR ){
      ei->d_constructor = n;
    }
    return ei;
  }
}

/** propagate */
void TheoryDatatypes::propagate(Effort effort){

}

/** propagate */
bool TheoryDatatypes::propagate(TNode literal){
  Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryDatatypes::explain(TNode literal, std::vector<TNode>& assumptions){
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

Node TheoryDatatypes::explain( TNode literal ){
  //std::cout << "Explain " << literal << std::endl;
  std::vector< TNode > assumptions;

  explain( literal, assumptions );
  if( assumptions.empty() ){
    return Node::null();
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/** Conflict when merging two constants */
void TheoryDatatypes::conflict(TNode a, TNode b){
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain( a.iffNode(b) );
  } else {
    d_conflictNode = explain( a.eqNode(b) );
  }
  //std::cout << "CONFLICT: Eq engine conflict = " << d_conflictNode << std::endl;
  d_out->conflict( d_conflictNode );
  d_conflict = true;
}

/** called when a new equivalance class is created */
void TheoryDatatypes::eqNotifyNewClass(TNode t){
  if( t.getKind()==APPLY_CONSTRUCTOR ){
    getOrMakeEqcInfo( t );
  }
}

/** called when two equivalance classes will merge */
void TheoryDatatypes::eqNotifyPreMerge(TNode t1, TNode t2){

}

/** called when two equivalance classes have merged */
void TheoryDatatypes::eqNotifyPostMerge(TNode t1, TNode t2){
  if( !d_conflict && t1.getType().isDatatype() ){
    Node trep1 = t1;
    Node trep2 = t2;
    //std::cout << "Post merge " << t1 << " " << t2 << std::endl;
    std::map< Node, EqcInfo* >::iterator it2 = d_eqc_info.find( t2 );
    if( it2!=d_eqc_info.end() ){
      bool checkInst = false;
      EqcInfo* eqc1;
      EqcInfo* eqc2 = it2->second;
      if( !eqc2->d_constructor.get().isNull() ){
        trep2 = eqc2->d_constructor.get();
      }
      std::map< Node, EqcInfo* >::iterator it1 = d_eqc_info.find( t1 );
      if( it1!=d_eqc_info.end() ){
        eqc1 = it1->second;
        if( !eqc1->d_constructor.get().isNull() ){
          trep1 = eqc1->d_constructor.get();
        }
        //check for clash
        Node cons1 = eqc1->d_constructor;
        Node cons2 = eqc2->d_constructor;
        if( !cons1.isNull() && !cons2.isNull() ){
          if( cons1.getOperator()!=cons2.getOperator() ){
            //check for clash
            d_conflictNode = explain( cons1.eqNode( cons2 ) );
            //std::cout << "CONFLICT: Clash conflict = " << d_conflictNode << std::endl;
            d_out->conflict( d_conflictNode );
            d_conflict = true;
            return;
          }else{
            //do unification
            Node unifEq = cons1.eqNode( cons2 );
            for( int i=0; i<(int)cons1.getNumChildren(); i++ ) {
              if( !d_equalityEngine.hasTerm( cons1[i] ) || !d_equalityEngine.hasTerm( cons2[i] ) ||
                  !d_equalityEngine.areEqual( cons1[i], cons2[i] ) ){
                Node eq = cons1[i].eqNode( cons2[i] );
                d_pending.push_back( eq );
                d_pending_exp[ eq ] = unifEq;
              }
            }
          }
        }
        eqc1->d_inst = eqc1->d_inst || eqc2->d_inst;
        if( cons1.isNull() && !cons2.isNull() ){
          checkInst = true;
          eqc1->d_constructor.set( eqc2->d_constructor );
        }
      }else{
        //just copy the equivalence class information
        eqc1 = new EqcInfo( getSatContext() );
        eqc1->d_inst.set( eqc2->d_inst );
        eqc1->d_constructor.set( eqc2->d_constructor );
        d_eqc_info[ t1 ] = eqc1;
      }
      //merge labels
      for( EqList::const_iterator j = eqc2->d_labels.begin(); j != eqc2->d_labels.end(); ++j ){
        addTester( *j, eqc1 );
        if( d_conflict ){
          return;
        }
      }
      //merge selectors
      if( !eqc2->d_selectors.empty() ){
        checkInst = checkInst || eqc1->d_selectors.empty();
        for( BoolMap::iterator j = eqc2->d_selectors.begin(); j != eqc2->d_selectors.end(); ++j ){
          if( !(*j).second ){
            eqc1->d_selectors[ (*j).first ] = false;
          }
        }
      }
      if( checkInst ){
        checkInstantiate( eqc1 );
        if( d_conflict ){
          return;
        }
      }
    }
    //add this to the transitive closure module
    Node oldRep = trep2;
    Node newRep = trep1;
    if( trep1.getKind()!=APPLY_CONSTRUCTOR && trep2.getKind()==APPLY_CONSTRUCTOR ){
      oldRep = trep1;
      newRep = trep2;
    }
    //std::cout << "^ cyc : " << oldRep << " -> " << newRep << std::endl;
    bool result = d_cycle_check.addEdgeNode( oldRep, newRep );
    d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
    Debug("datatypes-cycles") << "Equal " << t1 << " -> " << t2 << " " << d_hasSeenCycle.get() << endl;
    if( d_hasSeenCycle.get() ){
      checkCycles();
      if( d_conflict ){
        return;
      }
    }
  }
}

/** called when two equivalence classes are made disequal */
void TheoryDatatypes::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){

}

void TheoryDatatypes::EqcInfo::getPossibleCons( TypeNode tn, std::vector< bool >& pcons ){
  const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
  pcons.resize( dt.getNumConstructors(), !hasLabel() );
  if( hasLabel() ){
    pcons[ getLabelIndex() ] = true;
  }else{
    for( EqList::const_iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
      Assert( (*i).getKind()==NOT );
      pcons[ Datatype::indexOf( (*i)[0].getOperator().toExpr() ) ] = false;
    }
  }
}

int TheoryDatatypes::EqcInfo::getLabelIndex(){
  if( !d_constructor.get().isNull() ){
    return Datatype::indexOf( d_constructor.get().getOperator().toExpr() );
  }else{
    return Datatype::indexOf( getLabel().getOperator().toExpr() );
  }
}

void TheoryDatatypes::addTester( TNode t, EqcInfo* eqc ){
  if( !d_conflict ){
    //std::cout << "Add tester " << t << " " << eqc << std::endl;
    bool tpolarity = t.getKind()!=NOT;
    Node tt = ( t.getKind() == NOT ) ? t[0] : t;
    int ttindex = Datatype::indexOf( tt.getOperator().toExpr() );
    Node j, jt;
    if( eqc->hasLabel() ){
      int jtindex = eqc->getLabelIndex();
      if( (jtindex==ttindex)!=tpolarity ){
        d_conflict = true;
        if( !eqc->d_constructor.get().isNull() ){
          std::vector< TNode > assumptions;
          explain( t, assumptions );
          explain( eqc->d_constructor.get().eqNode( tt[0] ), assumptions );
          d_conflictNode = NodeManager::currentNM()->mkNode( AND, assumptions );
          //std::cout << "CONFLICT: Tester eq conflict = " << d_conflictNode << std::endl;
          d_out->conflict( d_conflictNode );
          return;
        }else{
          j = eqc->getLabel();
          jt = j;
        }
      }
    }else{
      for( EqList::const_iterator i = eqc->d_labels.begin(); i != eqc->d_labels.end(); i++ ) {
        Assert( (*i).getKind()==NOT );
        j = *i;
        jt = j[0];
        int jtindex = Datatype::indexOf( jt.getOperator().toExpr() );
        if( jtindex==ttindex ){
          if( tpolarity ){  //we are in conflict
            d_conflict = true;
            break;
          }else{            //it is redundant
            return;
          }
        }
      }
      if( !d_conflict ){
        //std::cout << "Add to labels " << t << std::endl;
        eqc->d_labels.push_back( t );
        const Datatype& dt = ((DatatypeType)(tt[0].getType()).toType()).getDatatype();
        if( tpolarity ){
          checkInstantiate( eqc );
        }else{
          //check if we have reached the maximum number of testers
          // in this case, add the positive tester
          if( eqc->d_labels.size()==dt.getNumConstructors()-1 ){
            std::vector< bool > pcons;
            eqc->getPossibleCons( tt[0].getType(), pcons );
            int testerIndex = -1;
            for( int i=0; i<(int)pcons.size(); i++ ) {
              if( pcons[i] ){
                testerIndex = i;
                break;
              }
            }
            Assert( testerIndex!=-1 );
            std::vector< Node > eq_terms;
            NodeBuilder<> nb(kind::AND);
            for( EqList::const_iterator i = eqc->d_labels.begin(); i != eqc->d_labels.end(); i++ ) {
              nb << (*i);
              if( std::find( eq_terms.begin(), eq_terms.end(), (*i)[0][0] )==eq_terms.end() ){
                eq_terms.push_back( (*i)[0][0] );
                if( (*i)[0][0]!=tt[0] ){
                  nb << (*i)[0][0].eqNode( tt[0] );
                }
              }
            }
            Node trep = getRepresentative( tt[0] );
            Node t_concl = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[unsigned(testerIndex)].getTester() ), trep );
            Node t_concl_exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
            //std::cout << "We know " << t_concl << " by " << t_concl_exp << std::endl;
            d_pending.push_back( t_concl );
            d_pending_exp[ t_concl ] = t_concl_exp;
            return;
          }
        }
      }
    }
    if( d_conflict ){
      std::vector< TNode > assumptions;
      explain( j, assumptions );
      explain( t, assumptions );
      explain( jt[0].eqNode( tt[0] ), assumptions );
      d_conflictNode = NodeManager::currentNM()->mkNode( AND, assumptions );
      //std::cout << "CONFLICT: Tester conflict = " << d_conflictNode << std::endl;
      d_out->conflict( d_conflictNode );
    }
  }
}


void TheoryDatatypes::check(Effort e) {

  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;
    //std::cout << "Assert " << fact << std::endl;

    //reset the maps
    d_checkMap.clear();
    d_pending.clear();
    d_pending_exp.clear();
    //assert the fact
    assertFact( fact, fact );
    flushPendingFacts();
  }

  if( e == EFFORT_FULL ) {
    Debug("datatypes-split") << "Check for splits " << e << endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ){
      Node n = (*eqcs_i);
      if( n.getType().isDatatype() ){
        EqcInfo* eqc = getOrMakeEqcInfo( n );
        //if there are more than 1 possible constructors for eqc
        if( eqc->d_constructor.get().isNull() && !eqc->hasLabel() ) {
          const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
          //if only one constructor, then this term must be this constructor
          if( dt.getNumConstructors()==1 ){
            Node t = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[0].getTester() ), n );
            d_pending.push_back( t );
            d_pending_exp[ t ] = NodeManager::currentNM()->mkConst( true );
          }else{
            std::vector< bool > pcons;
            eqc->getPossibleCons( n.getType(), pcons );
            //std::cout << "pcons " << n << " = ";
            //for( int i=0; i<(int)pcons.size(); i++ ){ //std::cout << pcons[i] << " "; }
            //std::cout << std::endl;
            //check if we do not need to resolve the constructor type for this equivalence class.
            // this is if there are no selectors for this equivalence class, its type is infinite,
            //  and we are not producing a model, then do not split.
            Node cons;
            bool foundSel = !eqc->d_selectors.empty();
            bool needSplit = true;
            for( unsigned int j=0; j<pcons.size(); j++ ) {
              if( pcons[j] ) {
                if( cons.isNull() ){
                  cons = Node::fromExpr( dt[ j ].getConstructor() );
                }
                if( !dt[ j ].isFinite() && !foundSel ) {//&& !Options::current()->produceModels && !Options::current()->finiteModelFind ){
                  needSplit = false;
                }
              }
            }
            if( needSplit && !cons.isNull() ) {
              const DatatypeConstructor& cn = getConstructor( cons );
              //std::cout << "*************Split for possible constructor " << cons << " for " << n <<  endl;
              Node test = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), n );
              NodeBuilder<> nb(kind::OR);
              nb << test << test.notNode();
              Node lemma = nb;
              Debug("datatypes-split") << "Lemma is " << lemma << endl;
              d_out->lemma( lemma );
              d_out->requirePhase( test, true );
              return;
            }else{
              //std::cout << "Do not split constructor for " << n << std::endl;
            }
            //std::cout << "Done split" << std::endl;
          }
        }
      }
      ++eqcs_i;
    }
    flushPendingFacts();
  }
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    Notice() << "TheoryDatatypes::check(): done" << endl;
  }
  if( e==EFFORT_FULL && !d_conflict ){
    //std::cout << "Datatypes model: " << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
    while( !eqcs_i.isFinished() ){
      Node eqc = (*eqcs_i);
      if( eqc.getType().isDatatype() || eqc.getType().isBoolean() ){
        //std::cout << eqc << " : " << eqc.getType() << " : " << std::endl;
        //std::cout << "   { ";
        //add terms to model
        eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
        while( !eqc_i.isFinished() ){
          //std::cout << (*eqc_i) << " ";
          ++eqc_i;
        }
        //std::cout << "}" << std::endl;
        if( eqc.getType().isDatatype() ){
          if( d_eqc_info.find( eqc )!=d_eqc_info.end() ){
            EqcInfo* ei = d_eqc_info[eqc];
            //std::cout << "   Instantiated : " << ( ei->d_inst ? "yes" : "no" ) << std::endl;
            if( ei->d_constructor.get().isNull() ){
              //std::cout << "   Constructor : " << std::endl;
              //std::cout << "   Labels : ";
              if( ei->hasLabel() ){
                //std::cout << ei->getLabel();
              }else{
                for( EqList::const_iterator j = ei->d_labels.begin(); j != ei->d_labels.end(); j++ ){
                  //std::cout << *j << " ";
                }
              }
              //std::cout << std::endl;
            }else{
              //std::cout << "   Constructor : " << ei->d_constructor.get() << std::endl;
            }
            //std::cout << "   Selectors : ";
            for( BoolMap::iterator j = ei->d_selectors.begin(); j != ei->d_selectors.end(); j++ ){
              //std::cout << (*j).first << " ";
            }
            //std::cout << std::endl;
          }
        }
      }
      ++eqcs_i;
    }
  }
}

void TheoryDatatypes::assertFact( Node fact, Node exp ){
  collectTerms( fact );
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.assertEquality( atom, polarity, exp );
  }else{
    d_equalityEngine.assertPredicate( atom, polarity, exp );
    if( atom.getKind()==kind::APPLY_TESTER ){
      EqcInfo* eqc = getOrMakeEqcInfo( atom[0] );
      addTester( fact, eqc );
    }
  }
}

void TheoryDatatypes::flushPendingFacts(){
  //also assert the pending facts
  int i = 0;
  while( !d_conflict && i<(int)d_pending.size() ){
    assertFact( d_pending[i], d_pending_exp[ d_pending[i] ] );
    i++;
  }
  d_pending.clear();
  d_pending_exp.clear();
}

void TheoryDatatypes::preRegisterTerm(TNode n) {
  Debug("datatypes-prereg") << "TheoryDatatypes::preRegisterTerm() " << n << endl;
  switch (n.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::APPLY_TESTER:
    // Get triggered for both equal and dis-equal
    d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    // Variables etc
    d_equalityEngine.addTerm(n);
    break;
  }
}

void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                     << t << endl;
}

void TheoryDatatypes::collectModelInfo( TheoryModel* m ){
  //std::cout << "Datatypes model: " << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( eqc.getType().isDatatype() || eqc.getType().isBoolean() ){
      //std::cout << eqc << " : " << eqc.getType() << " : " << std::endl;
      //std::cout << "   ";
      //add terms to model
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ){
        //std::cout << (*eqc_i) << " ";
        ++eqc_i;
      }
      //std::cout << std::endl;
      if( eqc.getType().isDatatype() ){
        if( d_eqc_info.find( eqc )!=d_eqc_info.end() ){
          EqcInfo* ei = d_eqc_info[eqc];
          //std::cout << "   Constructor : " << ei->d_constructor.get() << std::endl;
          if( ei->d_constructor.get().isNull() ){
            //std::cout << "   Labels : ";
            if( ei->hasLabel() ){
              //std::cout << ei->getLabel();
            }else{
              for( EqList::const_iterator j = ei->d_labels.begin(); j != ei->d_labels.end(); j++ ){
                //std::cout << *j << " ";
              }
            }
            //std::cout << std::endl;
          }
          //std::cout << "   Selectors : ";
          for( BoolMap::iterator j = ei->d_selectors.begin(); j != ei->d_selectors.end(); j++ ){
            //std::cout << (*j).first << " ";
          }
          //std::cout << std::endl;
        }
      }
    }
    ++eqcs_i;
  }
  m->assertEqualityEngine( &d_equalityEngine );
}


void TheoryDatatypes::collectTerms( Node n ) {
  for( int i=0; i<(int)n.getNumChildren(); i++ ) {
    collectTerms( n[i] );
  }
  if( n.getKind() == APPLY_CONSTRUCTOR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      //std::cout << "^ cyc : " << n << " -> " << n[i] << std::endl;
      Debug("datatypes-cycles") << "Subterm " << n << " -> " << n[i] << endl;
      bool result = d_cycle_check.addEdgeNode( n, n[i] );
      d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
    }
  }else if( n.getKind() == APPLY_SELECTOR ){
    Debug("datatypes") << "  Found selector " << n << endl;
    Node argRep = getRepresentative( n[0] );
    EqcInfo* eqc = getOrMakeEqcInfo( argRep );
    if( eqc->d_selectors.find( n.getOperator() )==eqc->d_selectors.end() ){
      bool checkInst = eqc->d_selectors.empty();
      d_equalityEngine.addTerm( n );
      //add selector to selector eq list
      eqc->d_selectors[ n ] = false;
      if( checkInst ){
        checkInstantiate( eqc );
      }
    }
  }
}

Node TheoryDatatypes::getInstantiateCons( Node n, const Datatype& dt, int index ){
  //add constructor to equivalence class
  std::vector< Node > children;
  children.push_back( Node::fromExpr( dt[index].getConstructor() ) );
  for( int i=0; i<(int)dt[index].getNumArgs(); i++ ){
    children.push_back( NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[index][i].getSelector() ), n ) );
  }
  Node n_ic = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
  //TODO: add type ascription for ambiguous constructor type?
  collectTerms( n_ic );
  return n_ic;
}

void TheoryDatatypes::checkInstantiate( EqcInfo* eqc ){
  //add constructor to equivalence class if not done so already
  if( eqc->hasLabel() && !eqc->d_inst ){
    Node exp;
    Node tt;
    if( !eqc->d_constructor.get().isNull() ){
      exp = NodeManager::currentNM()->mkConst( true );
      tt = eqc->d_constructor;
    }else{
      exp = eqc->getLabel();
      tt = exp[0];
    }
    int index = eqc->getLabelIndex();
    ////std::cout << tt << " " << exp << " " << index << std::endl;
    const Datatype& dt = ((DatatypeType)(tt.getType()).toType()).getDatatype();
    //must be finite or have a selector
    if( !eqc->d_selectors.empty() || dt[ index ].isFinite() ){
      Node tt_cons = getInstantiateCons( tt, dt, index );
      if( tt!=tt_cons ){
        Node eq = tt.eqNode( tt_cons );
        //std::cout << ">>>INSTANTIATE " << eqc << " " << eq << std::endl;
        d_pending.push_back( eq );
        d_pending_exp[ eq ] = exp;
      }
      eqc->d_inst = true;
    }else{
      ////std::cout << "do not instantiate " << eqc << " ( " << tt << " ), " << eqc->d_selectors.empty() << " " << dt[ index ].isFinite() << std::endl;
    }
  }else{
    ////std::cout << "do not instantiate " << eqc  << ", already instantiated or not ready" << eqc->hasLabel() << " " << eqc->d_inst << std::endl;
  }
}

void TheoryDatatypes::checkCycles() {
  //std::cout << "Check cycles" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    map< Node, bool > visited;
    NodeBuilder<> explanation(kind::AND);
    if( searchForCycle( eqc, eqc, visited, explanation ) ) {
      d_conflictNode = explanation.getNumChildren() == 1 ? explanation.getChild( 0 ) : explanation;
      //std::cout << "CONFLICT: Cycle conflict : " << d_conflictNode << std::endl;
      d_out->conflict( d_conflictNode );
      d_conflict = true;
      Debug("datatypes") << "Detected cycle for " << eqc << endl;
      Debug("datatypes") << "Conflict is " << d_conflictNode << endl;
      return;
    }
    ++eqcs_i;
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
bool TheoryDatatypes::searchForCycle( Node n, Node on,
                                      map< Node, bool >& visited,
                                      NodeBuilder<>& explanation ) {
  //Debug("datatypes") << "Search for cycle " << n << " " << on << endl;
  Node ncons;
  std::map< Node, EqcInfo* >::iterator it = d_eqc_info.find( n );
  if( it!=d_eqc_info.end() ){
    EqcInfo* eqc = it->second;
    Node ncons = eqc->d_constructor.get();
    if( !ncons.isNull() ) {
      for( int i=0; i<(int)ncons.getNumChildren(); i++ ) {
        Node nn = getRepresentative( ncons[i] );
        if( visited.find( nn ) == visited.end() ) {
          visited[nn] = true;
          if( nn == on || searchForCycle( nn, on, visited, explanation ) ) {
            if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n, ncons[i] ) ){
              Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << ncons[i] << "!!!!" << std::endl;
            }
            if( nn != ncons[i] ) {
              if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( ncons[i], nn ) ){
                Debug("datatypes-cycles") << "Cycle equality: " << ncons[i] << " is not -> " << nn << "!!!!" << std::endl;
              }
              explanation << NodeManager::currentNM()->mkNode( EQUAL, nn, ncons[i] );
            }
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool TheoryDatatypes::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryDatatypes::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryDatatypes::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

Node TheoryDatatypes::getRepresentative( Node a ){
  if( hasTerm( a ) ){
    return d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}

///--------------------------------/new


#else
/*
const DatatypeConstructor& TheoryDatatypes::getConstructor( Node cons )
{
  Expr consExpr = cons.toExpr();
  return Datatype::datatypeOf(consExpr)[ Datatype::indexOf(consExpr) ];
}

Node TheoryDatatypes::getConstructorForSelector( Node sel )
{
  size_t selIndex = Datatype::indexOf( sel.toExpr() );
  const Datatype& dt = ((DatatypeType)((sel.getType()[0]).toType())).getDatatype();
  for( unsigned i = 0; i<dt.getNumConstructors(); i++ ){
    if( dt[i].getNumArgs()>selIndex &&
        Node::fromExpr( dt[i][selIndex].getSelector() )==sel ){
      return Node::fromExpr( dt[i].getConstructor() );
    }
  }
  Assert( false );
  return Node::null();
}


TheoryDatatypes::TheoryDatatypes(Context* c, UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  Theory(THEORY_DATATYPES, c, u, out, valuation, logicInfo, qe),
  d_currAsserts(c),
  d_currEqualities(c),
  d_selectors(c),
  d_reps(c),
  d_selector_eq(c),
  d_equivalence_class(c),
  d_inst_map(c),
  d_cycle_check(c),
  d_hasSeenCycle(c, false),
  d_labels(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_disequalities(c),
  d_em(c),
  d_cce(&d_cc){
}


TheoryDatatypes::~TheoryDatatypes() {
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                     << t << endl;
}

void TheoryDatatypes::notifyCongruent(TNode lhs, TNode rhs) {
  Debug("datatypes") << "TheoryDatatypes::notifyCongruent(): "
                     << lhs << " = " << rhs << endl;
  if(!hasConflict()) {
    merge(lhs,rhs);
  }
  Debug("datatypes-debug") << "TheoryDatatypes::notifyCongruent(): done." << endl;
}

void TheoryDatatypes::preRegisterTerm(TNode n) {
  Debug("datatypes-prereg") << "TheoryDatatypes::preRegisterTerm() " << n << endl;
}


void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

void TheoryDatatypes::check(Effort e) {

  for( int i=0; i<(int)d_currAsserts.size(); i++ ) {
    Debug("datatypes") << "currAsserts[" << i << "] = " << d_currAsserts[i] << endl;
  }
  for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
    Debug("datatypes") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
  }

  while(!done()) {
    Node assertion = get();
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") || Debug.isOn("datatypes-cycles")
        || Debug.isOn("datatypes-debug-pf") || Debug.isOn("datatypes-conflict") ) {
      Notice() << "*** TheoryDatatypes::check(): " << assertion << endl;
      d_currAsserts.push_back( assertion );
    }

    //clear from the derived map
    d_checkMap.clear();
    collectTerms( assertion );
    if( !hasConflict() ){
      if( d_em.hasNode( assertion ) ){
        Debug("datatypes") << "Assertion has already been derived" << endl;
        d_em.assertTrue( assertion );
      } else {
        switch(assertion.getKind()) {
        case kind::EQUAL:
        case kind::IFF:
          addEquality(assertion);
          break;
        case kind::APPLY_TESTER:
          addTester( assertion );
          break;
        case kind::NOT:
          {
            switch( assertion[0].getKind()) {
            case kind::EQUAL:
            case kind::IFF:
              {
                Node a = assertion[0][0];
                Node b = assertion[0][1];
                addDisequality(assertion[0]);
                d_cc.addTerm(a);
                d_cc.addTerm(b);
                if(Debug.isOn("datatypes")) {
                  Debug("datatypes") << "       a  == > " << a << endl
                              << "       b  == > " << b << endl
                              << "  find(a) == > " << debugFind(a) << endl
                              << "  find(b) == > " << debugFind(b) << endl;
                }
                // There are two ways to get a conflict here.
                if(!hasConflict()) {
                  if(find(a) == find(b)) {
                    // We get a conflict this way if we WERE previously watching
                    // a, b and were notified previously (via notifyCongruent())
                    // that they were congruent.
                    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, assertion[0][0], assertion[0][1] );
                    NodeBuilder<> nbc(kind::AND);
                    nbc << ccEq << assertion;
                    Node contra = nbc;
                    d_em.addNode( ccEq, &d_cce );
                    d_em.addNodeConflict( contra, Reason::contradiction );
                  } else {
                    // If we get this far, there should be nothing conflicting due
                    // to this disequality.
                    Assert(!d_cc.areCongruent(a, b));
                  }
                }
              }
              break;
            case kind::APPLY_TESTER:
              addTester( assertion );
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
    }
    //rules to check for collapse, instantiate
    while( !hasConflict() && !d_checkMap.empty() ){
      std::map< Node, bool > temp;
      temp = d_checkMap;
      d_checkMap.clear();
      std::map< Node, bool >::iterator i;
      for( i = temp.begin(); i != temp.end(); i++ ){
        Node n = find( i->first );
        if( temp.find( n )==temp.end() || temp[n] ){
          if( !hasConflict() ) checkInstantiateEqClass( n );
          if( !hasConflict() ) updateSelectors( n );
          temp[n] = false;
        }
      }
    }
    //if there is now a conflict
    if( hasConflict() ) {
      Debug("datatypes-conflict") << "Constructing conflict..." << endl;
      for( int i=0; i<(int)d_currAsserts.size(); i++ ) {
        Debug("datatypes-conflict") << "currAsserts[" << i << "] = " << d_currAsserts[i] << endl;
      }
      //Debug("datatypes-conflict") << d_cc << std::endl;
      Node conflict = d_em.getConflict();
      if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ||
          Debug.isOn("datatypes-cycles") || Debug.isOn("datatypes-conflict") ){
        Notice() << "Conflict constructed : " << conflict << endl;
      }
      if( conflict.getKind()!=kind::AND ){
        conflict = NodeManager::currentNM()->mkNode(kind::AND, conflict, conflict);
      }
      d_out->conflict(conflict);
      return;
    }
  }

  if( e == EFFORT_FULL ) {
    Debug("datatypes-split") << "Check for splits " << e << endl;
    //do splitting
    for( EqLists::iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
      Node sf = find( (*i).first );
      if( sf.getKind() != APPLY_CONSTRUCTOR ) {
        addTermToLabels( sf );
        EqList* lbl = (sf == (*i).first) ? (*i).second : (*d_labels.find( sf )).second;
        Debug("datatypes-split") << "Check for splitting " << (*i).first
                                 << ", label size = " << lbl->size() << endl;
        if( lbl->empty() || (*lbl)[ lbl->size()-1 ].getKind() == NOT ) {    //there are more than 1 possible constructors for sf
          const Datatype& dt = ((DatatypeType)(sf.getType()).toType()).getDatatype();
          vector< bool > possibleCons;
          possibleCons.resize( dt.getNumConstructors(), true );
          for( EqList::const_iterator j = lbl->begin(); j != lbl->end(); j++ ) {
            TNode leqn = (*j);
            possibleCons[ Datatype::indexOf( leqn[0].getOperator().toExpr() ) ] = false;
          }
          Node cons;
          bool foundSel = false;
          for( unsigned int j=0; j<possibleCons.size(); j++ ) {
            if( !foundSel && possibleCons[j] ) {
              cons = Node::fromExpr( dt[ j ].getConstructor() );
              //if there is a selector, split
              for( unsigned int k=0; k<dt[ j ].getNumArgs(); k++ ) {
                Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[j][k].getSelector() ), sf );
                if( d_selectors.find( s ) != d_selectors.end() ) {
                  foundSel = true;
                  break;
                }
              }
            }
          }
          //check if we do not need to resolve the constructor type for this equivalence class.
          // this is if there are no selectors for this equivalence class, its type is infinite,
          //  and we are not producing a model.
          if( !foundSel && !Options::current()->produceModels && !Options::current()->finiteModelFind ){
            for( unsigned int j=0; j<possibleCons.size(); j++ ) {
              if( possibleCons[j] && !dt[ j ].isFinite() ) {
                Debug("datatypes") << "Did not find selector for " << sf
                                  << " and " << dt[ j ].getConstructor() << " is not finite." << endl;
                cons = Node::null();
                break;
              }
            }
          }
          if( !cons.isNull() ) {
            const DatatypeConstructor& cn = getConstructor( cons );
            Debug("datatypes-split") << "*************Split for possible constructor " << cons << endl;
#if 1
            Node test = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), (*i).first );
            NodeBuilder<> nb(kind::OR);
            nb << test << test.notNode();
#else
            std::vector< Node > children;
            children.push_back( Node::fromExpr( cn.getConstructor() ) );
            for( int j=0; j<cn.getNumArgs(); j++ ){
              children.push_back( NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[j].getSelector() ), (*i).first ) );
            }
            Node i_cons = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
            Node eq = i_cons.eqNode( (*i).first );
            NodeBuilder<> nb(kind::OR);
            nb << eq << eq.notNode();
#endif
            Node lemma = nb;
            Debug("datatypes-split") << "Lemma is " << lemma << endl;
            //Message() << "Lemma is " << lemma << std::endl;
            d_out->lemma( lemma );
            return;
          }
        }
      } else {
        Debug("datatypes-split") << (*i).first << " is " << sf << endl;
        Assert( sf != (*i).first );
      }
    }
  }
  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    Notice() << "TheoryDatatypes::check(): done" << endl;
  }
#if 0
  if( e == EFFORT_FULL ) {
    //complete model if necessary
    bool eqAdded = false;
    if( Options::current()->produceModels || Options::current()->finiteModelFind ){
      for( EqLists::iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
        Node n = find( (*i).first );
        if( n.getKind() != APPLY_CONSTRUCTOR ) {
          addTermToLabels( n );
          EqList* lbl = (n == (*i).first) ? (*i).second : (*d_labels.find( n )).second;
          if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind() == APPLY_TESTER ) {
            const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
            int j = Datatype::indexOf( (*lbl)[ lbl->size()-1 ].getOperator().toExpr() );
            std::vector< Node > children;
            children.push_back( Node::fromExpr( dt[j].getConstructor() ) );
            for( int i=0; i<dt[j].getNumArgs(); i++ ){
              children.push_back( NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[j][i].getSelector() ), n ) );
            }
            Node cons = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
            if( find( n )!=find( cons ) ){
              Message() << "Assert " << n << " = " << cons << ", by " << (*lbl)[ lbl->size()-1 ] << std::endl;
              Node newEq = NodeManager::currentNM()->mkNode( EQUAL, n, cons );
              collectTerms( newEq );
              d_em.addNode( newEq, (*lbl)[ lbl->size()-1 ], 0 );
              addEquality( newEq );
              eqAdded = true;
            }
          }
        }
      }
    }
    if( eqAdded ){
      check( e );
    }
  }
#endif
}

bool TheoryDatatypes::checkTester( Node assertion, Node& conflict, unsigned& r ){
  Debug("datatypes") << "Check tester " << assertion << endl;

  Node tassertion = ( assertion.getKind() == NOT ) ? assertion[0] : assertion;
  Assert( find( tassertion[0] ) == tassertion[0] );

  //if argument is a constructor, it is trivial
  if( tassertion[0].getKind() == APPLY_CONSTRUCTOR ) {
    size_t tIndex = Datatype::indexOf(tassertion.getOperator().toExpr());
    size_t cIndex = Datatype::indexOf(tassertion[0].getOperator().toExpr());
    if( (tIndex==cIndex) == (assertion.getKind() == NOT) ) {
      conflict = assertion;
      r = Reason::idt_tclash;
    }
    return false;
  }

  addTermToLabels( tassertion[0] );
  EqList* lbl = (*d_labels.find( tassertion[0] )).second;
  //check if empty label (no possible constructors for term)
  for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
    Node leqn = (*i);
    Debug("datatypes-debug") << "checking " << leqn << std::endl;
    if( leqn.getKind() == kind::NOT ) {
      if( leqn[0].getOperator() == tassertion.getOperator() ) {
        if( assertion.getKind() != NOT ) {
          conflict = NodeManager::currentNM()->mkNode( AND, leqn, assertion );
          r = Reason::contradiction;
          Debug("datatypes") << "Contradictory labels " << conflict << endl;
        }
        return false;
      }
    }else{
      if( (leqn.getOperator() == tassertion.getOperator()) == (assertion.getKind() == NOT) ) {
        conflict = NodeManager::currentNM()->mkNode( AND, leqn, assertion );
        r = Reason::idt_tclash;
        Debug("datatypes") << "Contradictory labels(2) " << conflict << endl;
      }
      return false;
    }
  }
  return true;
}

void TheoryDatatypes::addTester( Node assertion ){
  Debug("datatypes") << "addTester " << assertion << endl;

  //preprocess the tester
  Node tassertion = ( assertion.getKind() == NOT ) ? assertion[0] : assertion;
  //add the term into congruence closure consideration
  d_cc.addTerm( tassertion[0] );

  Node assertionRep;
  Node tassertionRep;
  Node tRep = tassertion[0];
  tRep = find( tRep );
  //add label instead for the representative (if it is different)
  if( tRep != tassertion[0] ) {
    //explanation is trivial (do not add to labels)
    if( tRep.getKind()==APPLY_CONSTRUCTOR && assertion.getKind()== kind::APPLY_TESTER &&
        Datatype::indexOf(assertion.getOperator().toExpr())==Datatype::indexOf(tRep.getOperator().toExpr()) ){
      tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
      assertionRep = tassertionRep;
      d_em.addNodeAxiom( assertionRep, Reason::idt_taxiom );
      return;
    }else{
      tassertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, tassertion.getOperator(), tRep );
      assertionRep = ( assertion.getKind() == NOT ) ? tassertionRep.notNode() : tassertionRep;
      //add explanation
      Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, tRep, tassertion[0] );
      d_em.addNode( ccEq, &d_cce );
      NodeBuilder<> nb2(kind::AND);
      nb2 << assertion << ccEq;
      Node expl = nb2;
      d_em.addNode( assertionRep, expl, Reason::idt_tcong );
    }
  }else{
    tassertionRep = tassertion;
    assertionRep = assertion;
  }

  Node conflict;
  unsigned r;
  if( checkTester( assertionRep, conflict, r ) ){
    //it is not redundant/contradictory, add it to labels
    EqLists::iterator lbl_i = d_labels.find( tRep );
    EqList* lbl = (*lbl_i).second;
    lbl->push_back( assertionRep );
    Debug("datatypes") << "Add to labels " << assertionRep << endl;
    if( assertionRep.getKind()==NOT ){
      const Datatype& dt = Datatype::datatypeOf( tassertion.getOperator().toExpr() );
      //we can conclude the final one
      if( lbl->size()==dt.getNumConstructors()-1 ){
        vector< bool > possibleCons;
        possibleCons.resize( dt.getNumConstructors(), true );
        NodeBuilder<> nb(kind::AND);
        for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
          possibleCons[ Datatype::indexOf( (*i)[0].getOperator().toExpr() ) ] = false;
          nb << (*i);
        }
        int testerIndex = -1;
        for( int i=0; i<(int)possibleCons.size(); i++ ) {
          if( possibleCons[i] ){
            testerIndex = i;
          }
        }
        Assert( testerIndex!=-1 );
        assertionRep = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[unsigned(testerIndex)].getTester() ), tRep );
        Node exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
        d_em.addNode( assertionRep, exp, Reason::idt_texhaust );
        addTester( assertionRep );    //add stronger statement
        return;
      }
    }
    if( assertionRep.getKind()==APPLY_TESTER ){
      d_checkMap[ tRep ] = true;
    }
  }else if( !conflict.isNull() ){
    d_em.addNodeConflict( conflict, r );
  }
}

//if only one constructor remaining for t, this function will return it
Node TheoryDatatypes::getInstantiateCons( Node t ){
  if( t.getKind() != APPLY_CONSTRUCTOR ){
    Assert( t == find( t ) );
    addTermToLabels( t );
    EqLists::iterator lbl_i = d_labels.find( t );
    if( lbl_i!=d_labels.end() ) {
      EqList* lbl = (*lbl_i).second;
      if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind() != NOT ) {
        const Datatype& dt = ((DatatypeType)(t.getType()).toType()).getDatatype();
        size_t testerIndex = Datatype::indexOf( (*lbl)[ lbl->size()-1 ].getOperator().toExpr() );
        return Node::fromExpr( dt[ testerIndex ].getConstructor() );
      }
    }
  }
  return Node::null();
}

void TheoryDatatypes::checkInstantiateEqClass( Node t ) {
  Debug("datatypes") << "TheoryDatatypes::checkInstantiateEqClass() " << t << endl;
  Assert( t == find( t ) );

  //if labels were created for t, and t has not been instantiated
  Node cons = getInstantiateCons( t );
  if( !cons.isNull() ){
    //for each term in equivalance class
    initializeEqClass( t );
    EqListN* eqc = (*d_equivalence_class.find( t )).second;
    for( EqListN::const_iterator iter = eqc->begin(); iter != eqc->end(); iter++ ) {
      Node te = *iter;
      Assert( find( te ) == t );
      if( checkInstantiate( te, cons ) ){
        return;
      }
    }
  }
}

//pre condition: find( te ) has been proven to be the constructor cons
//that is, is_[cons]( find( te ) ) is stored in d_labels
bool TheoryDatatypes::checkInstantiate( Node te, Node cons )
{
  Debug("datatypes") << "TheoryDatatypes::checkInstantiate() " << te << endl;
  //if term has not yet been instantiated
  if( d_inst_map.find( te ) == d_inst_map.end() ) {
    //find if selectors have been applied to t
    vector< Node > selectorVals;
    selectorVals.push_back( cons );
    bool foundSel = false;
    const DatatypeConstructor& cn = getConstructor( cons );
    for( unsigned int i=0; i<cn.getNumArgs(); i++ ) {
      Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[i].getSelector() ), te );
      if( d_selectors.find( s ) != d_selectors.end() ) {
        foundSel = true;
        s = find( s );
      }
      selectorVals.push_back( s );
    }
    if( cn.isFinite() || foundSel ) {
      d_inst_map[ te ] = true;
      Node val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
      //instantiate, add equality
      if( val.getType()!=te.getType() ){ //IDT-param
        Assert( Datatype::datatypeOf( cons.toExpr() ).isParametric() );
        Debug("datatypes-gt") << "Inst: ambiguous type for " << cons << ", ascribe to " << te.getType() << std::endl;
        const DatatypeConstructor& dtc = Datatype::datatypeOf(cons.toExpr())[Datatype::indexOf(cons.toExpr())];
        Debug("datatypes-gt") << "constructor is " << dtc << std::endl;
        Type tspec = dtc.getSpecializedConstructorType(te.getType().toType());
        Debug("datatypes-gt") << "tpec is " << tspec << std::endl;
        selectorVals[0] = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                            NodeManager::currentNM()->mkConst(AscriptionType(tspec)), cons);
        val = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, selectorVals );
      }
      if( find( val ) != find( te ) ) {
        //build explaination
        NodeBuilder<> nb(kind::AND);
        //explanation for tester
        Node t = find( te );
        addTermToLabels( t );
        Assert( d_labels.find( t )!=d_labels.end() );
        EqList* lbl = (*d_labels.find( t )).second;
        nb << (*lbl)[ lbl->size()-1 ];    //this should be changed to be tester for te, not t for fine-grained
        //explanation for arguments
        for( unsigned int i=0; i<cn.getNumArgs(); i++ ) {
          Node s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( cn[i].getSelector() ), te );
          if( selectorVals[i+1]!=s ){
            Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, selectorVals[i+1], s );
            d_em.addNode( ccEq, &d_cce );
            nb << ccEq;
          }else{
            //reflexive for s, if we want idt_inst to be fined grained
            //Node eq = NodeManager::currentNM()->mkNode( EQUAL, s, s );
            //d_em.addNodeAxiom( s, Reason::refl );
          }
        }
        Node jeq = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, val, te );
        Debug("datatypes") << "Instantiate: " << newEq << "." << endl;
        d_em.addNode( newEq, jeq, Reason::idt_inst_coarse );
        //collect terms of instantiation term
        collectTerms( val, false );
        //add equality for the instantiation
        addEquality( newEq );
        return true;
      }
    } else {
      Debug("datatypes") << "Do not Instantiate: infinite constructor, no selectors " << cons << endl;
    }
  }else{
    Debug("datatypes") << "Do not Instantiate: " << te << " already instantiated" << endl;
  }
  return false;
}

bool TheoryDatatypes::collapseSelector( Node t ) {
  if( !hasConflict() && t.getKind() == APPLY_SELECTOR ) {
    //collapse constructor
    TypeNode retTyp = t.getType();
    TypeNode typ = t[0].getType();
    Node sel = t.getOperator();
    TypeNode selType = sel.getType();
    Node cons = getConstructorForSelector( sel );
    const DatatypeConstructor& cn = getConstructor( cons );
    Node tmp = find( t[0] );
    Node retNode = t;
    if( tmp.getKind() == APPLY_CONSTRUCTOR ) {
      if( tmp.getOperator() == cons ) {
        Debug("datatypes") << "Applied selector " << t << " to correct constructor." << endl;
        retNode = tmp[ Datatype::indexOf( sel.toExpr() ) ];
      } else {
        Debug("datatypes") << "Applied selector " << t << " to wrong constructor." << endl;
        retNode = retTyp.mkGroundTerm();    //IDT-param
      }
      if( tmp!=t[0] ){
        t = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, t.getOperator(), tmp );
      }
      Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );
      d_em.addNodeAxiom( neq, Reason::idt_collapse );
      Debug("datatypes") << "Add collapse equality " << neq << endl;
      addEquality( neq );
      return true;
    } else {
      //see whether we can prove that the selector is applied to the wrong tester
      Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), tmp );
      Node conflict;
      unsigned r;
      checkTester( tester, conflict, r );
      if( !conflict.isNull() ) {
        Debug("datatypes") << "Applied selector " << t << " to provably wrong constructor. " << retTyp << endl;
        //conflict is c ^ tester, where conflict => false, but we want to say c => ~tester
        //must remove tester from conflict
        if( conflict.getKind()==kind::AND ){
          NodeBuilder<> jt(kind::AND);
          for( int i=0; i<(int)conflict.getNumChildren(); i++ ){
            if( conflict[i]!=tester ){
              jt << conflict[i];
            }
          }
          conflict = ( jt.getNumChildren()==1 ) ? jt.getChild( 0 ) : jt;
        }else{
          Assert( conflict==tester );
          conflict = Node::null();
        }
        if( conflict!=tester.notNode() ){
          d_em.addNode( tester.notNode(), conflict, r );    //note that application of r is non-standard (TODO: fix)
        }

        if( tmp != t[0] ) {
          Node teq = NodeManager::currentNM()->mkNode( EQUAL, tmp, t[0] );
          d_em.addNode( teq, &d_cce );
          Node exp = NodeManager::currentNM()->mkNode( AND, tester.notNode(), teq );
          tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( cn.getTester() ), t[0] );
          d_em.addNode( tester.notNode(), exp, Reason::idt_tcong );
        }
        retNode = retTyp.mkGroundTerm();    //IDT-param
        Node neq = NodeManager::currentNM()->mkNode( EQUAL, retNode, t );

        d_em.addNode( neq, tester.notNode(), Reason::idt_collapse2 );
        addEquality( neq );
        return true;
      }
    }
  }
  return false;
}

//this function will test if each selector whose argument is in the equivalence class of "a" can be collapsed
void TheoryDatatypes::updateSelectors( Node a ) {
  Debug("datatypes") << "updateSelectors: " << a << endl;
  EqListsN::iterator sel_a_i = d_selector_eq.find( a );
  if( sel_a_i != d_selector_eq.end() ) {
    EqListN* sel_a = (*sel_a_i).second;
    for( EqListN::const_iterator i = sel_a->begin(); i != sel_a->end(); i++ ) {
      Node s = (*i);
      //if a is still a representative, and s has not yet been collapsed
      if( find( a )==a && !d_selectors[s] ){
        Assert( s.getKind()==APPLY_SELECTOR && find( s[0] ) == a );
        if( a != s[0] ) {
          s = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, s.getOperator(), a );
          collectTerms( s, false );
        }
        d_selectors[s] = collapseSelector( s );
      }
    }
  }
}

void TheoryDatatypes::collectModelInfo( TheoryModel* m ){
  std::map< Node, bool > processed;
  //assert all equalities in equivalence classes
  for( EqLists::iterator i = d_labels.begin(); i != d_labels.end(); i++ ) {
    Node n = (*i).first;
    Node r = find( n );
    if( processed.find( r )==processed.end() ){
      processed[r] = true;
      TypeNode tn = r.getType();
      Assert( tn.isDatatype() );
      Node eqc_cons = r.getKind()==APPLY_CONSTRUCTOR ? r : Node::null();
      EqListsN::iterator eqc_r_i = d_equivalence_class.find( r );
      if( eqc_r_i!=d_equivalence_class.end() ){
        EqListN* eqc = (*eqc_r_i).second;
        for( EqListN::const_iterator iter = eqc->begin(); iter != eqc->end(); iter++ ) {
          if( (*iter)!=r ){
            m->assertEquality( r, *iter, true );
            if( (*iter).getKind()==APPLY_CONSTRUCTOR ){
              eqc_cons = *iter;
            }
          }
        }
      }
      //if we have not yet assigned a constructor, do so
      if( eqc_cons.isNull()){
        vector< bool > possibleCons;
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        possibleCons.resize( dt.getNumConstructors(), true );
        addTermToLabels( r );
        EqList* lbl = (r == (*i).first) ? (*i).second : (*d_labels.find( r )).second;
        for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
          Node t = *i;
          if( t.getKind()==NOT ){
            Assert( t[0].getKind()==APPLY_TESTER );
            possibleCons[ Datatype::indexOf( t[0].getOperator().toExpr() ) ] = false;
          }else{
            Assert( t.getKind()==APPLY_TESTER );
            int index = Datatype::indexOf( t.getOperator().toExpr() );
            for( int j=0; j<(int)dt.getNumConstructors(); j++ ){
              if( j!=index ){
                possibleCons[ j ] = false;
              }
            }
          }
        }
        //must do a constructor (just choose the first one)
        for( unsigned int j=0; j<possibleCons.size(); j++ ) {
          if( possibleCons[j] ) {
            std::vector< Node > children;
            children.push_back( Node::fromExpr( dt[j].getConstructor() ) );
            for( int i=0; i<dt[j].getNumArgs(); i++ ){
              children.push_back( NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[j][i].getSelector() ), r ) );
            }
            eqc_cons = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
            Message() << "Assign " << eqc_cons << " to " << r << std::endl;
            m->assertEquality( r, eqc_cons, true );
            break;
          }
        }
      }
      Assert( !eqc_cons.isNull() );
    }
  }
}

void TheoryDatatypes::merge(TNode a, TNode b) {
  if( !d_merge_pending.empty() ) {
    //Debug("datatypes") << "Append to merge pending list " << d_merge_pending.size() << endl;
    d_merge_pending[d_merge_pending.size()-1].push_back( pair< Node, Node >( a, b ) );
    return;
  }
  Assert(!hasConflict());
  a = find(a);
  b = find(b);
  if( a == b) {
    return;
  }
  Debug("datatypes") << "Merge "<< a << " " << b << endl;

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
  if( b.getKind() == APPLY_SELECTOR && a.getKind() != APPLY_SELECTOR ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make constructors the representatives
  if( a.getKind() == APPLY_CONSTRUCTOR ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }
  //make sure skolem variable is not representative
  if( b.getKind() == SKOLEM ) {
    TNode tmp = a;
    a = b;
    b = tmp;
  }

  //check for clash
  NodeBuilder<> explanation(kind::AND);
  if( a.getKind() == kind::APPLY_CONSTRUCTOR && b.getKind() == kind::APPLY_CONSTRUCTOR
      && a.getOperator()!=b.getOperator() ){
    Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, a, b );
    d_em.addNode( ccEq, &d_cce );
    d_em.addNodeConflict( ccEq, Reason::idt_clash );
    Debug("datatypes") << "Clash " << a << " " << b << endl;
    return;
  }
  Debug("datatypes-debug") << "Done clash" << endl;

  Debug("datatypes-ae") << "Set canon: "<< a << " " << b << endl;
  // b becomes the canon of a
  d_unionFind.setCanon(a, b);
  d_reps[a] = false;
  d_reps[b] = true;

  //add this to the transitive closure module
  bool result = d_cycle_check.addEdgeNode( a, b );
  d_hasSeenCycle.set( d_hasSeenCycle.get() || result );
  Debug("datatypes-cycles") << "Equal " << a << " -> " << b << " " << d_hasSeenCycle.get() << endl;
  if( d_hasSeenCycle.get() ){
    checkCycles();
    if( hasConflict() ){
      return;
    }
  }
  //else{
  //  checkCycles();
  //  if( hasConflict() ){
  //    for( int i=0; i<(int)d_currEqualities.size(); i++ ) {
  //      Debug("datatypes-cycles") << "currEqualities[" << i << "] = " << d_currEqualities[i] << endl;
  //    }
  //    d_cycle_check.debugPrint();
  //    Assert( false );
  //  }
  //}
  Debug("datatypes-debug") << "Done cycles" << endl;

  //merge equivalence classes
  initializeEqClass( b );
  EqListN* eqc_b = (*d_equivalence_class.find( b )).second;
  EqListsN::iterator eqc_a_i = d_equivalence_class.find( a );
  if( eqc_a_i!=d_equivalence_class.end() ){
    EqListN* eqc_a = (*eqc_a_i).second;
    for( EqListN::const_iterator i = eqc_a->begin(); i != eqc_a->end(); i++ ) {
      eqc_b->push_back( *i );
    }
  }else{
    eqc_b->push_back( a );
  }
  //merge selector lists
  EqListsN::iterator sel_a_i = d_selector_eq.find( a );
  if( sel_a_i != d_selector_eq.end() ) {
    EqListsN::iterator sel_b_i = d_selector_eq.find( b );
    EqListN* sel_b;
    if( sel_b_i == d_selector_eq.end() ) {
      sel_b = new(getSatContext()->getCMM()) EqListN(true, getSatContext(), false,
                                          ContextMemoryAllocator<Node>(getSatContext()->getCMM()));
      d_selector_eq.insertDataFromContextMemory(b, sel_b);
    } else {
      sel_b = (*sel_b_i).second;
    }
    EqListN* sel_a = (*sel_a_i).second;
    for( EqListN::const_iterator i = sel_a->begin(); i != sel_a->end(); i++ ) {
      sel_b->push_back( *i );
    }
    if( !sel_a->empty() ){
      d_checkMap[ b ] = true;
    }
  }

  deq_ia = d_disequalities.find(a);
  map<TNode, TNode> alreadyDiseqs;
  if(deq_ia != d_disequalities.end()) {
     //Collecting the disequalities of b, no need to check for conflicts
     //since the representative of b does not change and we check all the things
     //in a's class when we look at the diseq list of find(a)
    EqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      EqList* deq = (*deq_ib).second;
      for(EqList::const_iterator j = deq->begin(); j != deq->end(); j++) {
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

     //Looking for conflicts in the a disequality list. Note
     //that at this point a and b are already merged. Also has
     //the side effect that it adds them to the list of b (which
     //became the canonical representative)
    EqList* deqa = (*deq_ia).second;
    for(EqList::const_iterator i = deqa->begin(); i != deqa->end(); i++) {
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];

      TNode sp = find(s);
      TNode tp = find(t);
      if(sp == tp) {
        Debug("datatypes") << "Construct standard conflict " << deqn << " " << sp << endl;
        d_em.addNode( deqn, &d_cce );
        d_em.addNodeConflict( NodeManager::currentNM()->mkNode( kind::AND, deqn, deqn.notNode() ), Reason::contradiction );
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

  //merge labels
  EqLists::iterator lbl_i = d_labels.find( a );
  if(lbl_i != d_labels.end()) {
    EqList* lbl = (*lbl_i).second;
    for( EqList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      addTester( *i );
      if( hasConflict() ) {
        return;
      }
    }
  }
  Debug("datatypes-debug") << "Done merge labels" << endl;

  //do unification
  if( a.getKind() == APPLY_CONSTRUCTOR && b.getKind() == APPLY_CONSTRUCTOR &&
      a.getOperator() == b.getOperator() ) {
    Debug("datatypes") << "Unification: " << a << " and " << b << "." << endl;
    for( int i=0; i<(int)a.getNumChildren(); i++ ) {
      if( find( a[i] ) != find( b[i] ) ) {
        Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, a, b );
        Node newEq = NodeManager::currentNM()->mkNode( EQUAL, a[i], b[i] );
        d_em.addNode( ccEq, &d_cce );
        d_em.addNode( newEq, ccEq, Reason::idt_unify );
        addEquality( newEq );
        if( hasConflict() ) {
          return;
        }
      }
    }
  }

  Debug("datatypes-debug") << "merge(): Done" << endl;
}

void TheoryDatatypes::addTermToLabels( Node t ) {
  if( t.getType().isDatatype() ) {
    Debug("datatypes-debug") << "Add term to labels " << t << std::endl;
    Node tmp = find( t );
    if( tmp == t ) {
      //add to labels
      EqLists::iterator lbl_i = d_labels.find(t);
      if(lbl_i == d_labels.end()) {
        EqList* lbl = new(getSatContext()->getCMM()) EqList(true, getSatContext(), false,
                                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()));
        //if there is only one constructor, then it must be
        const Datatype& dt = ((DatatypeType)(t.getType()).toType()).getDatatype();
        if( dt.getNumConstructors()==1 ){
          Node tester = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[0].getTester() ), t );
          lbl->push_back( tester );
          d_checkMap[ t ] = true;
          d_em.addNodeAxiom( tester, Reason::idt_texhaust );
        }
        d_labels.insertDataFromContextMemory(tmp, lbl);
      }
    }
  }
}

void TheoryDatatypes::initializeEqClass( Node t ) {
  EqListsN::iterator eqc_i = d_equivalence_class.find( t );
  if( eqc_i == d_equivalence_class.end() ) {
    EqListN* eqc = new(getSatContext()->getCMM()) EqListN(true, getSatContext(), false,
                                          ContextMemoryAllocator<Node>(getSatContext()->getCMM()));
    eqc->push_back( t );
    d_equivalence_class.insertDataFromContextMemory(t, eqc);
  }
}

void TheoryDatatypes::collectTerms( Node n, bool recurse ) {
  if( recurse ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      collectTerms( n[i] );
    }
  }
  if( n.getKind() == APPLY_CONSTRUCTOR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      Debug("datatypes-cycles") << "Subterm " << n << " -> " << n[i] << endl;
      bool result CVC4_UNUSED = d_cycle_check.addEdgeNode( n, n[i] );
      Assert( !result );    //this should not create any new cycles (relevant terms should have been recorded before)
    }
  }else{
    if( n.getKind() == APPLY_SELECTOR && d_selectors.find( n ) == d_selectors.end() ) {
      Debug("datatypes") << "  Found selector " << n << endl;
      d_selectors[ n ] = false;
      d_cc.addTerm( n );
      Node tmp = find( n[0] );
      d_checkMap[ tmp ] = true;

      //add selector to selector eq list
      Debug("datatypes") << "  Add selector to list " << tmp << " " << n << endl;
      EqListsN::iterator sel_i = d_selector_eq.find( tmp );
      EqListN* sel;
      if( sel_i == d_selector_eq.end() ) {
        sel = new(getSatContext()->getCMM()) EqListN(true, getSatContext(), false,
                                          ContextMemoryAllocator<Node>(getSatContext()->getCMM()));
        d_selector_eq.insertDataFromContextMemory(tmp, sel);
      } else {
        sel = (*sel_i).second;
      }
      sel->push_back( n );
    }
    addTermToLabels( n );
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
    deq = new(getSatContext()->getCMM()) EqList(true, getSatContext(), false,
                                             ContextMemoryAllocator<TNode>(getSatContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  //if(Debug.isOn("uf")) {
  //  Debug("uf") << "  size is now " << deq->size() << endl;
  //}
}

void TheoryDatatypes::addEquality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  if( !hasConflict() && find( eq[0] ) != find( eq[1] ) ) {
    Debug("datatypes") << "Add equality " << eq << "." << endl;
    Debug("datatypes-debug-pf") << "Add equality " << eq << "." << endl;
#if 1    //for delayed merging
    //setup merge pending list
    d_merge_pending.push_back( vector< pair< Node, Node > >() );

    d_cce.assertTrue(eq);
    d_cc.addTerm(eq[0]);
    d_cc.addTerm(eq[1]);

    //record which nodes are waiting to be merged
    vector< pair< Node, Node > > mp;
    mp.insert( mp.begin(),
               d_merge_pending[d_merge_pending.size()-1].begin(),
               d_merge_pending[d_merge_pending.size()-1].end() );
    d_merge_pending.pop_back();

    //merge original nodes
    if( !hasConflict() ) {
      merge( eq[0], eq[1] );
    }else{
      Debug("datatypes-debug-pf") << "Forget merge " << eq << std::endl;
    }
    //merge nodes waiting to be merged
    for( int i=0; i<(int)mp.size(); i++ ) {
      if( !hasConflict() ) {
        merge( mp[i].first, mp[i].second );
      }else{
        Debug("datatypes-debug-pf") << "Forget merge " << mp[i].first << " " << mp[i].second << std::endl;
      }
    }
#elif 0
    Debug("datatypes-ae") << "Add equality " << eq << "." << endl;
    Debug("datatypes-ae") << "   Find is " << find( eq[0] ) << " = " << find( eq[1] ) << std::endl;
    //merge original nodes
    merge( eq[0], eq[1] );
    d_cce.assertTrue(eq);
    d_cc.addTerm(eq[0]);
    d_cc.addTerm(eq[1]);
#else
    Debug("datatypes-ae") << "Add equality " << eq << "." << endl;
    Debug("datatypes-ae") << "   Find is " << find( eq[0] ) << " = " << find( eq[1] ) << std::endl;
    merge( eq[0], eq[1] );
    if( !hasConflict() ){
      d_cce.assertTrue(eq);
      d_cc.addTerm(eq[0]);
      d_cc.addTerm(eq[1]);
    }
#endif
    if( Debug.isOn("datatypes") || Debug.isOn("datatypes-cycles") ){
      d_currEqualities.push_back(eq);
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

void TheoryDatatypes::checkCycles() {
  for( BoolMap::iterator i = d_reps.begin(); i != d_reps.end(); i++ ) {
    if( (*i).second ) {
      map< Node, bool > visited;
      NodeBuilder<> explanation(kind::AND);
      if( searchForCycle( (*i).first, (*i).first, visited, explanation ) ) {
        Node cCycle = explanation.getNumChildren() == 1 ? explanation.getChild( 0 ) : explanation;
        d_em.addNodeConflict( cCycle, Reason::idt_cycle_coarse );
        Debug("datatypes") << "Detected cycle for " << (*i).first << endl;
        Debug("datatypes") << "Conflict is " << cCycle << endl;
        return;
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
bool TheoryDatatypes::searchForCycle( Node n, Node on,
                                      map< Node, bool >& visited,
                                      NodeBuilder<>& explanation ) {
  //Debug("datatypes") << "Search for cycle " << n << " " << on << endl;
  if( n.getKind() == APPLY_CONSTRUCTOR ) {
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      Node nn = find( n[i] );
      if( visited.find( nn ) == visited.end() ) {
        visited[nn] = true;
        if( nn == on || searchForCycle( nn, on, visited, explanation ) ) {
          if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n, n[i] ) ){
            Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << n[i] << "!!!!" << std::endl;
          }
          if( nn != n[i] ) {
            if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n[i], nn ) ){
              Debug("datatypes-cycles") << "Cycle equality: " << n[i] << " is not -> " << nn << "!!!!" << std::endl;
            }
            Node ccEq = NodeManager::currentNM()->mkNode( EQUAL, nn, n[i] );
            d_em.addNode( ccEq, &d_cce );
            explanation << ccEq;
          }
          return true;
        }
      }
    }
  }
  return false;
}

bool TheoryDatatypes::hasTerm( Node a ){
  return false;
}

bool TheoryDatatypes::areEqual( Node a, Node b ){
  Node ar = find( a );
  Node br = find( b );
  if( ar==br ){
    return true;
  }else if( ar.getKind()==APPLY_CONSTRUCTOR && br.getKind()==APPLY_CONSTRUCTOR &&
            ar.getOperator()==br.getOperator() ){
    //for( int i=0; i<(int)ar.getNumChildren(); i++ ){
    //  if( !areEqual( ar[0], br[0] ) ){
    //    return false;
    //  }
    //}
    //return true;
    return false;
  }else{
    return false;
  }
}

bool TheoryDatatypes::areDisequal( Node a, Node b ){
  Node ar = find( a );
  Node br = find( b );
  if( ar==br ){
    return false;
  }else if( ar.getKind()==APPLY_CONSTRUCTOR && br.getKind()==APPLY_CONSTRUCTOR &&
            ar.getOperator()!=br.getOperator() ){
    return true;
  }else{
    EqLists::iterator deq_ia = d_disequalities.find( ar );
    EqLists::iterator deq_ib = d_disequalities.find( br );
    if( deq_ia!=d_disequalities.end() && deq_ib!=d_disequalities.end() ){
      EqList* deq;
      if( (*deq_ib).second->size()<(*deq_ia).second->size() ){
        deq = (*deq_ib).second;
      }else{
        deq = (*deq_ia).second;
      }
      for(EqList::const_iterator i = deq->begin(); i != deq->end(); i++) {
        TNode deqn = (*i);
        TNode sp = find(deqn[0]);
        TNode tp = find(deqn[1]);
        if( sp==a && tp==b ){
          return true;
        }else if( sp==b && tp==a ){
          return true;
        }
      }
    }
    return false;
  }
}

Node TheoryDatatypes::getRepresentative( Node a ){
  return find( a );
}

*/
#endif