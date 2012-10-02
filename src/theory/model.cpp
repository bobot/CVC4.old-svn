/*********************                                                        */
/*! \file model.cpp
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
 ** \brief Implementation of model class
 **/

#include "theory/model.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/type_enumerator.h"
#include "smt/model_format_mode.h"
#include "smt/options.h"
#include "theory/uf/theory_uf_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

TheoryModel::TheoryModel( context::Context* c, std::string name, bool enableFuncModels ) :
  d_substitutions(c), d_equalityEngine(c, name), d_enableFuncModels(enableFuncModels)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
  d_equalityEngine.addFunctionKind(kind::SELECT);
  d_equalityEngine.addFunctionKind(kind::STORE);
  d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
}

void TheoryModel::reset(){
  d_reps.clear();
  d_rep_set.clear();
  d_uf_terms.clear();
  d_uf_models.clear();
}

Node TheoryModel::getValue( TNode n ){
  //apply substitutions
  Node nn = d_substitutions.apply( n );
  //get value in model
  return getModelValue( nn );
}

Expr TheoryModel::getValue( Expr expr ){
  Node n = Node::fromExpr( expr );
  Node ret = getValue( n );
  return ret.toExpr();
}

/** get cardinality for sort */
Cardinality TheoryModel::getCardinality( Type t ){
  TypeNode tn = TypeNode::fromType( t );
  //for now, we only handle cardinalities for uninterpreted sorts
  if( tn.isSort() ){
    if( d_rep_set.hasType( tn ) ){
      return Cardinality( d_rep_set.d_type_reps[tn].size() );
    }else{
      return Cardinality( CardinalityUnknown() );
    }
  }else{
    return Cardinality( CardinalityUnknown() );
  }
}

void TheoryModel::toStream( std::ostream& out )
{
  out << this;
}

Node TheoryModel::getModelValue( TNode n )
{
  if( n.isConst() ) {
    return n;
  }

  TypeNode t = n.getType();
  if (t.isFunction() || t.isPredicate()) {
    if (d_enableFuncModels) {
      if (d_uf_models.find(n) != d_uf_models.end()) {
        // Existing function
        return d_uf_models[n];
      }
      // Unknown function symbol: return LAMBDA x. c, where c is the first constant in the enumeration of the range type
      vector<TypeNode> argTypes = t.getArgTypes();
      vector<Node> args;
      NodeManager* nm = NodeManager::currentNM();
      for (unsigned i = 0; i < argTypes.size(); ++i) {
        args.push_back(nm->mkBoundVar(argTypes[i]));
      }
      Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, args);
      TypeEnumerator te(t.getRangeType());
      return nm->mkNode(kind::LAMBDA, boundVarList, *te);
    }
    // TODO: if func models not enabled, throw an error?
    Unreachable();
  }

  if (n.getNumChildren() > 0) {
    std::vector<Node> children;
    if (n.getKind() == APPLY_UF) {
      Node op = n.getOperator();
      if (d_uf_models.find(op) == d_uf_models.end()) {
        // Unknown term - return first enumerated value for this type
        TypeEnumerator te(n.getType());
        return *te;
      }
      // Plug in uninterpreted function model
      children.push_back(d_uf_models[op]);
    }
    else if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back(n.getOperator());
    }
    //evaluate the children
    for (unsigned i = 0; i < n.getNumChildren(); ++i) {
      Node val = getValue(n[i]);
      children.push_back(val);
    }
    Node val = Rewriter::rewrite(NodeManager::currentNM()->mkNode(n.getKind(), children));
    Assert(val.isConst());
    return val;
  }

  if (!d_equalityEngine.hasTerm(n)) {
    // Unknown term - return first enumerated value for this type
    TypeEnumerator te(n.getType());
    return *te;
  }
  Node val = d_equalityEngine.getRepresentative(n);
  Assert(d_reps.find(val) != d_reps.end());
  val = d_reps[val];
  Assert(val.isConst());
  return val;
}


Node TheoryModel::getInterpretedValue( TNode n ){
  Trace("model") << "Get interpreted value of " << n << std::endl;
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    //for function models
    if( d_enableFuncModels ){
      if( d_uf_models.find( n )!=d_uf_models.end() ){
        //pre-existing function model
        Trace("model") << "Return function value." << std::endl;
        return d_uf_models[n];
      }else{
        Trace("model") << "Return arbitrary function value." << std::endl;
        //otherwise, choose the constant default value
        uf::UfModelTree ufmt( n );
        Node default_v = getInterpretedValue( NodeManager::currentNM()->mkSkolem( "defaultValueQueryVar_$$", type.getRangeType(),
                                              "a placeholder variable to query for a default value in model construction" ) );
        ufmt.setDefaultValue( this, default_v );
        return ufmt.getFunctionValue( "$x" );
      }
    }else{
      return n;
    }
  }else{
    Trace("model-debug") << "check rep..." << std::endl;
    Node ret;
    //check if the representative is defined
    n = d_equalityEngine.hasTerm( n ) ? d_equalityEngine.getRepresentative( n ) : n;
    Trace("model-debug") << "rep is..." << n << std::endl;
    if( d_reps.find( n )!=d_reps.end() ){
      Trace("model") << "Return value in equality engine."<< std::endl;
      return d_reps[n];
    }
    Trace("model-debug") << "check apply uf models..." << std::endl;
    //if it is APPLY_UF, we must consult the corresponding function if it exists
    if( n.getKind()==APPLY_UF ){
      Node op = n.getOperator();
      if( d_uf_models.find( op )!=d_uf_models.end() ){
        std::vector< Node > lam_children;
        lam_children.push_back( d_uf_models[ op ] );
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          lam_children.push_back( n[i] );
        }
        Node app_lam = NodeManager::currentNM()->mkNode( APPLY_UF, lam_children );
        ret = Rewriter::rewrite( app_lam );
        Trace("model") << "Consult UF model." << std::endl;
      }
    }
    Trace("model-debug") << "check existing..." << std::endl;
    if( ret.isNull() ){
      //second, try to choose an existing term as value
      std::vector< Node > v_emp;
      ret = getDomainValue( type, v_emp );
      if( !ret.isNull() ){
        Trace("model") << "Choose existing value." << std::endl;
      }
    }
    Trace("model-debug") << "check new..." << std::endl;
    if( ret.isNull() ){
      //otherwise, choose new value
      ret = getNewDomainValue( type );
      if( !ret.isNull() ){
        Trace("model") << "Choose new value." << std::endl;
      }
    }
    if( !ret.isNull() ){
      return ret;
    }else{
      //otherwise, just return itself (this usually should not happen)
      Trace("model") << "Return self." << std::endl;
      return n;
    }
  }
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_rep_set.d_type_reps[tn][i] )==exclude.end() ){
        return d_rep_set.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

//FIXME: need to ensure that theory enumerators exist for each sort
Node TheoryModel::getNewDomainValue( TypeNode tn ){
  if( tn.isSort() ){
    return Node::null();
  }else{
    TypeEnumerator te(tn);
    while( !te.isFinished() ){
      Node r = *te;
      if(Debug.isOn("getNewDomainValue")) {
        Debug("getNewDomainValue") << "getNewDomainValue( " << tn << ")" << endl;
        Debug("getNewDomainValue") << "+ TypeEnumerator gave: " << r << endl;
        Debug("getNewDomainValue") << "+ d_type_reps are:";
        for(vector<Node>::const_iterator i = d_rep_set.d_type_reps[tn].begin();
            i != d_rep_set.d_type_reps[tn].end();
            ++i) {
          Debug("getNewDomainValue") << " " << *i;
        }
        Debug("getNewDomainValue") << endl;
      }
      if( std::find(d_rep_set.d_type_reps[tn].begin(), d_rep_set.d_type_reps[tn].end(), r) ==d_rep_set.d_type_reps[tn].end() ) {
        Debug("getNewDomainValue") << "+ it's new, so returning " << r << endl;
        return r;
      }
      ++te;
    }
    return Node::null();
  }
}

/** add substitution */
void TheoryModel::addSubstitution( TNode x, TNode t, bool invalidateCache ){
  if( !d_substitutions.hasSubstitution( x ) ){
    d_substitutions.addSubstitution( x, t, invalidateCache );
  }
}

/** add term */
void TheoryModel::addTerm( Node n ){
  if( !d_equalityEngine.hasTerm( n ) ){
    d_equalityEngine.addTerm( n );
  }
  //must collect UF terms
  if (n.getKind()==APPLY_UF) {
    Node op = n.getOperator();
    if( std::find( d_uf_terms[ op ].begin(), d_uf_terms[ op ].end(), n )==d_uf_terms[ op ].end() ){
      d_uf_terms[ op ].push_back( n );
      Trace("model-add-term-uf") << "Add term " << n << std::endl;
    }
  }
}

/** assert equality */
void TheoryModel::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void TheoryModel::assertPredicate( Node a, bool polarity ){
  if( a.getKind()==EQUAL ){
    d_equalityEngine.assertEquality( a, polarity, Node::null() );
  }else{
    d_equalityEngine.assertPredicate( a, polarity, Node::null() );
  }
}

/** assert equality engine */
void TheoryModel::assertEqualityEngine( const eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType().isBoolean() ){
      predicate = true;
      predPolarity = ee->areEqual( eqc, d_true );
      //FIXME: do we guarentee that all boolean equivalence classes contain either d_true or d_false?
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
    while( !eqc_i.isFinished() ){
      if( predicate ){
        assertPredicate( *eqc_i, predPolarity );
      }else{
        assertEquality( *eqc_i, eqc, true );
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

void TheoryModel::assertRepresentative( Node n ){
  Trace("model-builder-reps") << "Assert rep : " << n << std::endl;
  d_reps[ n ] = n;
}

bool TheoryModel::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node TheoryModel::getRepresentative( Node a ){
  if( d_equalityEngine.hasTerm( a ) ){
    Node r = d_equalityEngine.getRepresentative( a );
    if( d_reps.find( r )!=d_reps.end() ){
      return d_reps[ r ];
    }else{
      return r;
    }
  }else{
    return a;
  }
}

bool TheoryModel::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal( Node a, Node b ){
  if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << getRepresentative( r );
  }
}

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){

}

void TheoryEngineModelBuilder::buildModel(Model* m, bool fullModel)
{
  TheoryModel* tm = (TheoryModel*)m;

  // Reset model
  tm->reset();

  // Collect model info from the theories
  Trace("model-builder") << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  d_te->collectModelInfo(tm, fullModel);
  Trace("model-builder") << "Collect representatives..." << std::endl;

  // Process all terms in the equality engine, store representatives for each EC
  std::map< Node, Node > assertedReps, constantReps;
  TypeSet typeConstSet, typeRepSet, typeNoRepSet;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  for ( ; !eqcs_i.isFinished(); ++eqcs_i) {

    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Trace("model-builder") << "Processing EC: " << eqc << endl;
    Assert(tm->d_equalityEngine.getRepresentative(eqc) == eqc);
    TypeNode eqct = eqc.getType();
    Assert(assertedReps.find(eqc) == assertedReps.end());
    Assert(constantReps.find(eqc) == constantReps.end());

    // Loop through terms in this EC
    Node rep, const_rep;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &tm->d_equalityEngine);
    for ( ; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      Trace("model-builder") << "  Processing Term: " << n << endl;
      // Record as rep if this node was specified as a representative
      if (tm->d_reps.find(n) != tm->d_reps.end()){
        Assert(rep.isNull());
        rep = tm->d_reps[n];
        Assert(!rep.isNull() );
        Trace("model-builder") << "  Rep( " << eqc << " ) = " << rep << std::endl;
      }
      // Record as const_rep if this node is constant
      if (n.isConst()) {
        Assert(const_rep.isNull());
        const_rep = n;
        Trace("model-builder") << "  ConstRep( " << eqc << " ) = " << const_rep << std::endl;
      }
      //model-specific processing of the term
      tm->addTerm(n);
    }

    // Assign representative for this EC
    if (!const_rep.isNull()) {
      // Theories should not specify a rep if there is already a constant in the EC
      Assert(rep.isNull());
      constantReps[eqc] = const_rep;
      typeConstSet.add(eqct, const_rep);
    }
    else if (!rep.isNull()) {
      assertedReps[eqc] = rep;
      typeRepSet.add(eqct, eqc);
    }
    else {
      typeNoRepSet.add(eqct, eqc);
    }
  }

  // Need to ensure that each EC has a constant representative.

  // Phase 1: For types that do not have asserted reps, assign the unassigned EC's using either evaluation or type enumeration
  Trace("model-builder") << "Starting phase 1..." << std::endl;
  TypeSet::iterator it;
  for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it) {
    set<Node>& noRepSet = TypeSet::getSet(it);
    Assert(!noRepSet.empty());
    // This assertion may be too strong, but hopefully not: we expect that for every type, either all of its EC's have asserted reps (or constants)
    // or none of its EC's have asserted reps.
    TypeNode t = TypeSet::getType(it);
    Assert(typeRepSet.getSet(t) == NULL);

    set<Node>::iterator i, i2;
    bool changed;

    // Find value for this EC using evaluation if possible
    do {
      changed = false;
      d_normalizedCache.clear();
      for (i = noRepSet.begin(); i != noRepSet.end(); ) {
        i2 = i;
        ++i;
        eq::EqClassIterator eqc_i = eq::EqClassIterator(*i2, &tm->d_equalityEngine);
        for ( ; !eqc_i.isFinished(); ++eqc_i) {
          Node n = *eqc_i;
          Node normalized = normalize(tm, n, constantReps);
          if (normalized.isConst()) {
            typeConstSet.add(t, normalized);
            constantReps[*i2] = normalized;
            Trace("model-builder") << "  Eval: Setting constant rep of " << (*i2) << " to " << normalized << endl;
            changed = true;
            noRepSet.erase(i2);
            break;
          }
        }
      }
    } while (changed);

    if (noRepSet.empty()) {
      continue;
    }

    set<Node>* constSet = typeConstSet.getSet(t);
    TypeEnumerator te(t);
    for (i = noRepSet.begin(); i != noRepSet.end(); ++i) {
      Assert(!te.isFinished());
      if (constSet != NULL) {
        while (constSet->find(*te) != constSet->end()) {
          ++te;
          Assert(!te.isFinished());
        }
        constSet->insert(*te);
      }
      else {
        typeConstSet.add(t, *te);
        constSet = typeConstSet.getSet(t);
      }
      constantReps[*i] = *te;
      Trace("model-builder") << "  New Const: Setting constant rep of " << (*i) << " to " << *te << endl;
      ++te;
    }
  }

  // Phase 2: Substitute into asserted reps using constReps.
  // Iterate until a fixed point is reached.
  Trace("model-builder") << "Starting phase 2..." << std::endl;
  bool changed;
  do {
    changed = false;
    d_normalizedCache.clear();
    for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it) {
      set<Node>& repSet = TypeSet::getSet(it);
      set<Node>::iterator i;
      for (i = repSet.begin(); i != repSet.end(); ) {
        Assert(assertedReps.find(*i) != assertedReps.end());
        Node rep = assertedReps[*i];
        Node normalized = normalize(tm, rep, constantReps);
        if (normalized.isConst()) {
          changed = true;
          constantReps[*i] = normalized;
          set<Node>::iterator i2 = i;
          ++i;
          repSet.erase(i2);
        }
        else {
          ++i;
        }
      }
    }
  } while (changed);

  // Assert that all representatives have been converted to constants
  for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it) {
    set<Node>& repSet = TypeSet::getSet(it);
    Assert(repSet.empty());
  }

  Trace("model-builder") << "Copy representatives to model..." << std::endl;
  //constantReps has the actual representatives we will use, now copy to model
  tm->d_reps.clear();
  for( std::map< Node, Node >::iterator it = constantReps.begin(); it != constantReps.end(); ++it ){
    tm->d_reps[ it->first ] = it->second;
    tm->d_rep_set.add( it->second );
  }

  //modelBuilder-specific initialization
  processBuildModel( tm, fullModel );

  // Check that every term evaluates to its representative in the model
  for (eqcs_i = eq::EqClassesIterator(&tm->d_equalityEngine); !eqcs_i.isFinished(); ++eqcs_i) {
    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Assert(constantReps.find(eqc) != constantReps.end());
    Node rep = constantReps[eqc];
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &tm->d_equalityEngine);
    for ( ; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      Assert(tm->getValue(*eqc_i) == rep);
    }
  }

}


Node TheoryEngineModelBuilder::normalize(TheoryModel* m, TNode r, std::map< Node, Node >& constantReps)
{
  std::map<Node, Node>::iterator itMap = constantReps.find(r);
  if (itMap != constantReps.end()) {
    return (*itMap).second;
  }
  NodeMap::iterator it = d_normalizedCache.find(r);
  if (it != d_normalizedCache.end()) {
    return (*it).second;
  }
  Node retNode = r;
  if (r.getNumChildren() > 0) {
    std::vector<Node> children;
    if (r.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back(r.getOperator());
    }
    bool childrenConst = true;
    for (size_t i=0; i < r.getNumChildren(); ++i) {
      Node ri = r[i];
      if (!ri.isConst()) {
        if (m->d_equalityEngine.hasTerm(ri)) {
          ri = m->d_equalityEngine.getRepresentative(ri);
        }
        ri = normalize(m, ri, constantReps);
        if (!ri.isConst()) {
          childrenConst = false;
        }
      }
      children.push_back(ri);
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind(), children );
    if (childrenConst) {
      retNode = Rewriter::rewrite(retNode);
    }
  }
  d_normalizedCache[r] = retNode;
  return retNode;
}


void TheoryEngineModelBuilder::processBuildModel(TheoryModel* m, bool fullModel)
{
  if (fullModel) {
    Trace("model-builder") << "Assigning function values..." << endl;
    //construct function values
    for( std::map< Node, std::vector< Node > >::iterator it = m->d_uf_terms.begin(); it != m->d_uf_terms.end(); ++it ){
      Node n = it->first;
      if( m->d_uf_models.find( n )==m->d_uf_models.end() ){
        TypeNode type = n.getType();
        uf::UfModelTree ufmt( n );
        Node default_v, un, simp, v;
        for( size_t i=0; i<it->second.size(); i++ ){
          un = it->second[i];
          vector<TNode> children;
          children.push_back(n);
          for (size_t j = 0; j < un.getNumChildren(); ++j) {
            children.push_back(m->getRepresentative(un[j]));
          }
          simp = NodeManager::currentNM()->mkNode(un.getKind(), children);
          v = m->getRepresentative(un);
          Trace("model-builder") << "  Setting (" << simp << ") to (" << v << ")" << endl;
          ufmt.setValue(m, simp, v);
          default_v = v;
        }
        if( default_v.isNull() ){
          //choose default value from model if none exists
          TypeEnumerator te(type.getRangeType());
          default_v = (*te);
        }
        ufmt.setDefaultValue( m, default_v );
        ufmt.simplify();
        Node val = ufmt.getFunctionValue( "$x" );
        Trace("model-builder") << "  Assigning (" << n << ") to (" << val << ")" << endl;
        m->d_uf_models[n] = val;
      }
    }
  }
}


Node TheoryEngineModelBuilder::chooseRepresentative( TheoryModel* m, Node eqc, bool fullModel ){
  //try to get a new domain value
  Node rep = m->getNewDomainValue( eqc.getType() );
  if( !rep.isNull() ){
    return rep;
  }else{
    //if we can't get new domain value, just return eqc itself (this typically should not happen)
    //FIXME: Assertion failure here?
    return eqc;
  }
}
