/*********************                                                        */
/*! \file inst_match.cpp
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
 ** \brief Implementation of inst match class
 **/

#include "theory/inst_match.h"
#include "theory/rr_inst_match.h"
#include "theory/rr_trigger.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rrinst;
using namespace CVC4::theory::uf::rrinst;

namespace CVC4{
namespace theory{
namespace rrinst{

typedef CVC4::theory::inst::InstMatch InstMatch;
typedef CVC4::theory::inst::CandidateGeneratorQueue CandidateGeneratorQueue;

/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio ){
  //std::cout << "Add " << index << " " << f[0].getNumChildren() << std::endl;
  if( index<(int)f[0].getNumChildren() && ( !imtio || index<(int)imtio->d_order.size() ) ){
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.d_map[ qe->getInstantiationConstant( f, i_index ) ];
    d_data[n].addInstMatch2( qe, f, m, index+1, imtio );
  }
}

/** exists match */
bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index, ImtIndexOrder* imtio ){
  //std::cout << "Exists " << index << " " << f[0].getNumChildren() << std::endl;
  if( index==(int)f[0].getNumChildren() || ( imtio && index==(int)imtio->d_order.size() ) ){
    return true;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.d_map[ qe->getInstantiationConstant( f, i_index ) ];
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
        return true;
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine()->hasTerm( n ) ){
        eq::EqClassIterator eqc = eq::EqClassIterator( qe->getEqualityQuery()->getRepresentative( n ),
                                ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, InstMatchTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
      //for( std::map< Node, InstMatchTrie >::iterator itc = d_data.begin(); itc != d_data.end(); ++itc ){
      //  if( itc->first!=n && qe->getEqualityQuery()->areEqual( n, itc->first ) ){
      //    if( itc->second.existsInstMatch( qe, f, m, modEq, index+1 ) ){
      //      return true;
      //    }
      //  }
      //}
    }
    return false;
  }
}

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, ImtIndexOrder* imtio ){
  if( !existsInstMatch( qe, f, m, modEq, 0, imtio ) ){
    //std::cout << "~Exists, add." << std::endl;
    addInstMatch2( qe, f, m, 0, imtio );
    return true;
  }else{
    //std::cout << "Exists, fail." << std::endl;
    return false;
  }
}

// InstMatchGenerator::InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
//   initializePattern( pat, qe );
// }

// InstMatchGenerator::InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
//   if( pats.size()==1 ){
//     initializePattern( pats[0], qe );
//   }else{
//     initializePatterns( pats, qe );
//   }
// }

// void InstMatchGenerator::setMatchFail( QuantifiersEngine* qe, Node n1, Node n2 ){
//   if( std::find( d_match_fails[n1][n2].begin(), d_match_fails[n1][n2].end(), this )==d_match_fails[n1][n2].end() ){
//     if( !qe->getEqualityQuery()->areDisequal( n1, n2 ) ){
//       d_match_fails[n1][n2].push_back( this );
//       d_match_fails[n2][n1].push_back( this );
//     }
//   }
// }

// void InstMatchGenerator::initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe ){
//   int childMatchPolicy = d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ? 0 : d_matchPolicy;
//   for( int i=0; i<(int)pats.size(); i++ ){
//     d_children.push_back( new InstMatchGenerator( pats[i], qe, childMatchPolicy ) );
//   }
//   if (d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH)
//     for( int i=0; i<(int)pats.size(); i++ ){
//       d_children_multi_efficient.push_back(
//           new InstMatchGenerator( pats[i], qe,MATCH_GEN_EFFICIENT_E_MATCH ) );
//     }
//   d_pattern = Node::null();
//   d_match_pattern = Node::null();
//   d_cg = NULL;
// }

// void InstMatchGenerator::initializePattern( Node pat, QuantifiersEngine* qe ){
//   Debug("inst-match-gen") << "Pattern term is " << pat << std::endl;
//   Assert( pat.hasAttribute(InstConstantAttribute()) );
//   d_pattern = pat;
//   d_match_pattern = pat;
//   if( d_match_pattern.getKind()==NOT ){
//     //we want to add the children of the NOT
//     d_match_pattern = d_pattern[0];
//   }
//   if( d_match_pattern.getKind()==IFF || d_match_pattern.getKind()==EQUAL ){
//     if( !d_match_pattern[0].hasAttribute(InstConstantAttribute()) ){
//       Assert( d_match_pattern[1].hasAttribute(InstConstantAttribute()) );
//       //swap sides
//       d_pattern = NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), d_match_pattern[1], d_match_pattern[0] );
//       d_pattern = pat.getKind()==NOT ? d_pattern.notNode() : d_pattern;
//       if( pat.getKind()!=NOT ){   //TEMPORARY until we do better implementation of disequality matching
//         d_match_pattern = d_match_pattern[1];
//       }else{
//         d_match_pattern = d_pattern[0][0];
//       }
//     }else if( !d_match_pattern[1].hasAttribute(InstConstantAttribute()) ){
//       Assert( d_match_pattern[0].hasAttribute(InstConstantAttribute()) );
//       if( pat.getKind()!=NOT ){   //TEMPORARY until we do better implementation of disequality matching
//         d_match_pattern = d_match_pattern[0];
//       }
//     }
//   }
//   int childMatchPolicy = MATCH_GEN_DEFAULT;
//   for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
//     if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
//       if( d_match_pattern[i].getKind()!=INST_CONSTANT ){
//         d_children.push_back( new InstMatchGenerator( d_match_pattern[i], qe, childMatchPolicy ) );
//         d_children_index.push_back( i );
//       }
//     }
//   }

//   Debug("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is " << d_match_pattern << std::endl;

//   //get the equality engine
//   Theory* th_uf = qe->getTheoryEngine()->getTheory( theory::THEORY_UF );
//   uf::InstantiatorTheoryUf* ith = (uf::InstantiatorTheoryUf*)th_uf->getInstantiator();
//   //create candidate generator
//   if( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
//     Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
//     //we will be producing candidates via literal matching heuristics
//     if( d_pattern.getKind()!=NOT ){
//       //candidates will be all equalities
//       d_cg = new uf::CandidateGeneratorTheoryUfLitEq( ith, d_match_pattern );
//     }else{
//       //candidates will be all disequalities
//       d_cg = new uf::CandidateGeneratorTheoryUfLitDeq( ith, d_match_pattern );
//     }
//   }else if( d_pattern.getKind()==EQUAL || d_pattern.getKind()==IFF || d_pattern.getKind()==NOT ){
//     Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
//     if( d_pattern.getKind()==NOT ){
//       std::cout << "Disequal generator unimplemented" << std::endl;  //DO_THIS
//       exit( 34 );
//       //Node op = d_match_pattern.getKind()==APPLY_UF ? d_match_pattern.getOperator() : Node::null();
//       ////we are matching for a term, but want to be disequal from a particular equivalence class
//       //d_cg = new uf::CandidateGeneratorTheoryUfDisequal( ith, op );
//       ////store the equivalence class that we will call d_cg->reset( ... ) on
//       //d_eq_class = d_pattern[0][1];
//     }else{
//       Assert( Trigger::isAtomicTrigger( d_match_pattern ) );
//       //we are matching only in a particular equivalence class
//       d_cg = new uf::CandidateGeneratorTheoryUf( ith, d_match_pattern.getOperator() );
//       //store the equivalence class that we will call d_cg->reset( ... ) on
//       d_eq_class = d_pattern[1];
//     }
//   }else if( Trigger::isAtomicTrigger( d_match_pattern ) ){
//     if( d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ){
//       //we will manually add candidates to queue
//       d_cg = new CandidateGeneratorQueue;
//       //register this candidate generator
//       ith->registerCandidateGenerator( d_cg, d_match_pattern );
//     }else{
//       //we will be scanning lists trying to find d_match_pattern.getOperator()
//       d_cg = new uf::CandidateGeneratorTheoryUf( ith, d_match_pattern.getOperator() );
//     }
//   }else{
//     d_cg = new CandidateGeneratorQueue;
//     if( !Trigger::getPatternArithmetic( d_match_pattern.getAttribute(InstConstantAttribute()), d_match_pattern, d_arith_coeffs ) ){
//       Debug("inst-match-gen") << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
//       std::cout << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
//       d_matchPolicy = MATCH_GEN_INTERNAL_ERROR;
//     }else{
//       Debug("matching-arith") << "Generated arithmetic pattern for " << d_match_pattern << ": " << std::endl;
//       for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
//         Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
//       }
//       //we will treat this as match gen internal arithmetic
//       d_matchPolicy = MATCH_GEN_INTERNAL_ARITHMETIC;
//     }
//   }
// }

// /** get match (not modulo equality) */
// bool InstMatchGenerator::getMatch( Node t, InstMatch& m, QuantifiersEngine* qe ){
//   Debug("matching") << "Matching " << t << " against pattern " << d_match_pattern << " ("
//                     << m.d_map.size() << ")" << ", " << d_children.size() << std::endl;
//   Assert( !d_match_pattern.isNull() );
//   if( d_matchPolicy==MATCH_GEN_INTERNAL_ARITHMETIC ){
//     return getMatchArithmetic( t, m, qe );
//   }else if( d_matchPolicy==MATCH_GEN_INTERNAL_ERROR ){
//     return false;
//   }else{
//     EqualityQuery* q = qe->getEqualityQuery();
//     //add m to partial match vector
//     std::vector< InstMatch > partial;
//     partial.push_back( InstMatch( &m ) );
//     //if t is null
//     Assert( !t.isNull() );
//     Assert( !t.hasAttribute(InstConstantAttribute()) );
//     Assert( t.getKind()==d_match_pattern.getKind() );
//     Assert( !Trigger::isAtomicTrigger( d_match_pattern ) || t.getOperator()==d_match_pattern.getOperator() );
//     //first, check if ground arguments are not equal, or a match is in conflict
//     for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
//       if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
//         if( d_match_pattern[i].getKind()==INST_CONSTANT ){
//           if( !partial[0].setMatch( q, d_match_pattern[i], t[i] ) ){
//             //match is in conflict
//             Debug("matching-debug") << "Match in conflict " << t[i] << " and "
//                                     << d_match_pattern[i] << " because "
//                                     << partial[0].d_map[d_match_pattern[i]]
//                                     << std::endl;
//             Debug("matching-fail") << "Match fail: " << partial[0].d_map[d_match_pattern[i]] << " and " << t[i] << std::endl;
//             //setMatchFail( qe, partial[0].d_map[d_match_pattern[i]], t[i] );
//             return false;
//           }
//         }
//       }else{
//         if( !q->areEqual( d_match_pattern[i], t[i] ) ){
//           Debug("matching-fail") << "Match fail arg: " << d_match_pattern[i] << " and " << t[i] << std::endl;
//           //setMatchFail( qe, d_match_pattern[i], t[i] );
//           //ground arguments are not equal
//           return false;
//         }
//       }
//     }
//     //now, fit children into match
//     //we will be requesting candidates for matching terms for each child
//     std::vector< Node > reps;
//     for( int i=0; i<(int)d_children.size(); i++ ){
//       Node rep = q->getRepresentative( t[ d_children_index[i] ] );
//       reps.push_back( rep );
//       d_children[i]->d_cg->reset( rep );
//     }

//     //combine child matches
//     int index = 0;
//     while( index>=0 && index<(int)d_children.size() ){
//       partial.push_back( InstMatch( &partial[index] ) );
//       if( d_children[index]->getNextMatch2( partial[index+1], qe ) ){
//         index++;
//       }else{
//         d_children[index]->d_cg->reset( reps[index] );
//         partial.pop_back();
//         if( !partial.empty() ){
//           partial.pop_back();
//         }
//         index--;
//       }
//     }
//     if( index>=0 ){
//       m = partial.back();
//       return true;
//     }else{
//       return false;
//     }
//   }
// }

// bool InstMatchGenerator::getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched ){
//   bool success = false;
//   Node t;
//   do{
//     //get the next candidate term t
//     t = d_cg->getNextCandidate();
//     //if t not null, try to fit it into match m
//     if( !t.isNull() ){
//       success = getMatch( t, m, qe );
//     }
//   }while( !success && !t.isNull() );
//   if (saveMatched) m.d_matched = t;
//   return success;
// }



// bool InstMatchGenerator::getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe ){
//   Debug("matching-arith") << "Matching " << t << " " << d_match_pattern << std::endl;
//   if( !d_arith_coeffs.empty() ){
//     NodeBuilder<> tb(kind::PLUS);
//     Node ic = Node::null();
//     for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
//       Debug("matching-arith") << it->first << " -> " << it->second << std::endl;
//       if( !it->first.isNull() ){
//         if( m.d_map.find( it->first )==m.d_map.end() ){
//           //see if we can choose this to set
//           if( ic.isNull() && ( it->second.isNull() || !it->first.getType().isInteger() ) ){
//             ic = it->first;
//           }
//         }else{
//           Debug("matching-arith") << "already set " << m.d_map[ it->first ] << std::endl;
//           Node tm = m.d_map[ it->first ];
//           if( !it->second.isNull() ){
//             tm = NodeManager::currentNM()->mkNode( MULT, it->second, tm );
//           }
//           tb << tm;
//         }
//       }else{
//         tb << it->second;
//       }
//     }
//     if( !ic.isNull() ){
//       Node tm;
//       if( tb.getNumChildren()==0 ){
//         tm = t;
//       }else{
//         tm = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
//         tm = NodeManager::currentNM()->mkNode( MINUS, t, tm );
//       }
//       if( !d_arith_coeffs[ ic ].isNull() ){
//         Assert( !ic.getType().isInteger() );
//         Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_arith_coeffs[ ic ].getConst<Rational>() );
//         tm = NodeManager::currentNM()->mkNode( MULT, coeff, tm );
//       }
//       m.d_map[ ic ] = Rewriter::rewrite( tm );
//       //set the rest to zeros
//       for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
//         if( !it->first.isNull() ){
//           if( m.d_map.find( it->first )==m.d_map.end() ){
//             m.d_map[ it->first ] = NodeManager::currentNM()->mkConst( Rational(0) );
//           }
//         }
//       }
//       Debug("matching-arith") << "Setting " << ic << " to " << tm << std::endl;
//       return true;
//     }else{
//       return false;
//     }
//   }else{
//     return false;
//   }
// }


// /** reset instantiation round */
// void InstMatchGenerator::resetInstantiationRound( QuantifiersEngine* qe ){
//   if( d_match_pattern.isNull() ){
//     for( int i=0; i<(int)d_children.size(); i++ ){
//       d_children[i]->resetInstantiationRound( qe );
// *    }
//     for( int i=0; i<(int)d_children_multi_efficient.size(); i++ ){
//       d_children_multi_efficient[i]->resetInstantiationRound( qe );
//     }
//     d_children_multi_efficient_index = 0;
//   }else{
//     if( d_cg ){
//       d_cg->resetInstantiationRound();
//     }
//   }
// }

// void InstMatchGenerator::reset( Node eqc, QuantifiersEngine* qe ){
//   if( d_match_pattern.isNull() ){
//     //std::cout << "Reset ";
//     for( int i=0; i<(int)d_children.size(); i++ ){
//       d_children[i]->reset( eqc, qe );
//       //std::cout << d_children[i]->d_match_pattern.getOperator() << ":" << qe->getTermDatabase()->d_op_map[ d_children[i]->d_match_pattern.getOperator() ].size() << " ";
//     }
//     for( int i=0; i<(int)d_children_multi_efficient.size(); i++ ){
//       d_children_multi_efficient[i]->reset( eqc, qe );
//     }
//     d_children_multi_efficient_index = 0;
//     //std::cout << std::endl;
//     d_partial.clear();
//   }else{
//     if( !d_eq_class.isNull() ){
//       //we have a specific equivalence class in mind
//       //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term
//       //just look in equivalence class of the RHS
//       d_cg->reset( d_eq_class );
//     }else{
//       d_cg->reset( eqc );
//     }
//   }
// }

// bool InstMatchGenerator::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
//   m.d_matched = Node::null();
//   if(!d_match_pattern.isNull() ){
//     // Mono-trigger
//     bool res = getNextMatch2( m, qe, true );
//     Assert(!res || !m.d_matched.isNull());
//     return res;
//   }

//   // It's a multi-trigger, d_partial is used as the stack for the search.
//   if( d_partial.empty() ){
//     Debug("inst_match::getNextMatch") << "inst_match::getNextMatch new round" << std::endl;
//     // First search of this round
//     d_partial.push_back( InstMatch() );
//     if(d_matchPolicy == MATCH_GEN_EFFICIENT_E_MATCH){
//       // Ask to efficient e-matching a new possibility
//       Assert(d_children_multi_efficient_index == 0 &&
//              d_children_multi_efficient.size() > 1);
//       while(!d_children_multi_efficient[d_children_multi_efficient_index]->
//             getNextMatch( d_partial.back(), qe)) {
//         d_partial.back().clear();
//         ++d_children_multi_efficient_index;
//         if(d_children_multi_efficient_index == d_children_multi_efficient.size()){
//           // None of the patterns have new matching terms
//           Debug("inst_match::getNextMatch") << "inst_match::getNextMatch No new terms by efficient e-matching" << std::endl;
//           return false;
//         }
//       }
//     Debug("inst_match::getNextMatch") << "inst_match::getNextMatch "
//                                       << " by initial " << d_children_multi_efficient_index
//                                       << " efficient d_partial " << d_partial.back() << std::endl;
//     }
//   }
//   /** todo reset? */

//   while( d_children.size() + 1 != d_partial.size() ) {
//     d_partial.push_back( InstMatch( &d_partial.back() ) );

//     Assert(d_children.size() + 1 >= d_partial.size());
//     const size_t index = d_partial.size() - 2;
//     if( !((d_matchPolicy == MATCH_GEN_EFFICIENT_E_MATCH &&
//            d_children_multi_efficient_index == index)
//           || d_children[index]->getNextMatch( d_partial.back(), qe ))
//        ){
//       /** No more match: backtrack */
//       d_children[index]->reset( Node::null(), qe );
//       d_partial.pop_back();
//       if(d_matchPolicy == MATCH_GEN_EFFICIENT_E_MATCH &&
//          d_children_multi_efficient_index == index - 1)
//         d_partial.pop_back(); //step above this one
//       if(d_partial.size() == 1){
//         /* Bottom of the stack */
//         if(d_matchPolicy != MATCH_GEN_EFFICIENT_E_MATCH)
//           return false;  /** No more possibilities */

//         // Ask to efficient e-matching a new possibility
//         d_partial.back().clear();
//         while(!d_children_multi_efficient[d_children_multi_efficient_index]->
//               getNextMatch( d_partial.back(), qe)) {
//           d_partial.back().clear();
//           ++d_children_multi_efficient_index;
//           if(d_children_multi_efficient_index == d_children_multi_efficient.size()){
//             // The patterns have no more new matching terms
//             // (given by efficient e matching)
//             Debug("inst_match::getNextMatch") << "inst_match::getNextMatch No more new terms by efficient e-matching" << std::endl;
//             return false;
//           }
//         }
//         Debug("inst_match::getNextMatch") << "inst_match::getNextMatch "
//                                           << " by " << d_children_multi_efficient_index
//                                           <<" efficient d_partial " << d_partial.back() << std::endl;
//       }else d_partial.pop_back();
//     };
//   }

//   /** A match is found */
//   m = d_partial.back();
//   d_partial.pop_back();
//   if(d_matchPolicy == MATCH_GEN_EFFICIENT_E_MATCH &&
//      d_children_multi_efficient_index == d_partial.size() - 1)
//     d_partial.pop_back(); //step above this one
//   return true;

// }



// Currently the implementation doesn't take into account that
// variable should have the same value given.
// TODO use the d_children way perhaps
// TODO replace by a real dictionnary
// We should create a real substitution? slower more precise
// We don't do that often
bool nonunifiable( TNode t0, TNode pat, const std::vector<Node> & vars){
  if(pat.isNull()) return true;

  typedef std::vector<std::pair<TNode,TNode> > tstack;
  tstack stack(1,std::make_pair(t0,pat)); // t * pat

  while(!stack.empty()){
    const std::pair<TNode,TNode> p = stack.back(); stack.pop_back();
    const TNode & t = p.first;
    const TNode & pat = p.second;

    // t or pat is a variable currently we consider that can match anything
    if( find(vars.begin(),vars.end(),t) != vars.end() ) continue;
    if( pat.getKind() == INST_CONSTANT ) continue;

    // t and pat are nonunifiable
    if( !Trigger::isAtomicTrigger( t ) || !Trigger::isAtomicTrigger( pat ) ) {
      if(t == pat) continue;
      else return true;
    };
    if( t.getOperator() != pat.getOperator() ) return true;

    //put the children on the stack
    for( size_t i=0; i < pat.getNumChildren(); i++ ){
      stack.push_back(std::make_pair(t[i],pat[i]));
    };
  }
  // The heuristic can't find non-unifiability
  return false;
};

// int InstMatchGenerator::addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//   //now, try to add instantiation for each match produced
//   Node f = d_match_pattern.getAttribute(InstConstantAttribute());
//   int addedLemmas = 0;
//   InstMatch m;
//   while( getNextMatch( m, qe ) ){
//     //m.makeInternal( d_quantEngine->getEqualityQuery() );
//     m.add( baseMatch );
//     if( qe->addInstantiation( f, m, addSplits ) ){
//       addedLemmas++;
//       if( instLimit>0 && addedLemmas==instLimit ){
//         return addedLemmas;
//       }
//     }
//     m.clear();
//   }
//   //return number of lemmas added
//   return addedLemmas;
// }

// /** constructors */
// InstMatchGeneratorMulti::InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption ) :
// d_f( f ){
//   Debug("smart-multi-trigger") << "Making smart multi-trigger for " << f << std::endl;
//   std::map< Node, std::vector< Node > > var_contains;
//   Trigger::getVarContains( f, pats, var_contains );
//   //convert to indicies
//   for( std::map< Node, std::vector< Node > >::iterator it = var_contains.begin(); it != var_contains.end(); ++it ){
//     Debug("smart-multi-trigger") << "Pattern " << it->first << " contains: ";
//     for( int i=0; i<(int)it->second.size(); i++ ){
//       Debug("smart-multi-trigger") << it->second[i] << " ";
//       int index = it->second[i].getAttribute(InstVarNumAttribute());
//       d_var_contains[ it->first ].push_back( index );
//       d_var_to_node[ index ].push_back( it->first );
//     }
//     Debug("smart-multi-trigger") << std::endl;
//   }
//   for( int i=0; i<(int)pats.size(); i++ ){
//     Node n = pats[i];
//     //make the match generator
//     d_children.push_back( new InstMatchGenerator( n, qe, matchOption ) );
//     //compute unique/shared variables
//     std::vector< int > unique_vars;
//     std::map< int, bool > shared_vars;
//     int numSharedVars = 0;
//     for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
//       if( d_var_to_node[ d_var_contains[n][j] ].size()==1 ){
//         Debug("smart-multi-trigger") << "Var " << d_var_contains[n][j] << " is unique to " << pats[i] << std::endl;
//         unique_vars.push_back( d_var_contains[n][j] );
//       }else{
//         shared_vars[ d_var_contains[n][j] ] = true;
//         numSharedVars++;
//       }
//     }
//     //we use the latest shared variables, then unique variables
//     std::vector< int > vars;
//     int index = i==0 ? (int)(pats.size()-1) : (i-1);
//     while( numSharedVars>0 && index!=i ){
//       for( std::map< int, bool >::iterator it = shared_vars.begin(); it != shared_vars.end(); ++it ){
//         if( it->second ){
//           if( std::find( d_var_contains[ pats[index] ].begin(), d_var_contains[ pats[index] ].end(), it->first )!=
//               d_var_contains[ pats[index] ].end() ){
//             vars.push_back( it->first );
//             shared_vars[ it->first ] = false;
//             numSharedVars--;
//           }
//         }
//       }
//       index = index==0 ? (int)(pats.size()-1) : (index-1);
//     }
//     vars.insert( vars.end(), unique_vars.begin(), unique_vars.end() );
//     Debug("smart-multi-trigger") << "   Index[" << i << "]: ";
//     for( int i=0; i<(int)vars.size(); i++ ){
//       Debug("smart-multi-trigger") << vars[i] << " ";
//     }
//     Debug("smart-multi-trigger") << std::endl;
//     //make ordered inst match trie
//     InstMatchTrie::ImtIndexOrder* imtio = new InstMatchTrie::ImtIndexOrder;
//     imtio->d_order.insert( imtio->d_order.begin(), vars.begin(), vars.end() );
//     d_children_trie.push_back( InstMatchTrieOrdered( imtio ) );
//   }

// }

// /** reset instantiation round (call this whenever equivalence classes have changed) */
// void InstMatchGeneratorMulti::resetInstantiationRound( QuantifiersEngine* qe ){
//   for( int i=0; i<(int)d_children.size(); i++ ){
//     d_children[i]->resetInstantiationRound( qe );
//   }
// }

// /** reset, eqc is the equivalence class to search in (any if eqc=null) */
// void InstMatchGeneratorMulti::reset( Node eqc, QuantifiersEngine* qe ){
//   for( int i=0; i<(int)d_children.size(); i++ ){
//     d_children[i]->reset( eqc, qe );
//   }
// }

// void InstMatchGeneratorMulti::collectInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
//                                                      std::vector< IndexedTrie >& unique_var_tries,
//                                                      int trieIndex, int childIndex, int endChildIndex, bool modEq ){
//   if( childIndex==endChildIndex ){
//     //now, process unique variables
//     collectInstantiations2( qe, m, addedLemmas, unique_var_tries, 0 );
//   }else if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
//     int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
//     Node curr_ic = qe->getInstantiationConstant( d_f, curr_index );
//     if( m.d_map.find( curr_ic )==m.d_map.end() ){
//       //if( d_var_to_node[ curr_index ].size()==1 ){    //FIXME
//       //  //unique variable(s), defer calculation
//       //  unique_var_tries.push_back( IndexedTrie( std::pair< int, int >( childIndex, trieIndex ), tr ) );
//       //  int newChildIndex = (childIndex+1)%(int)d_children.size();
//       //  collectInstantiations( qe, m, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
//       //                         0, newChildIndex, endChildIndex, modEq );
//       //}else{
//         //shared and non-set variable, add to InstMatch
//         for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
//           InstMatch mn( &m );
//           mn.d_map[ curr_ic ] = it->first;
//           collectInstantiations( qe, mn, addedLemmas, &(it->second), unique_var_tries,
//                                   trieIndex+1, childIndex, endChildIndex, modEq );
//         }
//       //}
//     }else{
//       //shared and set variable, try to merge
//       Node n = m.d_map[ curr_ic ];
//       std::map< Node, InstMatchTrie >::iterator it = tr->d_data.find( n );
//       if( it!=tr->d_data.end() ){
//         collectInstantiations( qe, m, addedLemmas, &(it->second), unique_var_tries,
//                                trieIndex+1, childIndex, endChildIndex, modEq );
//       }
//       if( modEq ){
//         //check modulo equality for other possible instantiations
//         if( ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine()->hasTerm( n ) ){
//           uf::EqClassIterator eqc = uf::EqClassIterator( qe->getEqualityQuery()->getRepresentative( n ),
//                                   ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
//           while( !eqc.isFinished() ){
//             Node en = (*eqc);
//             if( en!=n ){
//               std::map< Node, InstMatchTrie >::iterator itc = tr->d_data.find( en );
//               if( itc!=tr->d_data.end() ){
//                 collectInstantiations( qe, m, addedLemmas, &(itc->second), unique_var_tries,
//                                        trieIndex+1, childIndex, endChildIndex, modEq );
//               }
//             }
//             ++eqc;
//           }
//         }
//       }
//     }
//   }else{
//     int newChildIndex = (childIndex+1)%(int)d_children.size();
//     collectInstantiations( qe, m, addedLemmas, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
//                            0, newChildIndex, endChildIndex, modEq );
//   }
// }

// void InstMatchGeneratorMulti::collectInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
//                                                       std::vector< IndexedTrie >& unique_var_tries,
//                                                       int uvtIndex, InstMatchTrie* tr, int trieIndex ){
//   if( uvtIndex<(int)unique_var_tries.size() ){
//     int childIndex = unique_var_tries[uvtIndex].first.first;
//     if( !tr ){
//       tr = unique_var_tries[uvtIndex].second;
//       trieIndex = unique_var_tries[uvtIndex].first.second;
//     }
//     if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
//       int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
//       Node curr_ic = qe->getInstantiationConstant( d_f, curr_index );
//       //unique non-set variable, add to InstMatch
//       for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
//         InstMatch mn( &m );
//         mn.d_map[ curr_ic ] = it->first;
//         collectInstantiations2( qe, mn, addedLemmas, unique_var_tries, uvtIndex, &(it->second), trieIndex+1 );
//       }
//     }else{
//       collectInstantiations2( qe, m, addedLemmas, unique_var_tries, uvtIndex+1 );
//     }
//   }else{
//     //m is an instantiation
//     if( qe->addInstantiation( d_f, m, true ) ){
//       addedLemmas++;
//       Debug("smart-multi-trigger") << "-> Produced instantiation " << m << std::endl;
//     }
//   }
// }

// int InstMatchGeneratorMulti::addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//   int addedLemmas = 0;
//   Debug("smart-multi-trigger") << "Process smart multi trigger" << std::endl;
//   for( int i=0; i<(int)d_children.size(); i++ ){
//     Debug("smart-multi-trigger") << "Calculate matches " << i << std::endl;
//     std::vector< InstMatch > newMatches;
//     InstMatch m;
//     while( d_children[i]->getNextMatch( m, qe ) ){
//       m.makeRepresentative( qe->getEqualityQuery() );
//       newMatches.push_back( InstMatch( &m ) );
//       m.clear();
//     }
//     //std::cout << "Merge for new matches " << i << std::endl;
//     for( int j=0; j<(int)newMatches.size(); j++ ){
//       //see if these produce new matches
//       d_children_trie[i].addInstMatch( qe, d_f, newMatches[j], true );
//       //possibly only do the following if we know that new matches will be produced?
//       //the issue is that instantiations are filtered in quantifiers engine, and so there is no guarentee that
//       // we can safely skip the following lines, even when we have already produced this match.
//       Debug("smart-multi-trigger") << "Child " << i << " produced match " << newMatches[j] << std::endl;
//       //collect new instantiations
//       int childIndex = (i+1)%(int)d_children.size();
//       std::vector< IndexedTrie > unique_var_tries;
//       collectInstantiations( qe, newMatches[j], addedLemmas,
//                              d_children_trie[childIndex].getTrie(), unique_var_tries, 0, childIndex, i, true );
//     }
//     //std::cout << "Done. " << i << " " << (int)d_curr_matches.size() << std::endl;
//   }
//   return addedLemmas;
// }

// int InstMatchGeneratorSimple::addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//   InstMatch m;
//   m.add( baseMatch );
//   int addedLemmas = 0;
//   if( d_match_pattern.getType()==NodeManager::currentNM()->booleanType() ){
//     for( int i=0; i<2; i++ ){
//       addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_pred_map_trie[i][ d_match_pattern.getOperator() ]),
//                          instLimit, addSplits );
//     }
//   }else{
//     addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_func_map_trie[ d_match_pattern.getOperator() ]),
//                        instLimit, addSplits );
//   }
//   return addedLemmas;
// }

// void InstMatchGeneratorSimple::addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex,
//                                                   TermArgTrie* tat, int instLimit, bool addSplits ){
//   if( argIndex==(int)d_match_pattern.getNumChildren() ){
//     //m is an instantiation
//     if( qe->addInstantiation( d_f, m, addSplits ) ){
//       addedLemmas++;
//       Debug("simple-multi-trigger") << "-> Produced instantiation " << m << std::endl;
//     }
//   }else{
//     if( d_match_pattern[argIndex].getKind()==INST_CONSTANT ){
//       Node ic = d_match_pattern[argIndex];
//       for( std::map< Node, TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
//         Node t = it->first;
//         if( m.d_map[ ic ].isNull() || m.d_map[ ic ]==t ){
//           Node prev = m.d_map[ ic ];
//           m.d_map[ ic ] = t;
//           addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second), instLimit, addSplits );
//           m.d_map[ ic ] = prev;
//         }
//       }
//     }else{
//       Node r = qe->getEqualityQuery()->getRepresentative( d_match_pattern[argIndex] );
//       std::map< Node, TermArgTrie >::iterator it = tat->d_data.find( r );
//       if( it!=tat->d_data.end() ){
//         addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second), instLimit, addSplits );
//       }
//     }
//   }
// }


/** New things */
class DumbMatcher: public Matcher{
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( Node n, InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
};

class DumbPatMatcher: public PatMatcher{
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
};


/* The order of the matching is:
   reset arg1, nextMatch arg1, reset arg2, nextMatch arg2, ... */
ApplyMatcher::ApplyMatcher( Node pat, QuantifiersEngine* qe): d_pattern(pat){
  Assert( pat.hasAttribute(InstConstantAttribute()) );
  Assert( pat.getKind() == kind::APPLY_UF );

  //set-up d_children, d_children_index and d_binded
  for( size_t i=0; i< d_pattern.getNumChildren(); ++i ){
    if( d_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_pattern[i].getKind()!=INST_CONSTANT ){
        //It's neither a constant argument neither a variable
        //we create the matcher for the subpattern
        d_children.push_back(mkMatcher(d_pattern[i], qe));
        d_children_index.push_back( i );
      }
    }
  }
}

void ApplyMatcher::resetInstantiationRound( QuantifiersEngine* qe ){
  for( size_t i=0; i< d_children.size(); i++ ){
    d_children[i]->resetInstantiationRound( qe );
  }
}

bool ApplyMatcher::reset(Node t, InstMatch & m, QuantifiersEngine* qe){
  Debug("matching") << "Matching " << t << " against pattern " << d_pattern << " ("
                    << m.d_map.size() << ")"  << std::endl;
  EqualityQuery* q = qe->getEqualityQuery();
  d_binded.clear();

  //if t is null
  Assert( !t.isNull() );
  Assert( !t.hasAttribute(InstConstantAttribute()) );
  Assert( t.getKind()==d_pattern.getKind() );
  Assert( t.getKind()!=APPLY_UF || t.getOperator()==d_pattern.getOperator() );
  //first, check if ground arguments are not equal, or a match is in conflict
  for( size_t i=0; i< d_pattern.getNumChildren(); i++ ){
    if( d_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_pattern[i].getKind()==INST_CONSTANT ){
        bool set;
        if( !m.setMatch( q, d_pattern[i], t[i], set) ){
          //match is in conflict
          Debug("matching-debug") << "Match in conflict " << t[i] << " and "
                                  << d_pattern[i] << " because "
                                  << m.d_map[d_pattern[i]]
                                  << std::endl;
          Debug("matching-fail") << "Match fail: " << m.d_map[d_pattern[i]] << " and " << t[i] << std::endl;
          //setMatchFail( qe, partial[0].d_map[d_pattern[i]], t[i] );
          m.erase(d_binded.begin(), d_binded.end());
          return false;
        }else{
          if(set){ //The variable has just been set
            d_binded.push_back(d_pattern[i]);
          }
        }
      }
    }else{
      //This argument is a constant
      if( !q->areEqual( d_pattern[i], t[i] ) ){
        Debug("matching-fail") << "Match fail arg: " << d_pattern[i] << " and " << t[i] << std::endl;
        //setMatchFail( qe, d_pattern[i], t[i] );
        //ground arguments are not equal
        m.erase(d_binded.begin(), d_binded.end());
        return false;
      }
    }
  }

  //now, fit children into match
  //we will be requesting candidates for matching terms for each child
  d_reps.clear();
  for( size_t i=0; i< d_children.size(); i++ ){
    Node rep = q->getRepresentative( t[ d_children_index[i] ] );
    d_reps.push_back( rep );
  }

  size_t index = 0;
  while( index< d_children.size() ){
    if(!d_children[index]->reset( d_reps[index], m, qe )){
      if(index == 0){
        m.erase(d_binded.begin(), d_binded.end());
        return false;
      } else return getNextMatch(m, qe, index-1);
    };
    ++index;
  };
  return true;
}


bool ApplyMatcher::getNextMatch(InstMatch& m, QuantifiersEngine* qe, size_t index){
  //combine child matches
  Assert ( index < d_children.size() );
  while( true ){
    if( d_children[index]->getNextMatch( m, qe ) ){
      ++index;
      if ( index == d_children.size() ) return true;
      // If the initialization failed we come back.
      if(!d_children[index]->reset( d_reps[index], m, qe )) --index;
    }else{
      if(index == 0){
        m.erase(d_binded.begin(), d_binded.end());
        return false;
      }
      --index;
    }
  }
}

bool ApplyMatcher::getNextMatch(InstMatch& m, QuantifiersEngine* qe){
  if(d_children.size() == 0){
    m.erase(d_binded.begin(), d_binded.end());
    return false;
  } else return getNextMatch(m, qe, d_children.size() - 1);
}

/** Proxy that call the sub-matcher on the result return by the given candidate generator */
template <class CG, class M>
class CandidateGeneratorMatcher: public Matcher{
  /** candidate generator */
  CG d_cg;
  /** the sub-matcher */
  M d_m;
public:
  CandidateGeneratorMatcher(CG cg, M m): d_cg(cg), d_m(m)
  {/* last is Null */};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cg.resetInstantiationRound();
    d_m.resetInstantiationRound(qe);
  };
  bool reset( Node n, InstMatch& m, QuantifiersEngine* qe ){
    d_cg.reset(n);
    return findMatch(m,qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    // The sub-matcher has another match
    return d_m.getNextMatch(m, qe) || findMatch(m,qe);
  }
private:
  bool findMatch( InstMatch& m, QuantifiersEngine* qe ){
    // Otherwise try to find a new candidate that has at least one match
    Node n;
    while(true){
      n = d_cg.getNextCandidate();
      if(n.isNull()) return false;
      if(d_m.reset(n,m,qe)) return true;
    };
  }
};

/** Proxy that call the sub-matcher on the result return by the given candidate generator */
template<class M>
class PatOfMatcher: public PatMatcher{
  M d_m;
public:
  inline PatOfMatcher(M m): d_m(m){}
  void resetInstantiationRound(QuantifiersEngine* qe){
    d_m.resetInstantiationRound(qe);
  }
  bool reset(InstMatch& m, QuantifiersEngine* qe){
    return d_m.reset(Node::null(),m,qe);
  };
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe){
    return d_m.getNextMatch(m,qe);
  };
};

class ArithMatcher: public Matcher{
private:
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
  /** get the match against ground term or formula t.
      d_match_mattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  /** the variable that are set by this matcher */
  std::vector< TNode > d_binded; /* TNode because the variables are already in d_arith_coeffs */
  Node d_pattern; //for debugging
public:
  ArithMatcher(Node pat, QuantifiersEngine* qe);
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( Node n, InstMatch& m, QuantifiersEngine* qe );
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
};

/** Match just a variable */
class VarMatcher: public Matcher{
  Node d_var;
  bool d_binded; /* True if the reset bind the variable to some value */
public:
  VarMatcher(Node var, QuantifiersEngine* qe): d_var(var), d_binded(false){}
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( Node n, InstMatch& m, QuantifiersEngine* qe ){
    EqualityQuery* q = qe->getEqualityQuery();
    if(!m.setMatch( q, d_var, n, d_binded )){
      //match is in conflict
      return false;
    } else return true;
  };
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    //match is in conflict
    if (d_binded) m.erase(d_var);
    return false;
  }
};

template <class M, class Test >
class TestMatcher: public Matcher{
  M d_m;
  Test d_test;
public:
  inline TestMatcher(M m, Test test): d_m(m), d_test(test){}
  inline void resetInstantiationRound(QuantifiersEngine* qe){
    d_m.resetInstantiationRound(qe);
  }
  inline bool reset(Node n, InstMatch& m, QuantifiersEngine* qe){
    return d_test(n) && d_m.reset(n, m, qe);
  }
  inline bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_m.getNextMatch(m, qe);
  }
};

class LegalOpTest: public unary_function<Node,bool> {
  Node d_op;
public:
  inline LegalOpTest(Node op): d_op(op){}
  inline bool operator() (Node n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      n.getKind()==APPLY_UF &&
      n.getOperator()==d_op;
  };
};

class LegalKindTest : public unary_function<Node,bool> {
  Kind d_kind;
public:
  inline LegalKindTest(Kind kind): d_kind(kind){}
  inline bool operator() (Node n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      n.getKind()==d_kind;
  };
};

class LegalTypeTest : public unary_function<Node,bool> {
  TypeNode d_type;
public:
  inline LegalTypeTest(TypeNode type): d_type(type){}
  inline bool operator() (Node n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      n.getType()==d_type;
  };
};

class LegalTest : public unary_function<Node,bool> {
public:
  inline bool operator() (Node n) {
    return CandidateGenerator::isLegalCandidate(n);
  };
};

class OpMatcher: public Matcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalOpTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfClass, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::APPLY_UF );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalOpTest(pat.getOperator()));
    /** Iter on the equivalence class of the given term */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF *>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
    uf::InstantiatorTheoryUf* ith =
      static_cast<uf::InstantiatorTheoryUf*>(uf->getInstantiator());
    CandidateGeneratorTheoryUfClass cdtUfEq(ith);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  OpMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)){}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( Node t, InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(t, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

class AllOpMatcher: public PatMatcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfOp, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::APPLY_UF );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalTest());
    /** Iter on the equivalence class of the given term */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF *>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
    uf::InstantiatorTheoryUf* ith =
      static_cast<uf::InstantiatorTheoryUf*>(uf->getInstantiator());
    CandidateGeneratorTheoryUfOp cdtUfEq(pat.getOperator(),ith);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  AllOpMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)){}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(Node::null(), m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};



/** Match all the pattern with the same term */
class SplitMatcher: public Matcher{
private:
  const size_t size;
  ApplyMatcher d_m; /** Use ApplyMatcher by creating a fake application */
public:
  SplitMatcher(std::vector< Node > pats, QuantifiersEngine* qe):
    size(pats.size()),
    d_m(NodeManager::currentNM()->mkNode(kind::INST_PATTERN,pats), qe) {}
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_m.resetInstantiationRound(qe);
  };
  bool reset( Node ex, InstMatch& m, QuantifiersEngine* qe ){
    NodeBuilder<> n(kind::INST_PATTERN);
    for(size_t i = 0; i < size; ++i) n << ex;
    return d_m.reset(n,m,qe);
  };
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return getNextMatch(m, qe);
  }
};


/** Match uf term in a fixed equivalence class */
class UfCstEqMatcher: public PatMatcher{
private:
  /* equivalence class to match */
  Node d_cst;
  /* generator */
  OpMatcher d_cgm;
public:
  UfCstEqMatcher( Node pat, Node cst, QuantifiersEngine* qe ):
    d_cst(cst),
    d_cgm(OpMatcher(pat,qe)) {};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(d_cst, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

/** Match equalities */
class UfEqMatcher: public PatMatcher{
private:
  /* generator */
  typedef SplitMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalTypeTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfClasses, AuxMatcher2 > AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(std::vector<Node> & pat, QuantifiersEngine* qe){
    Assert( pat.size() > 0);
    TypeNode ty = pat[0].getType();
    for(size_t i = 1; i < pat.size(); ++i){
      Assert(pat[i].getType() == ty);
    }
    /** In reverse order of matcher sequence */
    /** Distribute it to all the pattern */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good type */
    AuxMatcher2 am2(am3,LegalTypeTest(ty));
    /** Generate one term by eq classes */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
    uf::InstantiatorTheoryUf* ith =
      static_cast<uf::InstantiatorTheoryUf*>(uf->getInstantiator());
    CandidateGeneratorTheoryUfClasses cdtUfEq(ith);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  UfEqMatcher( std::vector<Node> & pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)){}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(Node::null(), m, qe); //cdtUfEq doesn't use it's argument for reset
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};


/** Match dis-equalities */
class UfDeqMatcher: public PatMatcher{
private:
  /* generator */
  typedef ApplyMatcher AuxMatcher3;

  class EqTest : public unary_function<Node,bool> {
    TypeNode d_type;
  public:
    inline EqTest(TypeNode type): d_type(type){};
    inline bool operator() (Node n) {
      return
        CandidateGenerator::isLegalCandidate(n) &&
        n.getKind() == kind::EQUAL &&
        n[0].getType()==d_type;
    };
  };
  typedef TestMatcher< AuxMatcher3, EqTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfClass, AuxMatcher2 > AuxMatcher1;
  AuxMatcher1 d_cgm;
  Node false_term;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::NOT);
    TNode eq = pat[0];
    Assert( eq.getKind() == kind::EQUAL);
    TypeNode ty = eq[0].getType();
    /** In reverse order of matcher sequence */
    /** Distribute it to all the pattern */
    AuxMatcher3 am3(eq,qe);
    /** Keep only the one that have the good type */
    AuxMatcher2 am2(am3,EqTest(ty));
    /** Will generate all the terms of the eq class of false */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
    uf::InstantiatorTheoryUf* ith =
      static_cast<uf::InstantiatorTheoryUf*>(uf->getInstantiator());
    CandidateGeneratorTheoryUfClass cdtUfEq(ith);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  UfDeqMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),
    false_term((static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF )))->getEqualityEngine()->
                getRepresentative(NodeManager::currentNM()->mkConst<bool>(false) )){};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(false_term, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

Matcher* mkMatcher( Node pat, QuantifiersEngine* qe ){
  Debug("inst-match-gen") << "mkMatcher: Pattern term is " << pat << std::endl;

  if( Trigger::isAtomicTrigger( pat ) ){
    return new OpMatcher(pat, qe);
  } else { /* Arithmetic? */
    /** TODO: something simpler to see if the pattern is a good
        arithmetic pattern */
    std::map< Node, Node > d_arith_coeffs;
    if( !Trigger::getPatternArithmetic( pat.getAttribute(InstConstantAttribute()), pat, d_arith_coeffs ) ){
      Debug("inst-match-gen") << "(?) Unknown matching pattern is " << pat << std::endl;
      std::cout << "(?) Unknown matching pattern is " << pat << std::endl;
      return new DumbMatcher();
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << pat << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
      ArithMatcher am3 (pat, qe);
      TestMatcher<ArithMatcher, LegalTypeTest>
        am2(am3,LegalTypeTest(pat.getType()));
      /* generator */
      uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
      uf::InstantiatorTheoryUf* ith =
        static_cast<uf::InstantiatorTheoryUf*> (uf->getInstantiator());
      CandidateGeneratorTheoryUfClass cdtUfEq(ith);
      return new CandidateGeneratorMatcher< CandidateGeneratorTheoryUfClass,
        TestMatcher<ArithMatcher, LegalTypeTest> > (cdtUfEq,am2);
    }
  }
};

PatMatcher* mkPattern( Node pat, QuantifiersEngine* qe ){
  Debug("inst-match-gen") << "Pattern term is " << pat << std::endl;
  Assert( pat.hasAttribute(InstConstantAttribute()) );

  if( pat.getKind()==kind::NOT && pat[0].getKind() == kind::EQUAL){
    /* Difference */
    return new UfDeqMatcher(pat, qe);
  } else if (pat.getKind() == kind::EQUAL){
    if( !pat[0].hasAttribute(InstConstantAttribute() )){
        Assert(pat[1].hasAttribute(InstConstantAttribute()));
        return new UfCstEqMatcher(pat[1], pat[0], qe);
    }else if( !pat[1].hasAttribute(InstConstantAttribute() )){
      Assert(pat[0].hasAttribute(InstConstantAttribute()));
      return new UfCstEqMatcher(pat[0], pat[1], qe);
    }else{
      std::vector< Node > pats(pat.begin(),pat.end());
      return new UfEqMatcher(pats,qe);
    }
  } else if( Trigger::isAtomicTrigger( pat ) ){
    return new AllOpMatcher(pat, qe);
  } else { /* Arithmetic? */
    /** TODO: something simpler to see if the pattern is a good
        arithmetic pattern */
    std::map< Node, Node > d_arith_coeffs;
    if( !Trigger::getPatternArithmetic( pat.getAttribute(InstConstantAttribute()), pat, d_arith_coeffs ) ){
      Debug("inst-match-gen") << "(?) Unknown matching pattern is " << pat << std::endl;
      std::cout << "(?) Unknown matching pattern is " << pat << std::endl;
      return new DumbPatMatcher();
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << pat << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
      ArithMatcher am3 (pat, qe);
      TestMatcher<ArithMatcher, LegalTest>
        am2(am3,LegalTest());
      /* generator */
      uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->getTheory( theory::THEORY_UF ));
      uf::InstantiatorTheoryUf* ith =
        static_cast<uf::InstantiatorTheoryUf*> (uf->getInstantiator());
      CandidateGeneratorTheoryUfType cdtUfEq(pat.getType(),ith);
      typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfType,
                                          TestMatcher<ArithMatcher, LegalTest> > AuxMatcher1;
      return new PatOfMatcher<AuxMatcher1>(AuxMatcher1(cdtUfEq,am2));
    }
  }
};

ArithMatcher::ArithMatcher(Node pat, QuantifiersEngine* qe): d_pattern(pat){

  if(Trigger::getPatternArithmetic(pat.getAttribute(InstConstantAttribute()), pat, d_arith_coeffs ) )
    {
    Debug("inst-match-gen") << "(?) Unknown matching pattern is " << d_pattern << std::endl;
    Assert(false);
  }else{
    Debug("matching-arith") << "Generated arithmetic pattern for " << d_pattern << ": " << std::endl;
    for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
      Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
    }
  }

};

bool ArithMatcher::reset( Node t, InstMatch& m, QuantifiersEngine* qe ){
  Debug("matching-arith") << "Matching " << t << " " << d_pattern << std::endl;
  d_binded.clear();
  if( !d_arith_coeffs.empty() ){
    NodeBuilder<> tb(kind::PLUS);
    Node ic = Node::null();
    for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
      Debug("matching-arith") << it->first << " -> " << it->second << std::endl;
      if( !it->first.isNull() ){
        if( m.d_map.find( it->first )==m.d_map.end() ){
          //see if we can choose this to set
          if( ic.isNull() && ( it->second.isNull() || !it->first.getType().isInteger() ) ){
            ic = it->first;
          }
        }else{
          Debug("matching-arith") << "already set " << m.d_map[ it->first ] << std::endl;
          Node tm = m.d_map[ it->first ];
          if( !it->second.isNull() ){
            tm = NodeManager::currentNM()->mkNode( MULT, it->second, tm );
          }
          tb << tm;
        }
      }else{
        tb << it->second;
      }
    }
    if( !ic.isNull() ){
      Node tm;
      if( tb.getNumChildren()==0 ){
        tm = t;
      }else{
        tm = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
        tm = NodeManager::currentNM()->mkNode( MINUS, t, tm );
      }
      if( !d_arith_coeffs[ ic ].isNull() ){
        Assert( !ic.getType().isInteger() );
        Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_arith_coeffs[ ic ].getConst<Rational>() );
        tm = NodeManager::currentNM()->mkNode( MULT, coeff, tm );
      }
      m.d_map[ ic ] = Rewriter::rewrite( tm );
      d_binded.push_back(ic);
      //set the rest to zeros
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        if( !it->first.isNull() ){
          if( m.d_map.find( it->first )==m.d_map.end() ){
            m.d_map[ it->first ] = NodeManager::currentNM()->mkConst( Rational(0) );
            d_binded.push_back(ic);
          }
        }
      }
      Debug("matching-arith") << "Setting " << ic << " to " << tm << std::endl;
      return true;
    }else{
      m.erase(d_binded.begin(), d_binded.end());
      return false;
    }
  }else{
    m.erase(d_binded.begin(), d_binded.end());
    return false;
  }
};

bool ArithMatcher::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
  m.erase(d_binded.begin(), d_binded.end());
  return false;
};

class MultiPatsMatcher: public PatsMatcher{
private:
  bool d_reset_done;
  std::vector< PatMatcher* > d_patterns;
  InstMatch im;
  bool reset( QuantifiersEngine* qe ){
    im.clear();
    d_reset_done = true;

    size_t index = 0;
    while( index< d_patterns.size() ){
      Debug("matching") << "MultiPatsMatcher::reset " << index << std::endl;
      if(!d_patterns[index]->reset( im, qe )){
        Debug("matching") << "MultiPatsMatcher::reset fail " << index << std::endl;
        if(index == 0) return false;
        else return getNextMatch(qe,index-1);
      };
      ++index;
    };
    return true;
  };

  bool getNextMatch( QuantifiersEngine* qe, size_t index ){
    //combine child matches
    Assert( index< d_patterns.size() );
    while( true ){
      Debug("matching") << "MultiPatsMatcher::index " << index << std::endl;
      if( d_patterns[index]->getNextMatch( im, qe ) ){
        ++index;
        if ( index == d_patterns.size() ) return true;
        Debug("matching") << "MultiPatsMatcher::rereset " << index << std::endl;
        // If the initialization failed we come back.
        if(!d_patterns[index]->reset( im, qe )) --index;
      }else{
        if(index == 0){
          return false;
        }
        --index;
      }
    }
  }
public:
  MultiPatsMatcher(std::vector< Node > & pats, QuantifiersEngine* qe):
    d_reset_done(false){
    Assert(pats.size() > 0);
    for( size_t i=0; i< pats.size(); i++ ){
      d_patterns.push_back(mkPattern(pats[i],qe));
    };
  };
  void resetInstantiationRound( QuantifiersEngine* qe ){
    for( size_t i=0; i< d_patterns.size(); i++ ){
      d_patterns[i]->resetInstantiationRound( qe );
    };
    d_reset_done = false;
    im.clear();
  };
  bool getNextMatch( QuantifiersEngine* qe ){
    Assert(d_patterns.size()>0);
    if(d_reset_done) return getNextMatch(qe,d_patterns.size() - 1);
    else return reset(qe);
  }
  const InstMatch& getInstMatch(){return im;};

  int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe, int instLimit, bool addSplits );
};

enum Step{
  STOP,
  GET_MONO_CANDIDATE,
  GET_MULTI_CANDIDATE,
  RESET1,
  RESET2,
  NEXT1,
  NEXT2,
  RESET_OTHER,
  NEXT_OTHER,
};
static inline std::ostream& operator<<(std::ostream& out, const Step& step) {
  switch(step){
  case STOP: out << "STOP"; break;
  case GET_MONO_CANDIDATE: out << "GET_MONO_CANDIDATE"; break;
  case GET_MULTI_CANDIDATE: out << "GET_MULTI_CANDIDATE"; break;
  case RESET1: out << "RESET1"; break;
  case RESET2: out << "RESET2"; break;
  case NEXT1: out << "NEXT1"; break;
  case NEXT2: out << "NEXT2"; break;
  case RESET_OTHER: out << "RESET_OTHER"; break;
  case NEXT_OTHER: out << "NEXT_OTHER"; break;
  }
  return out;
}


int MultiPatsMatcher::addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe, int instLimit, bool addSplits ){
  //now, try to add instantiation for each match produced
  int addedLemmas = 0;
  resetInstantiationRound( qe );
  im.add( baseMatch );
  while( getNextMatch( qe ) ){
    InstMatch im_copy = getInstMatch();
    //m.makeInternal( d_quantEngine->getEqualityQuery() );
    if( qe->addInstantiation( quant, im_copy, addSplits ) ){
      addedLemmas++;
      if( instLimit>0 && addedLemmas==instLimit ){
        return addedLemmas;
      }
    }
  }
  //return number of lemmas added
  return addedLemmas;
}

// /** constructors */
// InstMatchGeneratorMulti::InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption ) :
// d_f( f ){
//   Debug("smart-multi-trigger") << "Making smart multi-trigger for " << f << std::endl;
//   std::map< Node, std::vector< Node > > var_contains;
//   Trigger::getVarContains( f, pats, var_contains );
//   //convert to indicies
//   for( std::map< Node, std::vector< Node > >::iterator it = var_contains.begin(); it != var_contains.end(); ++it ){
//     Debug("smart-multi-trigger") << "Pattern " << it->first << " contains: ";
//     for( int i=0; i<(int)it->second.size(); i++ ){
//       Debug("smart-multi-trigger") << it->second[i] << " ";
//       int index = it->second[i].getAttribute(InstVarNumAttribute());
//       d_var_contains[ it->first ].push_back( index );
//       d_var_to_node[ index ].push_back( it->first );
//     }
//     Debug("smart-multi-trigger") << std::endl;
//   }
//   for( int i=0; i<(int)pats.size(); i++ ){
//     Node n = pats[i];
//     //make the match generator
//     d_children.push_back( new InstMatchGenerator( n, qe, matchOption ) );
//     //compute unique/shared variables
//     std::vector< int > unique_vars;
//     std::map< int, bool > shared_vars;
//     int numSharedVars = 0;
//     for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
//       if( d_var_to_node[ d_var_contains[n][j] ].size()==1 ){
//         Debug("smart-multi-trigger") << "Var " << d_var_contains[n][j] << " is unique to " << pats[i] << std::endl;
//         unique_vars.push_back( d_var_contains[n][j] );
//       }else{
//         shared_vars[ d_var_contains[n][j] ] = true;
//         numSharedVars++;
//       }
//     }
//     //we use the latest shared variables, then unique variables
//     std::vector< int > vars;
//     int index = i==0 ? (int)(pats.size()-1) : (i-1);
//     while( numSharedVars>0 && index!=i ){
//       for( std::map< int, bool >::iterator it = shared_vars.begin(); it != shared_vars.end(); ++it ){
//         if( it->second ){
//           if( std::find( d_var_contains[ pats[index] ].begin(), d_var_contains[ pats[index] ].end(), it->first )!=
//               d_var_contains[ pats[index] ].end() ){
//             vars.push_back( it->first );
//             shared_vars[ it->first ] = false;
//             numSharedVars--;
//           }
//         }
//       }
//       index = index==0 ? (int)(pats.size()-1) : (index-1);
//     }
//     vars.insert( vars.end(), unique_vars.begin(), unique_vars.end() );
//     Debug("smart-multi-trigger") << "   Index[" << i << "]: ";
//     for( int i=0; i<(int)vars.size(); i++ ){
//       Debug("smart-multi-trigger") << vars[i] << " ";
//     }
//     Debug("smart-multi-trigger") << std::endl;
//     //make ordered inst match trie
//     InstMatchTrie::ImtIndexOrder* imtio = new InstMatchTrie::ImtIndexOrder;
//     imtio->d_order.insert( imtio->d_order.begin(), vars.begin(), vars.end() );
//     d_children_trie.push_back( InstMatchTrieOrdered( imtio ) );
//   }

// }


// /** reset, eqc is the equivalence class to search in (any if eqc=null) */
// void InstMatchGeneratorMulti::reset( Node eqc, QuantifiersEngine* qe ){
//   for( int i=0; i<(int)d_children.size(); i++ ){
//     d_children[i]->reset( eqc, qe );
//   }
// }

// void InstMatchGeneratorMulti::collectInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
//                                                      std::vector< IndexedTrie >& unique_var_tries,
//                                                      int trieIndex, int childIndex, int endChildIndex, bool modEq ){
//   if( childIndex==endChildIndex ){
//     //now, process unique variables
//     collectInstantiations2( qe, m, addedLemmas, unique_var_tries, 0 );
//   }else if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
//     int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
//     Node curr_ic = qe->getInstantiationConstant( d_f, curr_index );
//     if( m.d_map.find( curr_ic )==m.d_map.end() ){
//       //if( d_var_to_node[ curr_index ].size()==1 ){    //FIXME
//       //  //unique variable(s), defer calculation
//       //  unique_var_tries.push_back( IndexedTrie( std::pair< int, int >( childIndex, trieIndex ), tr ) );
//       //  int newChildIndex = (childIndex+1)%(int)d_children.size();
//       //  collectInstantiations( qe, m, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
//       //                         0, newChildIndex, endChildIndex, modEq );
//       //}else{
//         //shared and non-set variable, add to InstMatch
//         for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
//           InstMatch mn( &m );
//           mn.d_map[ curr_ic ] = it->first;
//           collectInstantiations( qe, mn, addedLemmas, &(it->second), unique_var_tries,
//                                   trieIndex+1, childIndex, endChildIndex, modEq );
//         }
//       //}
//     }else{
//       //shared and set variable, try to merge
//       Node n = m.d_map[ curr_ic ];
//       std::map< Node, InstMatchTrie >::iterator it = tr->d_data.find( n );
//       if( it!=tr->d_data.end() ){
//         collectInstantiations( qe, m, addedLemmas, &(it->second), unique_var_tries,
//                                trieIndex+1, childIndex, endChildIndex, modEq );
//       }
//       if( modEq ){
//         //check modulo equality for other possible instantiations
//         if( ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine()->hasTerm( n ) ){
//           uf::EqClassIterator eqc = uf::EqClassIterator( qe->getEqualityQuery()->getRepresentative( n ),
//                                   ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
//           while( !eqc.isFinished() ){
//             Node en = (*eqc);
//             if( en!=n ){
//               std::map< Node, InstMatchTrie >::iterator itc = tr->d_data.find( en );
//               if( itc!=tr->d_data.end() ){
//                 collectInstantiations( qe, m, addedLemmas, &(itc->second), unique_var_tries,
//                                        trieIndex+1, childIndex, endChildIndex, modEq );
//               }
//             }
//             ++eqc;
//           }
//         }
//       }
//     }
//   }else{
//     int newChildIndex = (childIndex+1)%(int)d_children.size();
//     collectInstantiations( qe, m, addedLemmas, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
//                            0, newChildIndex, endChildIndex, modEq );
//   }
// }

// void InstMatchGeneratorMulti::collectInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
//                                                       std::vector< IndexedTrie >& unique_var_tries,
//                                                       int uvtIndex, InstMatchTrie* tr, int trieIndex ){
//   if( uvtIndex<(int)unique_var_tries.size() ){
//     int childIndex = unique_var_tries[uvtIndex].first.first;
//     if( !tr ){
//       tr = unique_var_tries[uvtIndex].second;
//       trieIndex = unique_var_tries[uvtIndex].first.second;
//     }
//     if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
//       int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
//       Node curr_ic = qe->getInstantiationConstant( d_f, curr_index );
//       //unique non-set variable, add to InstMatch
//       for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
//         InstMatch mn( &m );
//         mn.d_map[ curr_ic ] = it->first;
//         collectInstantiations2( qe, mn, addedLemmas, unique_var_tries, uvtIndex, &(it->second), trieIndex+1 );
//       }
//     }else{
//       collectInstantiations2( qe, m, addedLemmas, unique_var_tries, uvtIndex+1 );
//     }
//   }else{
//     //m is an instantiation
//     if( qe->addInstantiation( d_f, m, true ) ){
//       addedLemmas++;
//       Debug("smart-multi-trigger") << "-> Produced instantiation " << m << std::endl;
//     }
//   }
// }

// int InstMatchGeneratorMulti::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//   int addedLemmas = 0;
//   Debug("smart-multi-trigger") << "Process smart multi trigger" << std::endl;
//   for( int i=0; i<(int)d_children.size(); i++ ){
//     Debug("smart-multi-trigger") << "Calculate matches " << i << std::endl;
//     std::vector< InstMatch > newMatches;
//     InstMatch m;
//     while( d_children[i]->getNextMatch( m, qe ) ){
//       m.makeRepresentative( qe );
//       newMatches.push_back( InstMatch( &m ) );
//       m.clear();
//     }
//     //std::cout << "Merge for new matches " << i << std::endl;
//     for( int j=0; j<(int)newMatches.size(); j++ ){
//       //see if these produce new matches
//       d_children_trie[i].addInstMatch( qe, d_f, newMatches[j], true );
//       //possibly only do the following if we know that new matches will be produced?
//       //the issue is that instantiations are filtered in quantifiers engine, and so there is no guarentee that
//       // we can safely skip the following lines, even when we have already produced this match.
//       Debug("smart-multi-trigger") << "Child " << i << " produced match " << newMatches[j] << std::endl;
//       //collect new instantiations
//       int childIndex = (i+1)%(int)d_children.size();
//       std::vector< IndexedTrie > unique_var_tries;
//       collectInstantiations( qe, newMatches[j], addedLemmas,
//                              d_children_trie[childIndex].getTrie(), unique_var_tries, 0, childIndex, i, true );
//     }
//     //std::cout << "Done. " << i << " " << (int)d_curr_matches.size() << std::endl;
//   }
//   return addedLemmas;
// }

// int InstMatchGeneratorSimple::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//   InstMatch m;
//   m.add( baseMatch );
//   int addedLemmas = 0;
//   if( d_match_pattern.getType()==NodeManager::currentNM()->booleanType() ){
//     for( int i=0; i<2; i++ ){
//       addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_pred_map_trie[i][ d_match_pattern.getOperator() ]),
//                          instLimit, addSplits );
//     }
//   }else{
//     addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_func_map_trie[ d_match_pattern.getOperator() ]),
//                        instLimit, addSplits );
//   }
//   return addedLemmas;
// }

// void InstMatchGeneratorSimple::addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex,
//                                                   TermArgTrie* tat, int instLimit, bool addSplits ){
//   if( argIndex==(int)d_match_pattern.getNumChildren() ){
//     //m is an instantiation
//     if( qe->addInstantiation( d_f, m, addSplits ) ){
//       addedLemmas++;
//       Debug("simple-multi-trigger") << "-> Produced instantiation " << m << std::endl;
//     }
//   }else{
//     if( d_match_pattern[argIndex].getKind()==INST_CONSTANT ){
//       Node ic = d_match_pattern[argIndex];
//       for( std::map< Node, TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
//         Node t = it->first;
//         if( m.d_map[ ic ].isNull() || m.d_map[ ic ]==t ){
//           Node prev = m.d_map[ ic ];
//           m.d_map[ ic ] = t;
//           addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second), instLimit, addSplits );
//           m.d_map[ ic ] = prev;
//         }
//       }
//     }else{
//       Node r = qe->getEqualityQuery()->getRepresentative( d_match_pattern[argIndex] );
//       std::map< Node, TermArgTrie >::iterator it = tat->d_data.find( r );
//       if( it!=tat->d_data.end() ){
//         addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second), instLimit, addSplits );
//       }
//     }
//   }
// }


PatsMatcher* mkPatterns( std::vector< Node > pat, QuantifiersEngine* qe ){
  return new MultiPatsMatcher( pat, qe);
}

class MultiEfficientPatsMatcher: public PatsMatcher{
private:
  bool d_phase_mono;
  std::vector< PatMatcher* > d_patterns;
  std::vector< ApplyMatcher > d_direct_patterns;
  InstMatch d_im;
  uf::EfficientHandler d_eh;
  uf::EfficientHandler::MultiCandidate d_mc;

  // bool indexDone( size_t i){
  //   return i == d_c.first.second ||
  //     ( i == d_c.second.second && d_c.second.first.empty());
  // }



  static const Step START = GET_MONO_CANDIDATE;
  Step d_step;

  bool resetOther( QuantifiersEngine* qe ){
    size_t index = 0;
    while( index< d_patterns.size() ){
      Debug("matching") << "MultiEfficientPatsMatcher::reset " << index << std::endl;
      if(!d_patterns[index]->reset( d_im, qe )){
        Debug("matching") << "MultiEfficientPatsMatcher::reset fail " << index << std::endl;
        if(index == 0) return false;
        else return getNextMatchOther(qe,index-1);
      };
      ++index;
    };
    return true;
  };

  bool getNextMatchOther( QuantifiersEngine* qe, size_t index ){
    //combine child matches
    Assert( index< d_patterns.size() );
    while( true ){
      Debug("matching") << "MultiEfficientPatsMatcher::index " << index << std::endl;
      if( d_patterns[index]->getNextMatch( d_im, qe ) ){
        ++index;
        if ( index == d_patterns.size() ) return true;
        Debug("matching") << "MultiEfficientPatsMatcher::rereset " << index << std::endl;
        // If the initialization failed we come back.
        if(!d_patterns[index]->reset( d_im, qe )) --index;
      }else{
        if(index == 0){
          return false;
        }
        --index;
      }
    }
  }
public:

  bool getNextMatch( QuantifiersEngine* qe ){
    Assert( d_step == START || d_step == NEXT_OTHER || d_step == STOP );
    while(true){
      Debug("matching") << "d_step=" << d_step << " "
                        << "d_im=" << d_im << std::endl;
      switch(d_step){
      case GET_MONO_CANDIDATE:
        Assert(d_im.empty());
        if(d_eh.getNextMonoCandidate(d_mc.first)){
          d_phase_mono = true;
          d_step = RESET1;
        } else d_step = GET_MULTI_CANDIDATE;
        break;
      case GET_MULTI_CANDIDATE:
        Assert(d_im.empty());
        if(d_eh.getNextMultiCandidate(d_mc)){
          d_phase_mono = false;
          d_step = RESET1;
        } else d_step = STOP;
        break;
      case RESET1:
        if(d_direct_patterns[d_mc.first.second].reset(d_mc.first.first,d_im,qe))
          d_step = d_phase_mono ? RESET_OTHER : RESET2;
        else d_step = d_phase_mono ? GET_MONO_CANDIDATE : GET_MULTI_CANDIDATE;
        break;
      case RESET2:
        Assert(!d_phase_mono);
        if(d_direct_patterns[d_mc.second.second].reset(d_mc.second.first,d_im,qe))
          d_step = RESET_OTHER;
        else d_step = NEXT1;
        break;
      case NEXT1:
        if(d_direct_patterns[d_mc.first.second].getNextMatch(d_im,qe))
          d_step = d_phase_mono ? RESET_OTHER : RESET2;
        else d_step = d_phase_mono ? GET_MONO_CANDIDATE : GET_MULTI_CANDIDATE;
        break;
      case NEXT2:
        if(d_direct_patterns[d_mc.second.second].getNextMatch(d_im,qe))
          d_step = RESET_OTHER;
        else d_step = NEXT1;
        break;
      case RESET_OTHER:
        if(resetOther(qe)){
          d_step = NEXT_OTHER;
          return true;
        } else d_step = d_phase_mono ? NEXT1 : NEXT2;
        break;
      case NEXT_OTHER:
        if(getNextMatchOther(qe,d_patterns.size() - 1)){
          d_step = NEXT_OTHER;
          return true;
        } else d_step = d_phase_mono ? NEXT1 : NEXT2;
        break;
      case STOP:
        Assert(d_im.empty());
        return false;
      }
    }
  }

  MultiEfficientPatsMatcher(std::vector< Node > & pats, QuantifiersEngine* qe):
    d_eh(qe->getTheoryEngine()->d_context), d_step(START){
    Assert(pats.size() > 0);
    for( size_t i=0; i< pats.size(); i++ ){
      d_patterns.push_back(mkPattern(pats[i],qe));
      Assert(pats[i].getKind()==kind::APPLY_UF);
      d_direct_patterns.push_back(ApplyMatcher(pats[i],qe));
    };
    Theory* th_uf = qe->getTheoryEngine()->getTheory( theory::THEORY_UF );
    uf::InstantiatorTheoryUf* ith = (uf::InstantiatorTheoryUf*)th_uf->getInstantiator();
    ith->registerEfficientHandler(d_eh, pats);
  };
  void resetInstantiationRound( QuantifiersEngine* qe ){
    Assert(d_step == START || d_step == STOP);
    for( size_t i=0; i< d_patterns.size(); i++ ){
      d_patterns[i]->resetInstantiationRound( qe );
      d_direct_patterns[i].resetInstantiationRound( qe );
    };
    d_step = START;
    Assert(d_im.empty());
  };

  const InstMatch& getInstMatch(){return d_im;};

  int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe, int instLimit, bool addSplits );
};

int MultiEfficientPatsMatcher::addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe, int instLimit, bool addSplits ){
  //now, try to add instantiation for each match produced
  int addedLemmas = 0;
  Assert(baseMatch.empty());
  resetInstantiationRound( qe );
  while( getNextMatch( qe ) ){
    InstMatch im_copy = getInstMatch();
    //m.makeInternal( d_quantEngine->getEqualityQuery() );
    if( qe->addInstantiation( quant, im_copy, addSplits ) ){
      addedLemmas++;
      if( instLimit>0 && addedLemmas==instLimit ){
        return addedLemmas;
      }
    }
  }
  //return number of lemmas added
  return addedLemmas;
};

PatsMatcher* mkPatternsEfficient( std::vector< Node > pat, QuantifiersEngine* qe ){
  return new MultiEfficientPatsMatcher( pat, qe);
}

} /* CVC4::theory::rrinst */
} /* CVC4::theory */
} /* CVC4 */
