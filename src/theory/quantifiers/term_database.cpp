/*********************                                                        */
/*! \file term_database.cpp
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
 ** \brief Implementation of term databse class
 **/

 #include "theory/quantifiers/term_database.h"
 #include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

 bool TermArgTrie::addTerm2( QuantifiersEngine* qe, Node n, int argIndex ){
   if( argIndex<(int)n.getNumChildren() ){
     Node r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
     std::map< Node, TermArgTrie >::iterator it = d_data.find( r );
     if( it==d_data.end() ){
       d_data[r].addTerm2( qe, n, argIndex+1 );
       return true;
     }else{
       return it->second.addTerm2( qe, n, argIndex+1 );
     }
   }else{
     //store n in d_data (this should be interpretted as the "data" and not as a reference to a child)
     d_data[n].d_data.clear();
     return false;
   }
 }

 void TermDb::addTerm( Node n, std::vector< Node >& added, bool withinQuant ){
   //don't add terms in quantifier bodies
   if( !withinQuant || Options::current()->registerQuantBodyTerms ){
     if( d_processed.find( n )==d_processed.end() ){
       d_processed[n] = true;
       //if this is an atomic trigger, consider adding it
       if( Trigger::isAtomicTrigger( n ) ){
         if( !n.hasAttribute(InstConstantAttribute()) ){
           Debug("term-db") << "register trigger term " << n << std::endl;
           //Notice() << "register trigger term " << n << std::endl;
           Node op = n.getOperator();
           d_op_map[op].push_back( n );
           d_type_map[ n.getType() ].push_back( n );
           added.push_back( n );

           uf::InstantiatorTheoryUf* d_ith = (uf::InstantiatorTheoryUf*)d_quantEngine->getInstantiator( THEORY_UF );
           for( int i=0; i<(int)n.getNumChildren(); i++ ){
             addTerm( n[i], added, withinQuant );
             if( Options::current()->efficientEMatching ){
               if( d_parents[n[i]][op].empty() ){
                 //must add parent to equivalence class info
                 Node nir = d_ith->getRepresentative( n[i] );
                 uf::EqClassInfo* eci_nir = d_ith->getEquivalenceClassInfo( nir );
                 if( eci_nir ){
                   eci_nir->d_pfuns[ op ] = true;
                 }
               }
               //add to parent structure
               if( std::find( d_parents[n[i]][op][i].begin(), d_parents[n[i]][op][i].end(), n )==d_parents[n[i]][op][i].end() ){
                 d_parents[n[i]][op][i].push_back( n );
               }
             }
           }
           if( Options::current()->efficientEMatching ){
             //new term, add n to candidate generators
             for( int i=0; i<(int)d_ith->d_cand_gens[op].size(); i++ ){
               d_ith->d_cand_gens[op][i]->addCandidate( n );
             }
           }
           if( Options::current()->eagerInstQuant ){
             if( !n.hasAttribute(InstLevelAttribute()) && n.getAttribute(InstLevelAttribute())==0 ){
               int addedLemmas = 0;
               for( int i=0; i<(int)d_ith->d_op_triggers[op].size(); i++ ){
                 addedLemmas += d_ith->d_op_triggers[op][i]->addTerm( n );
               }
               //Message() << "Terms, added lemmas: " << addedLemmas << std::endl;
               d_quantEngine->flushLemmas( &d_quantEngine->getTheoryEngine()->getTheory( THEORY_QUANTIFIERS )->getOutputChannel() );
             }
           }
         }
       }
       for( int i=0; i<(int)n.getNumChildren(); i++ ){
         addTerm( n[i], added, withinQuant );
       }
     }
   }
 }

 void TermDb::reset( Theory::Effort effort ){
   int nonCongruentCount = 0;
   int congruentCount = 0;
   int alreadyCongruentCount = 0;
   //rebuild d_func/pred_map_trie for each operation, this will calculate all congruent terms
   for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
     if( !it->second.empty() ){
       if( it->second[0].getType()==NodeManager::currentNM()->booleanType() ){
         d_pred_map_trie[ 0 ][ it->first ].d_data.clear();
         d_pred_map_trie[ 1 ][ it->first ].d_data.clear();
       }else{
         d_func_map_trie[ it->first ].d_data.clear();
         for( int i=0; i<(int)it->second.size(); i++ ){
           Node n = it->second[i];
           if( !n.getAttribute(NoMatchAttribute()) ){
             if( !d_func_map_trie[ it->first ].addTerm( d_quantEngine, n ) ){
               NoMatchAttribute nma;
               n.setAttribute(nma,true);
               congruentCount++;
             }else{
               nonCongruentCount++;
             }
           }else{
             congruentCount++;
             alreadyCongruentCount++;
           }
         }
       }
     }
   }
   for( int i=0; i<2; i++ ){
     Node n = NodeManager::currentNM()->mkConst( i==1 );
     eq::EqClassIterator eqc( d_quantEngine->getEqualityQuery()->getRepresentative( n ),
                               ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
     while( !eqc.isFinished() ){
       Node en = (*eqc);
       if( en.getKind()==APPLY_UF && !en.hasAttribute(InstConstantAttribute()) ){
         if( !en.getAttribute(NoMatchAttribute()) ){
           Node op = en.getOperator();
           if( !d_pred_map_trie[i][op].addTerm( d_quantEngine, en ) ){
             NoMatchAttribute nma;
             en.setAttribute(nma,true);
             congruentCount++;
           }else{
             nonCongruentCount++;
           }
         }else{
           alreadyCongruentCount++;
         }
       }
       ++eqc;
     }
   }
   Debug("term-db-cong") << "TermDb: Reset" << std::endl;
   Debug("term-db-cong") << "Congruent/Non-Congruent = ";
   Debug("term-db-cong") << congruentCount << "(" << alreadyCongruentCount << ") / " << nonCongruentCount << std::endl;
}
