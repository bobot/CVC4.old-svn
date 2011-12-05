/*********************                                                        */
/*! \file bitblast_strategies.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of bitblasting functions for various operators. 
 **
 ** Implementation of bitblasting functions for various operators. 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLAST__STRATEGIES_H
#define __CVC4__BITBLAST__STRATEGIES_H


#include "expr/node.h"
#include "bv_solver_types.h"

namespace CVC4 {
namespace theory {
namespace bv {

class Bitblaster;


typedef std::vector<SatLit>    Bits; 


/** 
 * Default Atom Bitblasting strategies: 
 * 
 * @param node the atom to be bitblasted
 * @param markerLit the marker literal corresponding to the atom
 * @param bb the bitblaster
 */

void UndefinedAtomBBStrategy (TNode node, SatVar markerLit, Bitblaster* bb);                               
void DefaultEqBB(TNode node, SatVar markerLit, Bitblaster* bb);

void DefaultUltBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultUleBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultUgtBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultUgeBB(TNode node, SatVar markerLit, Bitblaster* bb);

void DefaultSltBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultSleBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultSgtBB(TNode node, SatVar markerLit, Bitblaster* bb);
void DefaultSgeBB(TNode node, SatVar markerLit, Bitblaster* bb);




/** 
 * Default Term Bitblasting strategies
 * 
 * @param node the term to be bitblasted
 * @param bb the bitblaster in which the clauses are added
 * 
 * @return the bits representing the new term 
 */

Bits* UndefinedTermBBStrategy(TNode node, Bitblaster* bb); 

Bits* DefaultVarBB         (TNode node, Bitblaster* bb);
Bits* DefaultConstBB       (TNode node, Bitblaster* bb);
Bits* DefaultNotBB         (TNode node, Bitblaster* bb);
Bits* DefaultConcatBB      (TNode node, Bitblaster* bb);
Bits* DefaultAndBB         (TNode node, Bitblaster* bb);
Bits* DefaultOrBB          (TNode node, Bitblaster* bb);
Bits* DefaultXorBB         (TNode node, Bitblaster* bb);
Bits* DefaultNandBB        (TNode node, Bitblaster* bb);
Bits* DefaultNorBB         (TNode node, Bitblaster* bb);
Bits* DefaultCompBB        (TNode node, Bitblaster* bb);
Bits* DefaultMultBB        (TNode node, Bitblaster* bb);
Bits* DefaultPlusBB        (TNode node, Bitblaster* bb);
Bits* DefaultSubBB         (TNode node, Bitblaster* bb);
Bits* DefaultNegBB         (TNode node, Bitblaster* bb);
Bits* DefaultUdivBB        (TNode node, Bitblaster* bb);
Bits* DefaultUremBB        (TNode node, Bitblaster* bb);
Bits* DefaultSdivBB        (TNode node, Bitblaster* bb);
Bits* DefaultSremBB        (TNode node, Bitblaster* bb);
Bits* DefaultSmodBB        (TNode node, Bitblaster* bb);
Bits* DefaultShlBB         (TNode node, Bitblaster* bb);
Bits* DefaultLshrBB        (TNode node, Bitblaster* bb);
Bits* DefaultAshrBB        (TNode node, Bitblaster* bb);
Bits* DefaultExtractBB     (TNode node, Bitblaster* bb);
Bits* DefaultRepeatBB      (TNode node, Bitblaster* bb);
Bits* DefaultZeroExtendBB  (TNode node, Bitblaster* bb);
Bits* DefaultSignExtendBB  (TNode node, Bitblaster* bb);
Bits* DefaultRotateRightBB (TNode node, Bitblaster* bb);
Bits* DefaultRotateLeftBB  (TNode node, Bitblaster* bb);


}
}
}

#endif
