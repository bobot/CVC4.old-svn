/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Some proof definitions
 **
 ** Some proof definitions.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_H
#define __CVC4__PROOF_H

#ifdef CVC4_PROOFS
#  define CVC4_USE_PROOFS 1
#else /* CVC4_PROOFS */
#  define CVC4_USE_PROOFS 0
#endif /* CVC4_PROOFS */

#ifdef CVC4_PROOFS
#  define IF_CVC4_SUPPORTS_PROOFS(x) x
#else /* CVC4_PROOFS */
#  define IF_CVC4_SUPPORTS_PROOFS(x)
#endif /* CVC4_PROOFS */

#define withProofs() (CVC4_USE_PROOFS && proofsOn())

#ifdef CVC4_PROOFS
#  define PROOF(x) if(proofsOn()) { x; }
#else /* CVC4_PROOFS */
#  define PROOF(x)
#endif

#endif /* __CVC4__PROOF_H */
