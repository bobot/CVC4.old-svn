/*********************                                                        */
/*! \file lemma_output_channel.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Mechanism for communication about new lemmas
 **
 ** This file defines an interface for use by the theory and propositional
 ** engines to communicate new lemmas to the "outside world," for example
 ** for lemma sharing between threads.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LEMMA_OUTPUT_CHANNEL_H
#define __CVC4__LEMMA_OUTPUT_CHANNEL_H

#include "expr/expr.h"

namespace CVC4 {

/**
 * This interface describes a mechanism for the propositional and theory
 * engines to communicate with the "outside world" about new lemmas being
 * discovered.
 */
class CVC4_PUBLIC LemmaOutputChannel {
public:
  /**
   * Notifies this output channel that there's a new lemma.
   * The lemma may or may not be in CNF.
   */
  virtual void notifyNewLemma(Expr lemma) = 0;
};/* class LemmaOutputChannel */

}/* CVC4 namespace */

#endif /* __CVC4__LEMMA_OUTPUT_CHANNEL_H */
