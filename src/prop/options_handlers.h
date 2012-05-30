/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP__OPTIONS_HANDLERS_H
#define __CVC4__PROP__OPTIONS_HANDLERS_H

#include "prop/sat_solver_factory.h"
#include <string>
#include <vector>

namespace CVC4 {
namespace prop {

inline void showSatSolvers(std::string option) {
  std::vector<std::string> solvers;
  SatSolverFactory::getSolverIds(solvers);
  printf("Available SAT solvers: ");
  for (unsigned i = 0; i < solvers.size(); ++ i) {
    if (i > 0) {
      printf(", ");
    }
    printf("%s", solvers[i].c_str());
  }
  printf("\n");
  exit(0);
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP__OPTIONS_HANDLERS_H */
