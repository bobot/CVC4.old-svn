/*********************                                                        */
/*! \file options_handlers.h
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
 ** \brief Custom handlers and predicates for expression package options
 **
 ** Custom handlers and predicates for expression package options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__OPTIONS_HANDLERS_H
#define __CVC4__EXPR__OPTIONS_HANDLERS_H

namespace CVC4 {
namespace expr {

inline void setDefaultExprDepth(std::string option, std::string optarg) {
  int depth = atoi(optarg.c_str());

  Debug.getStream() << Expr::setdepth(depth);
  Trace.getStream() << Expr::setdepth(depth);
  Notice.getStream() << Expr::setdepth(depth);
  Chat.getStream() << Expr::setdepth(depth);
  Message.getStream() << Expr::setdepth(depth);
  Warning.getStream() << Expr::setdepth(depth);
}

inline void setPrintExprTypes(std::string option) {
  Debug.getStream() << Expr::printtypes(true);
  Trace.getStream() << Expr::printtypes(true);
  Notice.getStream() << Expr::printtypes(true);
  Chat.getStream() << Expr::printtypes(true);
  Message.getStream() << Expr::printtypes(true);
  Warning.getStream() << Expr::printtypes(true);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__OPTIONS_HANDLERS_H */
