/*********************                                                        */
/*! \file swig.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Common swig checks and definitions
 **
 ** Common swig checks and definitions, when generating swig interfaces.
 **/

#ifndef __CVC4__BINDINGS__SWIG_H
#define __CVC4__BINDINGS__SWIG_H

#ifndef SWIG
#  error This file should only be included when generating swig interfaces.
#endif /* SWIG */

#if !defined(SWIG_VERSION) || SWIG_VERSION < 0x020000
#  error CVC4 bindings require swig version 2.0.0 or later, sorry.
#endif /* SWIG_VERSION */

%import "cvc4_public.h"
%import "util/tls.h"

// swig doesn't like the __thread storage class...
#define __thread
// ...or GCC attributes
#define __attribute__(x)

#endif /* __CVC4__BINDINGS__SWIG_H */
