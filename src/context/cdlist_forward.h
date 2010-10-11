/*********************                                                        */
/*! \file cdlist_forward.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the
 ** CDList<> template
 **
 ** This is a forward declaration header to declare the CDList<>
 ** template.  It's useful if you want to forward-declare CDList<>
 ** without including the full cdlist.h header, for example, in a
 ** public header context.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONTEXT__CDLIST_FORWARD_H
#define __CVC4__CONTEXT__CDLIST_FORWARD_H

#include <memory>

namespace __gnu_cxx {
  template <class Key> class hash;
}/* __gnu_cxx namespace */

namespace CVC4 {
  namespace context {
    template <class T, class Allocator = std::allocator<T> >
    class CDList;

    template <class T>
    class CDList<T, ContextMemoryAllocator<T> >;
  }/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDLIST_FORWARD_H */
