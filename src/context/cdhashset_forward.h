/*********************                                                        */
/*! \file cdhashset_forward.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the CDSet<>
 ** template
 **
 ** This is a forward declaration header to declare the CDSet<>
 ** template.  It's useful if you want to forward-declare CDSet<>
 ** without including the full cdset.h header, for example, in a
 ** public header context.
 **
 ** For CDSet<> in particular, it's difficult to forward-declare it
 ** yourself, because it has a default template argument.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONTEXT__CDSET_FORWARD_H
#define __CVC4__CONTEXT__CDSET_FORWARD_H

/// \cond internals

namespace __gnu_cxx {
  template <class Key> struct hash;
}/* __gnu_cxx namespace */

namespace CVC4 {
  namespace context {
    template <class V, class HashFcn = __gnu_cxx::hash<V> >
    class CDHashSet;
  }/* CVC4::context namespace */
}/* CVC4 namespace */

/// \endcond

#endif /* __CVC4__CONTEXT__CDSET_FORWARD_H */
