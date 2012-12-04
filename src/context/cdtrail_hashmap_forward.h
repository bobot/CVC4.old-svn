/*********************                                                        */
/*! \file cdhashmap_forward.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the CDMap<>
 ** template
 **
 ** This is a forward declaration header to declare the CDMap<>
 ** template.  It's useful if you want to forward-declare CDMap<>
 ** without including the full cdmap.h header, for example, in a
 ** public header context.
 **
 ** For CDMap<> in particular, it's difficult to forward-declare it
 ** yourself, because it has a default template argument.
 **/

#include "cvc4_public.h"

#pragma once

namespace __gnu_cxx {
  template <class Key> struct hash;
}/* __gnu_cxx namespace */

namespace CVC4 {
  namespace context {
    template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
    class CDTrailHashMap;
  }/* CVC4::context namespace */
}/* CVC4 namespace */

