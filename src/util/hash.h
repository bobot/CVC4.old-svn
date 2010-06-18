/*********************                                                        */
/*! \file hash.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#ifndef __CVC4__HASH_H_
#define __CVC4__HASH_H_

#include <ext/hash_map>
namespace std { using namespace __gnu_cxx; }

namespace CVC4 {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return std::hash<const char*>()(str.c_str());
  }
};

}

#endif /* __CVC4__HASH_H_ */
