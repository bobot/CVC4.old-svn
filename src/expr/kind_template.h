/*********************                                                        */
/** kind_template.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Template for the Node kind header.
 **/

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

#include "cvc4_config.h"
#include <iostream>
#include <sstream>

namespace CVC4 {
namespace kind {

enum Kind_t {
  UNDEFINED_KIND = -1, /*! undefined */
  NULL_EXPR, /*! Null kind */
${kind_decls}
  LAST_KIND

};/* enum Kind_t */

}/* CVC4::kind namespace */

// import Kind into the "CVC4" namespace but keep the individual kind
// constants under kind::
typedef ::CVC4::kind::Kind_t Kind;

namespace kind {

inline std::ostream& operator<<(std::ostream&, CVC4::Kind) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, CVC4::Kind k) {
  using namespace CVC4::kind;

  switch(k) {

  /* special cases */
  case UNDEFINED_KIND: out << "UNDEFINED_KIND"; break;
  case NULL_EXPR: out << "NULL"; break;
${kind_printers}
  case LAST_KIND: out << "LAST_KIND"; break;
  default: out << "UNKNOWNKIND!" << int(k); break;
  }

  return out;
}

inline std::string kindToString(::CVC4::Kind k) {
  std::stringstream ss;
  ss << k;
  return ss.str();
}

struct KindHashFcn {
  static inline size_t hash(::CVC4::Kind k) { return k; }
};

}/* CVC4::kind namespace */
}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
