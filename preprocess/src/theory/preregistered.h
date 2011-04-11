
#ifndef __CVC4__THEORY__PREREGISTERED__H
#define __CVC4__THEORY__PREREGISTERED_H

namespace CVC4 {
namespace theory {

struct PreRegisteredAttrTag {};
typedef expr::Attribute<PreRegisteredAttrTag, bool> PreRegistered;

}/* CVC4::theory namespace */

}/* CVC4 namespace */


#endif /* __CVC4__THEORY__PREREGISTERED_H */
