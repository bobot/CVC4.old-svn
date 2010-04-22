

namespace CVC4 {
namespace theory {
namespace arith {

struct IsNormalAttrID;

typedef expr::Attribute<IsNormalAttrID, bool> IsNormal;


inline bool isNormalized(TNode x){
  return x.hasAttribute(IsNormal());
}

struct NormalFormAttrID;

typedef expr::Attribute<IsNormalAttrID, Node> NormalForm;



}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

