#ifndef __CVC4__PICKLE_H
#define __CVC4__PICKLE_H

#include <sstream>

namespace CVC4{

namespace expr {
namespace pickle {

class Pickler {
  std::ostringstream *d_s;
public:
  Pickler() {}
  Pickler(std::ostringstream *s) : d_s(s) {}
  template <typename T> void operator << (const T &b) {
    // TOADD: assert(sizeof(b) * 8 == NBITS_BLOCK);
Debug("pickle") << "<< :" << sizeof(b) << std::endl;
    d_s->write( (char *) &b, sizeof(b) );
  }
  std::ostringstream* getStream() { return d_s; }
};

void pickleNode(Pickler &p, const TNode &n);

std::string pickleTest(const TNode &n);

} /* namespace pickle */
} /* namespace expr */

} /* namespace CVC4 */

#endif /* __CVC4__PICKLE_H */
