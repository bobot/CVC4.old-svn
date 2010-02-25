/* Copy-and-pasted from ANTLR's RecognitionException
 *
 * Copyright (c) 2003-2008, Terence Parr
 * All rights reserved.
 * */

#ifndef __CVC4__PARSER__SEMANTIC_EXCEPTION_H
#define __CVC4__PARSER__SEMANTIC_EXCEPTION_H

#include "util/exception.h"

namespace CVC4 {
namespace parser {

class SemanticException : public Exception {
public:
  SemanticException();
  SemanticException(const std::string& s);
  SemanticException(const std::string& s, const std::string& filename,
                    int line, int column);

  ~SemanticException() {
  }

  std::string getFilename() const {
    return d_filename;
  }

  int getLine() const {
    return d_line;
  }

  int getColumn() const {
    return d_column;
  }

protected:
  std::string d_filename;
  int d_line;
  int d_column;
};

}
}

#endif
