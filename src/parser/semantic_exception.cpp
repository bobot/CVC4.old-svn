/*
 * semantic_exception.cpp
 *
 *  Created on: Feb 24, 2010
 *      Author: chris
 */

#include "semantic_exception.h"

namespace CVC4 {
namespace parser {

SemanticException::SemanticException() {
}
SemanticException::SemanticException(const std::string& s) :
  Exception(s) {
}
SemanticException::SemanticException(const std::string& s,
                                     const std::string& filename, int line,
                                     int column) :
  Exception(s), d_filename(filename), d_line(line), d_column(column) {
}
}
}

