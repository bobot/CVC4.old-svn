/*
 * smt.cpp
 *
 *  Created on: Feb 26, 2010
 *      Author: chris
 */
#ifndef __CVC4__PARSER__SMT_PARSER_H
#define __CVC4__PARSER__SMT_PARSER_H

#include "util/Assert.h"
#include "parser/pegtl_parser.h"

/*
namespace pegtl {
template< typename Location >
struct file_input;
class ascii_location;
}
*/

namespace CVC4 {

class Command;
class Expr;

namespace parser {

class SmtParser : public PegtlParser {
public:
  /**
   * Create a parser for the given input file, using memory-mapped input.
   *
   * @param filename the file to parse
   */
  SmtParser(std::string filename):
    d_filename( filename ) {
  }


  /**
   * Create a parser for the given input stream
   *
   * @param input the input stream to parse
   * @param filename the name of the file backing the input stream
   */
//  SmtParser(std::istream& input, std::string filename);


  /**
   * Parse a command.
   * @return a command
   */
  Command* parseCommand();

  /**
   * Parse an expression.
   * @return the expression
   */
  Expr parseExpr();

private:
  std::string d_filename;
//  pegtl::file_input< pegtl::ascii_location >* d_input;
};
}
}
#endif // __CVC4__PARSER__SMT_PARSER_H
