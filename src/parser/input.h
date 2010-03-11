/*********************                                                        */
/** parser.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser abstraction.
 **/

#ifndef __CVC4__PARSER__PARSER_H
#define __CVC4__PARSER__PARSER_H

#include <string>
#include <iostream>

#include "cvc4_config.h"
#include "expr/node.h"
#include "expr/kind.h"
#include "parser/parser_exception.h"
#include "parser/parser_options.h"
#include "parser/symbol_table.h"
#include "util/Assert.h"

namespace CVC4 {

// Forward declarations
class BooleanType;
class NodeManager;
class Command;
class Expr;
class FunctionType;
class KindType;
class Type;

namespace parser {

/** Types of check for the symols */
enum DeclarationCheck {
  /** Enforce that the symbol has been declared */
  CHECK_DECLARED,
  /** Enforce that the symbol has not been declared */
  CHECK_UNDECLARED,
  /** Don't check anything */
  CHECK_NONE
};

/** Returns a string representation of the given object (for
    debugging). */
inline std::string toString(DeclarationCheck check) {
  switch(check) {
  case CHECK_NONE: return "CHECK_NONE";
  case CHECK_DECLARED:  return "CHECK_DECLARED";
  case CHECK_UNDECLARED: return "CHECK_UNDECLARED";
  default: Unreachable();
  }
}

/**
 * Types of symbols. Used to define namespaces.
 */
enum SymbolType {
  /** Variables */
  SYM_VARIABLE,
  /** Functions */
  SYM_FUNCTION,
  /** Sorts */
  SYM_SORT
};

/** Returns a string representation of the given object (for
    debugging). */
inline std::string toString(SymbolType type) {
  switch(type) {
  case SYM_VARIABLE: return "SYM_VARIABLE";
  case SYM_FUNCTION: return "SYM_FUNCTION";
  case SYM_SORT: return "SYM_SORT";
  default: Unreachable();
  }
}

/**
 * The parser. The parser should be obtained by calling the static methods
 * getNewParser, and should be deleted when done.
 *
 * This class includes convenience methods for interacting with the NodeManager
 * from within a grammar.
 */
class CVC4_PUBLIC Input {

public:
  /** Create a parser for the given file.
    *
    * @param nodeManager the NodeManager for creating expressions from the input
    * @param lang the input language
    * @param filename the input filename
    */
   static Input* newFileInput(ExprManager* exprManager, InputLanguage lang, const std::string& filename, bool useMmap=false);

  /** Create a parser for the given input stream.
   *
   * @param nodeManager the NodeManager for creating expressions from the input
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  //static Input* getNewInput(NodeManager* nodeManager, InputLanguage lang, std::istream& input, const std::string& name);

  /** Create a parser for the given input string
   *
   * @param nodeManager the NodeManager for creating nodeessions from the input
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringInput(ExprManager* exprManager, InputLanguage lang, const std::string& input, const std::string& name);

  /**
   * Destructor.
   */
  ~Input();

  /**
   * Parse the next command of the input. If EOF is encountered a EmptyCommand
   * is returned and done flag is set.
   */
  Command* parseNextCommand() throw(ParserException);

  /**
   * Parse the next nodeession of the stream. If EOF is encountered a null
   * nodeession is returned and done flag is set.
   * @return the parsed nodeession
   */
  Expr parseNextExpression() throw(ParserException);

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  bool done() const;

  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks();

  /** Get the name of the input file. */
  inline const std::string getFilename() {
    return d_filename;
  }

  /**
     * Returns a variable, given a name and a type.
     * @param var_name the name of the variable
     * @return the variable nodeession
     */
    Node getVariable(const std::string& var_name);

    /**
     * Returns a function, given a name and a type.
     * @param name the name of the function
     * @return the function nodeession
     */
    Node getFunction(const std::string& name);

    /**
     * Returns a sort, given a name
     */
    const Type* getSort(const std::string& sort_name);

    /**
     * Checks if a symbol has been declared.
     * @param name the symbol name
     * @param type the symbol type
     * @return true iff the symbol has been declared with the given type
     */
    bool isDeclared(const std::string& name, SymbolType type = SYM_VARIABLE);

    /**
     * Checks if the declaration policy we want to enforce holds
     * for the given symbol.
     * @param name the symbol to check
     * @param check the kind of check to perform
     * @param type the type of the symbol
     * @throws ParserException if checks are enabled and the check fails
     */
    void checkDeclaration(const std::string& name,
                          DeclarationCheck check,
                          SymbolType type = SYM_VARIABLE)
      throw (ParserException);

    /**
     * Checks whether the given name is bound to a function.
     * @param name the name to check
     * @throws ParserException if checks are enabled and name is not bound to a function
     */
    void checkFunction(const std::string& name) throw (ParserException);

    /**
     * Check that <code>kind</code> can accept <code>numArgs</codes> arguments.
     * @param kind the built-in operator to check
     * @param numArgs the number of actual arguments
     * @throws ParserException if checks are enabled and the operator <code>kind</code> cannot be
     * applied to <code>numArgs</code> arguments.
     */
    void checkArity(Kind kind, unsigned int numArgs) throw (ParserException);

    /**
     * Returns the type for the variable with the given name.
     * @param name the symbol to lookup
     * @param type the (namespace) type of the symbol
     */
    const Type* getType(const std::string& var_name,
                        SymbolType type = SYM_VARIABLE);

    /**
     * Returns the true nodeession.
     * @return the true nodeession
     */
    Node getTrueNode() const;

    /**
     * Returns the false nodeession.
     * @return the false nodeession
     */
    Node getFalseNode() const;

    /**
     * Creates a new unary CVC4 nodeession using the nodeession manager.
     * @param kind the kind of the nodeession
     * @param child the child
     * @return the new unary nodeession
     */
    Node mkNode(Kind kind, TNode child);

    /**
     * Creates a new binary CVC4 expression using the expression manager.
     * @param kind the kind of the expression
     * @param child1 the first child
     * @param child2 the second child
     * @return the new binary expression
     */
    Node mkNode(Kind kind, TNode child_1, TNode child_2);

    /**
     * Creates a new ternary CVC4 expression using the expression manager.
     * @param kind the kind of the expression
     * @param child_1 the first child
     * @param child_2 the second child
     * @param child_3
     * @return the new ternary expression
     */
    Node mkNode(Kind kind, TNode child_1, TNode child_2,
                TNode child_3);

    /**
     * Creates a new CVC4 expression using the expression manager.
     * @param kind the kind of the expression
     * @param children the children of the expression
     */
    Node mkNode(Kind kind, const std::vector<Node>& children);

    /** Create a new CVC4 variable expression of the given type. */
    Node mkVar(const std::string& name, const Type* type);

    /** Create a set of new CVC4 variable expressions of the given
        type. */
    const std::vector<Node>
    mkVars(const std::vector<std::string> names,
           const Type* type);

    /** Create a new variable definition (e.g., from a let binding). */
    void defineVar(const std::string& name, const Node& val);
    /** Remove a variable definition (e.g., from a let binding). */
    void undefineVar(const std::string& name);

    Expr mkDistinct(const std::vector<Node>& args);

    const Expr toExpr(Node node);

    /** Returns a function type over the given domain and range types. */
    const Type* functionType(const Type* domain, const Type* range);

    /** Returns a function type over the given types. argTypes must be
        non-empty. */
    const Type* functionType(const std::vector<const Type*>& argTypes,
                             const Type* rangeType);

    /**
     * Returns a function type over the given types. If types has only
     * one element, then the type is just types[0].
     *
     * @param types a non-empty list of input and output types.
     */
    const Type* functionType(const std::vector<const Type*>& types);

    /**
     * Returns a predicate type over the given sorts. If sorts is empty,
     * then the type is just BOOLEAN.

     * @param sorts a list of input types
     */
    const Type* predicateType(const std::vector<const Type*>& sorts);

    /**
     * Creates a new sort with the given name.
     */
    const Type* newSort(const std::string& name);

    /**
     * Creates a new sorts with the given names.
     */
    const std::vector<const Type*>
    newSorts(const std::vector<std::string>& names);

    /** Is the symbol bound to a boolean variable? */
    bool isBoolean(const std::string& name);

    /** Is the symbol bound to a function? */
    bool isFunction(const std::string& name);

    /** Is the symbol bound to a predicate? */
    bool isPredicate(const std::string& name);

    /** Returns the boolean type. */
    const BooleanType* booleanType();

    /** Returns the kind type (i.e., the type of types). */
    const KindType* kindType();

    /** Returns the minimum arity of the given kind. */
    static unsigned int minArity(Kind kind);

    /** Returns the maximum arity of the given kind. */
    static unsigned int maxArity(Kind kind);

    virtual void parseError(const std::string& msg) throw (ParserException) = 0;

protected:
    virtual Command* doParseCommand() throw(ParserException) = 0;
    virtual Node doParseExpr() throw(ParserException) = 0;

    /**
     * Create a new parser for the given file.
     * @param nodeManager the ExprManager to use
     * @param filename the path of the file to parse
     */
    Input(ExprManager* exprManager, const std::string& filename);

private:

  /** Sets the done flag */
  void setDone(bool done = true);

  /** Lookup a symbol in the given namespace. */
  Node getSymbol(const std::string& var_name, SymbolType type);

  /** Whether to de-allocate the input */
//  bool d_deleteInput;

  /** The nodeession manager */
  NodeManager* d_nodeManager;
  ExprManager* d_exprManager;
  NodeManagerScope d_nodeManagerScope;

  /** The symbol table lookup */
  SymbolTable<Node> d_varSymbolTable;

  /** The sort table */
  SymbolTable<const Type*> d_sortTable;

  /** The name of the input file. */
  std::string d_filename;

  /** Are we done */
  bool d_done;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;

}; // end of class Input

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
