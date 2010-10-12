/*
 * smt.cpp
 *
 *  Created on: Feb 26, 2010
 *      Author: chris
 */

#include <pegtl.hh>

#include "smt_parser.h"

namespace CVC4 {
namespace parser {

using namespace pegtl;
using namespace pegtl::ascii;

struct comment : ifmust< one< ';' >, until< eol > > {};

struct spacing : sor< comment, space > {};

// symbols
struct lparen : padr< one < '(' >, spacing > {};
struct rparen : padr< one < ')' >, spacing > {};

template< typename Token >
struct keywordTok : padr< Token, spacing > {};

// keywords
struct andTok : keywordTok< string<a,n,d> > {};
struct falseTok: keywordTok< string<f,a,l,s,e> > {};
struct orTok : keywordTok< string<o,r> > {};
struct notTok : keywordTok< string<n,o,t> > {};
struct trueTok : keywordTok< string<t,r,u,e> > {};
struct benchmarkTok : keywordTok< string<b,e,n,c,h,m,a,r,k> > {};

template< typename Token >
struct attrTok : keywordTok< seq< one<':'>, Token > > {};

struct assumptionTok : attrTok< string<a,s,s,u,m,p,t,i,o,n> > {};
struct extrapredsTok : attrTok< string<e,x,t,r,a,p,r,e,d,s> > {};
struct formulaTok : attrTok< string<f,o,r,m,u,l,a> > {};
struct logicTok : attrTok< string<l,o,g,i,c> > {};
struct statusTok : attrTok< string<s,t,a,t,u,s> > {};
struct attrId : attrTok< identifier > {};

struct variable : padr< identifier, spacing > {};

struct builtin
: sor< andTok,
       orTok,
       notTok > {};

struct annotatedFormula;

struct annotatedFormulaList
: plus< annotatedFormula > {};

struct applyOp
: seq< lparen,
       builtin,
       annotatedFormulaList,
       rparen > {};

struct annotatedFormula
: sor< applyOp,
       variable,
       trueTok,
       falseTok > {};

struct predicateDecl
: seq< lparen, plus< variable >, rparen > {} ;

struct predicateList
: seq< lparen, plus< predicateDecl >, rparen > {};

struct annotation
: padr< seq< attrId, ifmust< one< '{' >, until< one< '}' > > > >, spacing > {};

struct benchmarkAttribute
: sor< seq< logicTok, variable >,
       seq< assumptionTok, annotatedFormula >,
       seq< formulaTok, annotatedFormula >,
       seq< statusTok, variable >,
       seq< extrapredsTok, predicateList >,
       annotation > {};


struct benchmark
: seq< lparen,
       benchmarkTok,
       variable,
       star< benchmarkAttribute >,
       rparen > { };


struct command : seq< pad< benchmark, spacing >, eof > {};
struct expr : seq< pad< annotatedFormula, spacing >, eof > {};

/**
 * Parse a command.
 * @return a command
 */
Command* SmtParser::parseCommand() {
  dummy_parse_file< command >( d_filename );
  return NULL;
}

/**
 * Parse an expression.
 * @return the expression
 */
Expr SmtParser::parseExpr() {
  basic_parse_file< expr >( d_filename );
  return Expr();
}


}
}
