/*********************                                                        */
/*! \file tptp.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definitions of TPTP constants.
 **
 ** Definitions of TPTP constants.
 **/

#include "expr/type.h"
#include "parser/parser.h"
#include "parser/smt/smt.h"
#include "parser/tptp/tptp.h"
#include "util/options.h"
#include "parser/antlr_input.h"

namespace CVC4 {
namespace parser {

Tptp::Tptp(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly), d_fof_conjecture(false) {
  addTheory(Tptp::THEORY_CORE);
  /* Try to find TPTP dir */
  // From tptp4x FileUtilities
  //----Try the TPTP directory, and TPTP variations
    char* home = getenv("TPTP");
    if (home == NULL) {
        home = getenv("TPTP_HOME");
// //----If no TPTP_HOME, try the tptp user (aaargh)
//         if (home == NULL && (PasswdEntry = getpwnam("tptp")) != NULL) {
//             home = PasswdEntry->pw_dir;
//         }
//----Now look in the TPTP directory from there
        if (home != NULL) {
          d_tptpDir = home;
          d_tptpDir.append("/TPTP/");
        }
    } else {
      d_tptpDir = home;
      //add trailing "/"
      if( d_tptpDir[d_tptpDir.size() - 1] != '/'){
        d_tptpDir.append("/");
      }
    }
}

void Tptp::addTheory(Theory theory) {
  ExprManager * em = getExprManager();
  switch(theory) {
  case THEORY_CORE:
    //TPTP (CNF and FOF) is unsorted so we define this common type
    {
      std::string d_unsorted_name = "$$unsorted";
      d_unsorted = em->mkSort(d_unsorted_name);
      preemptCommand( new DeclareTypeCommand(d_unsorted_name, 0, d_unsorted) );
    }
    {
      Type t;
      //Conversion from rational to unsorted
      t = em->mkFunctionType(em->realType(), d_unsorted);
      d_rtu_op = em->mkVar("$$rtu",t);
      //Conversion from string to unsorted
      t = em->mkFunctionType(em->stringType(), d_unsorted);
      d_stu_op = em->mkVar("$$stu",t);
      //Conversion from unsorted to rational
      t = em->mkFunctionType(d_unsorted, em->realType());
      d_utr_op = em->mkVar("$$utr",t);
      //Conversion from unsorted to string
      t = em->mkFunctionType(d_unsorted, em->stringType());
      d_uts_op = em->mkVar("$$uts",t);
    }
    // propositionnal
    defineType("Bool", em->booleanType());
    defineVar("$true", em->mkConst(true));
    defineVar("$false", em->mkConst(false));
    addOperator(kind::AND);
    addOperator(kind::EQUAL);
    addOperator(kind::IFF);
    addOperator(kind::IMPLIES);
    //addOperator(kind::ITE); //only for tff thf
    addOperator(kind::NOT);
    addOperator(kind::OR);
    addOperator(kind::XOR);
    addOperator(kind::APPLY_UF);
    //Add quantifiers?
    break;

  default:
    Unhandled(theory);
  }
}


/* The include are managed in the lexer but called in the parser */
// Inspired by From http://www.antlr.org/api/C/interop.html

void Tptp::includeFile(std::string fileName){
  if( !d_tptpDir.empty() ){
    fileName = d_tptpDir + fileName;
  } else {
    parseError("Command 'include' found but the TPTP directory is not specified (environnement variable TPTP)");
  };
  Debug("parser") << "Including " << fileName << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) fileName.c_str());
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) fileName.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  if( in == NULL ) {
    parseError("Couldn't open file: " + fileName);
  }
  // Get the lexer
  AntlrInput * ai = static_cast<AntlrInput *>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();
  // Samething than the predefined PUSHSTREAM(in);
  lexer->pushCharStream(lexer,in);
  // restart it
  //lexer->rec->state->tokenStartCharIndex	= -10;
  //lexer->emit(lexer);

  // Note that the input stream is not closed when it EOFs, I don't bother
  // to do it here, but it is up to you to track streams created like this
  // and destroy them when the whole parse session is complete. Remember that you
  // don't want to do this until all tokens have been manipulated all the way through
  // your tree parsers etc as the token does not store the text it just refers
  // back to the input stream and trying to get the text for it will abort if you
  // close the input stream too early.
  //
}

void Tptp::endFile(){
  Options::tptp_fof_conjecture = d_fof_conjecture;
  preemptCommand(new CheckSatCommand(getExprManager()->mkConst(bool(true))));
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
