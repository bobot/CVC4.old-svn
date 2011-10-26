/*********************                                                        */
/*! \file antlr_input.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A super-class for ANTLR-generated input language parsers.
 **
 ** A super-class for ANTLR-generated input language parsers
 **/

#include <limits.h>
#include <antlr3.h>
#include <stdint.h>

#include "antlr_input.h"
#include "input.h"
#include "bounded_token_buffer.h"
#include "bounded_token_factory.h"
#include "memory_mapped_input_buffer.h"
#include "parser_exception.h"
#include "parser.h"

#include "expr/command.h"
#include "expr/type.h"
#include "parser/cvc/cvc_input.h"
#include "parser/smt/smt_input.h"
#include "parser/smt2/smt2_input.h"
#include "util/output.h"
#include "util/Assert.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

typedef struct ANTLR3_LINE_BUFFERED_INPUT_STREAM {
  ANTLR3_INPUT_STREAM antlr;
  std::istream* in;
} *pANTLR3_LINE_BUFFERED_INPUT_STREAM;

AntlrInputStream::AntlrInputStream(std::string name, 
                                   pANTLR3_INPUT_STREAM input,
                                   bool fileIsTemporary) :
  InputStream(name,fileIsTemporary),
  d_input(input) {
  AlwaysAssert( input != NULL );
}

AntlrInputStream::~AntlrInputStream() {
  d_input->free(d_input);
}

pANTLR3_INPUT_STREAM AntlrInputStream::getAntlr3InputStream() const {
  return d_input;
}

AntlrInputStream*
AntlrInputStream::newFileInputStream(const std::string& name,
                                     bool useMmap)
  throw (InputStreamException, AssertionException) {
  pANTLR3_INPUT_STREAM input = NULL;
  if( useMmap ) {
    input = MemoryMappedInputBufferNew(name);
  } else {
    // libantlr3c v3.2 isn't source-compatible with v3.4
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
    input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) name.c_str());
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
    input = antlr3FileStreamNew((pANTLR3_UINT8) name.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  }
  if( input == NULL ) {
    throw InputStreamException("Couldn't open file: " + name);
  }
  return new AntlrInputStream( name, input );
}

static  pANTLR3_INPUT_STREAM    antlr3CreateLineBufferedStream(std::istream& in);

static void 
setupInputStream(pANTLR3_INPUT_STREAM input)
{
    ANTLR3_BOOLEAN  isBigEndian;

    // Used to determine the endianness of the machine we are currently
    // running on.
    //
    ANTLR3_UINT16 bomTest = 0xFEFF;
    
    // What endianess is the machine we are running on? If the incoming
    // encoding endianess is the same as this machine's natural byte order
    // then we can use more efficient API calls.
    //
    if  (*((pANTLR3_UINT8)(&bomTest)) == 0xFE)
    {
        isBigEndian = ANTLR3_TRUE;
    }
    else
    {
        isBigEndian = ANTLR3_FALSE;
    }

    // What encoding did the user tell us {s}he thought it was? I am going
    // to get sick of the questions on antlr-interest, I know I am.
    //
    switch  (input->encoding)
    {
        case    ANTLR3_ENC_UTF8:

            // See if there is a BOM at the start of this UTF-8 sequence
            // and just eat it if there is. Windows .TXT files have this for instance
            // as it identifies UTF-8 even though it is of no consequence for byte order
            // as UTF-8 does not have a byte order.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xEF
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xBB
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+2))    == 0xBF
                )
            {
                // The UTF8 BOM is present so skip it
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 3);
            }

            // Install the UTF8 input routines
            //
            antlr3UTF8SetupStream(input);
            break;

        case    ANTLR3_ENC_UTF16:

            // See if there is a BOM at the start of the input. If not then
            // we assume that the byte order is the natural order of this
            // machine (or it is really UCS2). If there is a BOM we determine if the encoding
            // is the same as the natural order of this machine.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFE
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFF
                )
            {
                // BOM Present, indicates Big Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 2);

                antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_TRUE);
            }
            else if  (      (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFF
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFE
                )
            {
                // BOM present, indicates Little Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 2);

                antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_FALSE);
            }
            else
            {
                // No BOM present, assume local computer byte order
                //
                antlr3UTF16SetupStream(input, isBigEndian, isBigEndian);
            }
            break;

        case    ANTLR3_ENC_UTF32:

            // See if there is a BOM at the start of the input. If not then
            // we assume that the byte order is the natural order of this
            // machine. If there is we determine if the encoding
            // is the same as the natural order of this machine.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0x00
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+2))    == 0xFE
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+3))    == 0xFF
                )
            {
                // BOM Present, indicates Big Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 4);

                antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_TRUE);
            }
            else if  (      (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFF
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFE
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                )
            {
                // BOM present, indicates Little Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 4);

                antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_FALSE);
            }
            else
            {
                // No BOM present, assume local computer byte order
                //
                antlr3UTF32SetupStream(input, isBigEndian, isBigEndian);
            }
            break;

        case    ANTLR3_ENC_UTF16BE:

            // Encoding is definately Big Endian with no BOM
            //
            antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_TRUE);
            break;

        case    ANTLR3_ENC_UTF16LE:

            // Encoding is definately Little Endian with no BOM
            //
            antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_FALSE);
            break;

        case    ANTLR3_ENC_UTF32BE:

            // Encoding is definately Big Endian with no BOM
            //
            antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_TRUE);
            break;

        case    ANTLR3_ENC_UTF32LE:

            // Encoding is definately Little Endian with no BOM
            //
            antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_FALSE);
            break;

        case    ANTLR3_ENC_EBCDIC:

            // EBCDIC is basically the same as ASCII but with an on the
            // fly translation to ASCII
            //
            antlr3EBCDICSetupStream(input);
            break;

        case    ANTLR3_ENC_8BIT:
        default:

            // Standard 8bit/ASCII
            //
            antlr38BitSetupStream(input);
            break;
    }
}

static ANTLR3_UCHAR
myLA(pANTLR3_INT_STREAM is, ANTLR3_INT32 la) {
    pANTLR3_INPUT_STREAM input;

    input   = ((pANTLR3_INPUT_STREAM) (is->super));

    Debug("pipe") << "LA" << std::endl;
    if	(( ((pANTLR3_UINT8)input->nextChar) + la - 1) >= (((pANTLR3_UINT8)input->data) + input->sizeBuf))
    {
      std::istream& in = *((pANTLR3_LINE_BUFFERED_INPUT_STREAM)input)->in;
      if(!in) {
        Debug("pipe") << "EOF" << std::endl;
        return	ANTLR3_CHARSTREAM_EOF;
      }
      Debug("pipe") << "READ" << std::endl;
      if(input->data == NULL) {
        Debug("pipe") << "ALLOC" << std::endl;
        input->data = malloc(100);
        input->nextChar = input->data;
        in.getline((((char*)input->data) + input->sizeBuf), 100);
      } else {
        Debug("pipe") << "REALLOC" << std::endl;
        size_t pos = (char*)input->nextChar - (char*)input->data;
        input->data = realloc(input->data, input->sizeBuf + 100);
        input->nextChar = (char*)input->data + pos;
        in.getline((((char*)input->data) + input->sizeBuf), 100);
      }
      if(!in) {
        Debug("pipe") << "bad input, or string too long" << std::endl;
        return ANTLR3_CHARSTREAM_EOF;
      }
      input->sizeBuf += strlen(((char*)input->data) + input->sizeBuf);
      Assert(*(((char*)input->data) + input->sizeBuf) == '\0');
      Debug("pipe") << "SIZEBUF now " << input->sizeBuf << std::endl;
      *(((char*)input->data) + input->sizeBuf) = '\n';
      ++input->sizeBuf;
    }

    Debug("pipe") << "READ POINTER[" << la << "] AT: >>" << string(((char*)input->nextChar), input->sizeBuf - (((char*)input->nextChar) - (char*)input->data) + 1) << "<< returning '" << (char)(*((pANTLR3_UINT8)input->nextChar + la - 1)) << "' (" << (unsigned)(*((pANTLR3_UINT8)input->nextChar + la - 1)) << ")" << std::endl;
    return	(ANTLR3_UCHAR)(*((pANTLR3_UINT8)input->nextChar + la - 1));
}

static void
myConsume(pANTLR3_INT_STREAM is)
{
    pANTLR3_INPUT_STREAM input;

    input   = ((pANTLR3_INPUT_STREAM) (is->super));

    Debug("pipe") << "consume! '" << *(char*)input->nextChar << "' (" << (unsigned)*(char*)input->nextChar << ")" << std::endl;
    if	((pANTLR3_UINT8)(input->nextChar) < (((pANTLR3_UINT8)input->data) + input->sizeBuf))
    {
	/* Indicate one more character in this line
	 */
	input->charPositionInLine++;

	if  ((ANTLR3_UCHAR)(*((pANTLR3_UINT8)input->nextChar)) == input->newlineChar)
	{
	    /* Reset for start of a new line of input
	     */
	    input->line++;
	    input->charPositionInLine	= 0;
	    input->currentLine		= (void *)(((pANTLR3_UINT8)input->nextChar) + 1);
            Debug("pipe") << "-- newline!" << std::endl;
	}

	/* Increment to next character position
	 */
	input->nextChar = (void *)(((pANTLR3_UINT8)input->nextChar) + 1);
        Debug("pipe") << "-- advance nextChar! looking at '" << *(char*)input->nextChar << "' (" << (unsigned)*(char*)input->nextChar << ")" << std::endl;
    } else Debug("pipe") << "-- nothing!" << std::endl;
}

pANTLR3_INPUT_STREAM
antlr3LineBufferedStreamNew(std::istream& in, ANTLR3_UINT32 encoding, pANTLR3_UINT8 name)
{
    pANTLR3_INPUT_STREAM    input;

    if(!in) {
      return NULL;
    }

    // First order of business is to set up the stream and install the data pointer.
    // Then we will work out the encoding and byte order and adjust the API functions that are installed for the
    // default 8Bit stream accordingly.
    //
    input   = antlr3CreateLineBufferedStream(in);
    if  (input == NULL)
    {
        return NULL;
    }

    // Size (in bytes) of the given 'string'
    //
    input->sizeBuf		= 0;

    input->istream->_LA		= myLA;
    input->istream->consume	= myConsume;

    ((pANTLR3_LINE_BUFFERED_INPUT_STREAM)input)->in = &in;

    // We have the data in memory now so we can deal with it according to 
    // the encoding scheme we were given by the user.
    //
    input->encoding = encoding;

    // Now we need to work out the endian type and install any 
    // API functions that differ from 8Bit
    //
    setupInputStream(input);

    // Now we can set up the file name
    //	
    input->istream->streamName	= input->strFactory->newStr8(input->strFactory, name);
    input->fileName		= input->istream->streamName;

    return input;
}

AntlrInputStream*
AntlrInputStream::newStreamInputStream(std::istream& input,
                                       const std::string& name,
                                       bool lineBuffered)
  throw (InputStreamException, AssertionException) {

  pANTLR3_INPUT_STREAM inputStream = NULL;

  if(lineBuffered) {
    inputStream =
      antlr3LineBufferedStreamNew(input,
                                  ANTLR3_ENC_8BIT,
                                  (pANTLR3_UINT8) strdup(name.c_str()));
  } else {

    // Since these are all NULL on entry, realloc will be called
    char *basep = NULL, *boundp = NULL, *cp = NULL;
    /* 64KB seems like a reasonable default size. */
    size_t bufSize = 0x10000;

    /* Keep going until we can't go no more. */
    while( !input.eof() && !input.fail() ) {

      if( cp == boundp ) {
        /* We ran out of room in the buffer. Realloc at double the size. */
        ptrdiff_t offset = cp - basep;
        basep = (char *) realloc(basep, bufSize);
        if( basep == NULL ) {
          throw InputStreamException("Failed buffering input stream: " + name);
        }
        cp = basep + offset;
        boundp = basep + bufSize;
        bufSize *= 2;
      }

      /* Read as much as we have room for. */
      input.read( cp, boundp - cp );
      cp += input.gcount();
    }

    /* Make sure the fail bit didn't get set. */
    if( !input.eof() ) {
      throw InputStreamException("Stream input failed: " + name);
    }

    /* Create an ANTLR input backed by the buffer. */
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
    inputStream =
      antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8) basep,
                                        cp - basep,
                                        (pANTLR3_UINT8) strdup(name.c_str()));
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
    inputStream =
      antlr3StringStreamNew((pANTLR3_UINT8) basep,
                            ANTLR3_ENC_8BIT,
                            cp - basep,
                            (pANTLR3_UINT8) strdup(name.c_str()));
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */

  }

  if( inputStream == NULL ) {
    throw InputStreamException("Couldn't initialize input: " + name);
  }

  return new AntlrInputStream( name, inputStream );
}


AntlrInputStream*
AntlrInputStream::newStringInputStream(const std::string& input,
                                       const std::string& name)
  throw (InputStreamException, AssertionException) {
  char* inputStr = strdup(input.c_str());
  char* nameStr = strdup(name.c_str());
  AlwaysAssert( inputStr!=NULL && nameStr!=NULL );
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  pANTLR3_INPUT_STREAM inputStream =
      antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8) inputStr,
                                        input.size(),
                                        (pANTLR3_UINT8) nameStr);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  pANTLR3_INPUT_STREAM inputStream =
      antlr3StringStreamNew((pANTLR3_UINT8) inputStr,
                            ANTLR3_ENC_8BIT,
                            input.size(),
                            (pANTLR3_UINT8) nameStr);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  if( inputStream==NULL ) {
    throw InputStreamException("Couldn't initialize string input: '" + input + "'");
  }
  return new AntlrInputStream( name, inputStream );
}

AntlrInput* AntlrInput::newInput(InputLanguage lang, AntlrInputStream& inputStream) {
  using namespace language::input;

  AntlrInput* input;

  switch(lang) {
  case LANG_CVC4: {
    input = new CvcInput(inputStream);
    break;
  }
  case LANG_SMTLIB:
    input = new SmtInput(inputStream);
    break;

  case LANG_SMTLIB_V2:
    input = new Smt2Input(inputStream);
    break;

  default:
    Unhandled(lang);
  }

  return input;
}

AntlrInput::AntlrInput(AntlrInputStream& inputStream, unsigned int lookahead) :
    Input(inputStream),
    d_lookahead(lookahead),
    d_lexer(NULL),
    d_parser(NULL),
    d_antlr3InputStream( inputStream.getAntlr3InputStream() ),
    d_tokenBuffer(NULL) {
}

/*
AntlrParser::AntlrParser(ExprManager* exprManager, std::istream& input, const std::string& name, unsigned int lookahead)
  Parser(exprManager,name),
  d_lookahead(lookahead) {

}
*/

/*
AntlrInput::Input(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead) :
  Input(exprManager,name),
  d_lookahead(lookahead),
  d_lexer(NULL),
  d_parser(NULL),
  d_tokenStream(NULL) {

  char* inputStr = strdup(input.c_str());
  char* nameStr = strdup(name.c_str());
  if( inputStr==NULL || nameStr==NULL ) {
    throw ParserException("Couldn't initialize string input: '" + input + "'");
  }
  d_inputStream = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8)inputStr,input.size(),(pANTLR3_UINT8)nameStr);
  if( d_inputStream == NULL ) {
    throw ParserException("Couldn't create input stream for string: '" + input + "'");
  }

}
*/

AntlrInput::~AntlrInput() {
  BoundedTokenBufferFree(d_tokenBuffer);
}

pANTLR3_COMMON_TOKEN_STREAM AntlrInput::getTokenStream() {
  return d_tokenBuffer->commonTstream;
}

void AntlrInput::lexerError(pANTLR3_BASE_RECOGNIZER recognizer) {
  pANTLR3_LEXER lexer = (pANTLR3_LEXER)(recognizer->super);
  AlwaysAssert(lexer!=NULL);
  Parser *parser = (Parser*)(lexer->super);
  AlwaysAssert(parser!=NULL);
  AntlrInput *input = (AntlrInput*) parser->getInput();
  AlwaysAssert(input!=NULL);

  /* Call the error display routine *if* there's not already a 
   * parse error pending.  If a parser error is pending, this
   * error is probably less important, so we just drop it. */
  if( input->d_parser->rec->state->error == ANTLR3_FALSE ) {
    input->parseError("Error finding next token.");
  }
}

void AntlrInput::parseError(const std::string& message)
  throw (ParserException, AssertionException) {
  Debug("parser") << "Throwing exception: "
      << getInputStream()->getName() << ":"
      << d_lexer->getLine(d_lexer) << "."
      << d_lexer->getCharPositionInLine(d_lexer) << ": "
      << message << endl;
  throw ParserException(message, getInputStream()->getName(),
                        d_lexer->getLine(d_lexer),
                        d_lexer->getCharPositionInLine(d_lexer));
}


void AntlrInput::setAntlr3Lexer(pANTLR3_LEXER pLexer) {
  d_lexer = pLexer;

  pANTLR3_TOKEN_FACTORY pTokenFactory = d_lexer->rec->state->tokFactory;
  if( pTokenFactory != NULL ) {
    pTokenFactory->close(pTokenFactory);
  }

  /* 2*lookahead should be sufficient, but we give ourselves some breathing room. */
  pTokenFactory = BoundedTokenFactoryNew(d_antlr3InputStream, 2*d_lookahead);
  if( pTokenFactory == NULL ) {
    throw ParserException("Couldn't create token factory.");
  }
  d_lexer->rec->state->tokFactory = pTokenFactory;

  pBOUNDED_TOKEN_BUFFER buffer = BoundedTokenBufferSourceNew(d_lookahead, d_lexer->rec->state->tokSource);
  if( buffer == NULL ) {
    throw ParserException("Couldn't create token buffer.");
  }

  d_tokenBuffer = buffer;

  // Override default lexer error reporting
  d_lexer->rec->reportError = &lexerError;
  // Override default nextToken function, just to prevent exceptions escaping.
  d_lexer->rec->state->tokSource->nextToken = &nextTokenStr;
}

void AntlrInput::setParser(Parser& parser) {
  // ANTLR isn't using super in the lexer or the parser, AFAICT.
  // We could also use @lexer/parser::context to add a field to the generated
  // objects, but then it would have to be declared separately in every
  // language's grammar and we'd have to in the address of the field anyway.
  d_lexer->super = &parser;
  d_parser->super = &parser;
}

void AntlrInput::setAntlr3Parser(pANTLR3_PARSER pParser) {
  d_parser = pParser;
//  d_parser->rec->match = &match;
  d_parser->rec->reportError = &reportError;
  /* Don't try to recover from a parse error. */
  // [chris 4/5/2010] Not clear on why this cast is necessary, but I get an error if I remove it.
  d_parser->rec->recoverFromMismatchedToken =
      (void* (*)(ANTLR3_BASE_RECOGNIZER_struct*, ANTLR3_UINT32, ANTLR3_BITSET_LIST_struct*))
      d_parser->rec->mismatch;
}

static pANTLR3_INPUT_STREAM
antlr3CreateLineBufferedStream(std::istream& in)
{
	// Pointer to the input stream we are going to create
	//
	pANTLR3_INPUT_STREAM    input;

	if	(in == NULL)
	{
		return NULL;
	}

	// Allocate memory for the input stream structure
	//
	input   = (pANTLR3_INPUT_STREAM)
		ANTLR3_CALLOC(1, sizeof(ANTLR3_LINE_BUFFERED_INPUT_STREAM));

	if	(input == NULL)
	{
		return	NULL;
	}

	// Structure was allocated correctly, now we can install the pointer
	//
        input->data             = NULL;
        input->isAllocated	= ANTLR3_FALSE;

	// Call the common 8 bit input stream handler
	// initialization.
	//
	antlr3GenericSetupStream(input);

        return  input;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
