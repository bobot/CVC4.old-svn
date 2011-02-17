/*********************                                                        */
/*! \file memory_mapped_input_buffer.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <fcntl.h>
#include <stdio.h>
#include <stdint.h>

#include <sys/errno.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <antlr3input.h>

#include "parser/memory_mapped_input_buffer.h"
#include "util/Assert.h"
#include "util/exception.h"

namespace CVC4 {
namespace parser {

extern "C" {

static ANTLR3_UINT32
MemoryMapFile(pANTLR3_INPUT_STREAM input, const std::string& filename);

void
UnmapFile(pANTLR3_INPUT_STREAM input);

pANTLR3_INPUT_STREAM MemoryMappedInputBufferNew(const std::string& filename) {
  // Pointer to the input stream we are going to create
  //
  pANTLR3_INPUT_STREAM input;
  ANTLR3_UINT32 status;

  // Allocate memory for the input stream structure
  //
  input = (pANTLR3_INPUT_STREAM) ANTLR3_CALLOC(1, sizeof(ANTLR3_INPUT_STREAM));

  if(input == NULL) {
    return NULL;
  }

  // Structure was allocated correctly, now we can read the file.
  //
  status = MemoryMapFile(input, filename);

  // Call the common 8 bit ASCII input stream handler
  // Initializer type thingy doobry function.
  //
  antlr3AsciiSetupStream(input, ANTLR3_CHARSTREAM);

  // Now we can set up the file name
  //
  input->istream->streamName
      = input->strFactory->newStr(input->strFactory,
                                  (uint8_t*) filename.c_str());
  input->fileName = input->istream->streamName;
  input->free = UnmapFile;

  if(status != ANTLR3_SUCCESS) {
    input->close(input);
    return NULL;
  }

  return input;
}

static ANTLR3_UINT32 MemoryMapFile(pANTLR3_INPUT_STREAM input,
                                   const std::string& filename) {
  errno = 0;
  struct stat st;
  if(stat(filename.c_str(), &st) == -1) {
    return ANTLR3_ERR_NOFILE;
  }

  input->sizeBuf = st.st_size;

  int fd = open(filename.c_str(), O_RDONLY);
  if(fd == -1) {
    return ANTLR3_ERR_NOFILE;
  }

  input->data = mmap(0, input->sizeBuf, PROT_READ, MAP_FILE | MAP_PRIVATE, fd,
                     0);
  errno = 0;
  if(intptr_t(input->data) == -1) {
    return ANTLR3_ERR_NOMEM;
  }

  return ANTLR3_SUCCESS;
}

/* This is a bit shady. antlr3AsciiSetupStream has free and close as aliases.
 * We need to unmap the file somewhere, so we install this function as free and
 * call the default version of close to de-allocate everything else. */
void UnmapFile(pANTLR3_INPUT_STREAM input) {
  munmap((void*) input->data, input->sizeBuf);
  input->close(input);
}

}/* extern "C" */

}/* CVC4::parser namespace */
}/* CVC4 namespace */
