/** \file
 * Defines the interface for an ANTLR3 common token stream. Custom token streams should create
 * one of these and then override any functions by installing their own pointers
 * to implement the various functions.
 */
#ifndef	__CVC4__PARSER__TWO_PLACE_TOKEN_STREAM_H
#define	__CVC4__PARSER__TWO_PLACE_TOKEN_STREAM_H

// [The "BSD licence"]
// Copyright (c) 2005-2009 Jim Idle, Temporal Wave LLC
// http://www.temporal-wave.com
// http://www.linkedin.com/in/jimidle
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. The name of the author may not be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
// IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
// OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
// THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include    <antlr3defs.h>

namespace CVC4 {
namespace parser {

#ifdef __cplusplus
extern "C" {
#endif



typedef struct  TWO_PLACE_TOKEN_BUFFER_struct
{
    /** The ANTLR3_TOKEN_STREAM interface implementation, which also includes
     *  the intstream implementation. We could duplicate the pANTLR_INT_STREAM
     *  in this interface and initialize it to a copy, but this could be confusing
     *  it just results in one more level of indirection and I think that with
     *  judicial use of 'const' later, the optimizer will do decent job.
     */
    pANTLR3_COMMON_TOKEN_STREAM    commonTstream;
    pANTLR3_COMMON_TOKEN tokenNeg1, token1, token2;
    unsigned long int index;
    ANTLR3_BOOLEAN done;
} TWO_PLACE_TOKEN_BUFFER, *pTWO_PLACE_TOKEN_BUFFER;

pTWO_PLACE_TOKEN_BUFFER
TwoPlaceTokenBufferSourceNew(ANTLR3_UINT32 hint, pANTLR3_TOKEN_SOURCE source);

void
TwoPlaceTokenBufferFree(pTWO_PLACE_TOKEN_BUFFER buffer);

#ifdef __cplusplus
}
#endif

}
}


#endif /* __CVC4__PARSER__TWO_PLACE_TOKEN_STREAM_H */

