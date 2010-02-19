/*********************                                                        */
/** node.cpp
 ** Original author: mdeters
 ** Major contributors: taking, dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to an expression.
 **/

#include "expr/node.h"
#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "util/Assert.h"

#include <sstream>

using namespace CVC4::expr;
using namespace std;

