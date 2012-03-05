/*********************                                                        */
/*! \file clock_gettime.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Replacement for clock_gettime() for systems without it (like Mac OS X)
 **
 ** Replacement for clock_gettime() for systems without it (like Mac OS X).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LIB__CLOCK_GETTIME_H
#define __CVC4__LIB__CLOCK_GETTIME_H

#include "lib/replacements.h"

#ifdef HAVE_CLOCK_GETTIME

/* it should be available from <time.h> */
#include <time.h>

#else /* HAVE_CLOCK_GETTIME */

/* otherwise, we have to define it */

/* get timespec from <time.h> */
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

typedef enum {
  CLOCK_REALTIME,
  CLOCK_MONOTONIC,
  CLOCK_REALTIME_HR,
  CLOCK_MONOTONIC_HR
} clockid_t;

long clock_gettime(clockid_t which_clock, struct timespec *tp);

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#endif /* HAVE_CLOCK_GETTIME */
#endif /*__CVC4__LIB__CLOCK_GETTIME_H */

