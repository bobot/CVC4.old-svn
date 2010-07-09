/*********************                                                        */
/*! \file context.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of base context operations.
 **
 ** Implementation of base context operations.
 **/


#include <iostream>
#include <vector>

#include "context/context.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {


Context::Context() : d_pCNOpre(NULL), d_pCNOpost(NULL) {
  // Create new memory manager
  d_pCMM = new ContextMemoryManager();

  // Create initial Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, 0));
}


Context::~Context() throw(AssertionException) {
  // Delete all Scopes
  popto(0);

  // Delete the memory manager
  delete d_pCMM;

  // Clear ContextNotifyObj lists so there are no dangling pointers
  ContextNotifyObj* pCNO;
  while(d_pCNOpre != NULL) {
    pCNO = d_pCNOpre;
    pCNO->d_ppCNOprev = NULL;
    d_pCNOpre = pCNO->d_pCNOnext;
    pCNO->d_pCNOnext = NULL;
  }
  while(d_pCNOpost != NULL) {
    pCNO = d_pCNOpost;
    pCNO->d_ppCNOprev = NULL;
    d_pCNOpost = pCNO->d_pCNOnext;
    pCNO->d_pCNOnext = NULL;
  }
}


void Context::push() {
  Trace("pushpop") << std::string(2 * getLevel(), ' ') << "Push {" << std::endl;

  // Create a new memory region
  d_pCMM->push();

  // Create a new top Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, getLevel()+1));
}


void Context::pop() {
  Assert(getLevel() > 0, "Cannot pop below level 0");

  // Notify the (pre-pop) ContextNotifyObj objects
  ContextNotifyObj* pCNO = d_pCNOpre;
  while(pCNO != NULL) {
    pCNO->notify();
    pCNO = pCNO->d_pCNOnext;
  }

  // Grab the top Scope
  Scope* pScope = d_scopeList.back();

  // Restore the previous Scope
  d_scopeList.pop_back();

  // Restore all objects in the top Scope
  delete pScope;

  // Pop the memory region
  d_pCMM->pop();

  // Notify the (post-pop) ContextNotifyObj objects
  pCNO = d_pCNOpost;
  while(pCNO != NULL) {
    pCNO->notify();
    pCNO = pCNO->d_pCNOnext;
  }

  Trace("pushpop") << std::string(2 * getLevel(), ' ') << "} Pop" << std::endl;
}


void Context::popto(int toLevel) {
  // Pop scopes until there are none left or toLevel is reached
  if(toLevel < 0) toLevel = 0;
  while(toLevel < getLevel()) pop();
}


void Context::addNotifyObjPre(ContextNotifyObj* pCNO) {
  // Insert pCNO at *front* of list
  if(d_pCNOpre != NULL)
    d_pCNOpre->prev() = &(pCNO->next());
  pCNO->next() = d_pCNOpre;
  pCNO->prev() = &d_pCNOpre;
  d_pCNOpre = pCNO;
}


void Context::addNotifyObjPost(ContextNotifyObj* pCNO) {
  // Insert pCNO at *front* of list
  if(d_pCNOpost != NULL)
    d_pCNOpost->prev() = &(pCNO->next());
  pCNO->next() = d_pCNOpost;
  pCNO->prev() = &d_pCNOpost;
  d_pCNOpost = pCNO;
}


void ContextObj::update() throw(AssertionException) {
  Debug("context") << "before update(" << this << "):" << std::endl
                   << *getContext() << std::endl;

  // Call save() to save the information in the current object
  ContextObj* pContextObjSaved = save(d_pScope->getCMM());

  Debug("context") << "in update(" << this << ") with restore "
                   << pContextObjSaved << ": waypoint 1" << std::endl
                   << *getContext() << std::endl;

  // Check that base class data was saved
  Assert( ( pContextObjSaved->d_pContextObjNext == d_pContextObjNext &&
            pContextObjSaved->d_ppContextObjPrev == d_ppContextObjPrev &&
            pContextObjSaved->d_pContextObjRestore == d_pContextObjRestore &&
            pContextObjSaved->d_pScope == d_pScope ),
          "save() did not properly copy information in base class" );

  // Link the "saved" object in place of this ContextObj in the scope
  // we're moving it FROM.
  Debug("context") << "in update(" << this
                   << "): next() == " << next() << std::endl;
  if(next() != NULL) {
    Debug("context") << "in update(" << this
                     << "): next()->prev() == " << next()->prev() << std::endl;
    next()->prev() = &pContextObjSaved->next();
    Debug("context") << "in update(" << this
                     << "): next()->prev() is now "
                     << next()->prev() << std::endl;
  }
  Debug("context") << "in update(" << this
                   << "): prev() == " << prev() << std::endl;
  Debug("context") << "in update(" << this
                   << "): *prev() == " << *prev() << std::endl;
  *prev() = pContextObjSaved;
  Debug("context") << "in update(" << this
                   << "): *prev() is now " << *prev() << std::endl;

  Debug("context") << "in update(" << this << ") with restore "
                   << pContextObjSaved << ": waypoint 3" << std::endl
                   << *getContext() << std::endl;

  // Update Scope pointer to current top Scope
  d_pScope = d_pScope->getContext()->getTopScope();

  // Store the saved copy in the restore pointer
  d_pContextObjRestore = pContextObjSaved;

  // Insert object into the list of objects that need to be restored when this
  // Scope is popped.
  d_pScope->addToChain(this);

  Debug("context") << "after update(" << this << ") with restore "
                   << pContextObjSaved << ":" << std::endl
                   << *getContext() << std::endl;
}


ContextObj* ContextObj::restoreAndContinue() throw(AssertionException) {
  // Variable to hold next object in list
  ContextObj* pContextObjNext;

  // Check the restore pointer.  If NULL, this must be the bottom Scope
  if(d_pContextObjRestore == NULL) {
    // might not be bottom scope, since objects allocated in context
    // memory don't get linked to scope 0
    //
    // Assert(d_pScope == d_pScope->getContext()->getBottomScope(),
    //        "Expected bottom scope");

    pContextObjNext = d_pContextObjNext;

    // Nothing else to do
  } else {
    // Call restore to update the subclass data
    restore(d_pContextObjRestore);

    // Remember the next object in the list
    pContextObjNext = d_pContextObjNext;

    // Restore the base class data
    d_pScope = d_pContextObjRestore->d_pScope;
    next() = d_pContextObjRestore->d_pContextObjNext;
    prev() = d_pContextObjRestore->d_ppContextObjPrev;
    d_pContextObjRestore = d_pContextObjRestore->d_pContextObjRestore;

    // Re-link this ContextObj to the list in this scope
    if(next() != NULL) {
      next()->prev() = &next();
    }
    *prev() = this;
  }

  // Return the next object in the list
  return pContextObjNext;
}


void ContextObj::destroy() throw(AssertionException) {
  /* Context can be big and complicated, so we only want to process this output
   * if we're really going to use it. (Same goes below.) */
  Debug("context") << "before destroy " << this << " (level " << getLevel()
                   << "):" << std::endl << *getContext() << std::endl;

  for(;;) {
    // If valgrind reports invalid writes on the next few lines,
    // here's a hint: make sure all classes derived from ContextObj in
    // the system properly call destroy() in their destructors.
    // That's needed to maintain this linked list properly.
    if(next() != NULL) {
      next()->prev() = prev();
    }
    *prev() = next();
    if(d_pContextObjRestore == NULL) {
      break;
    }
    Debug("context") << "in destroy " << this << ", restore object is "
                     << d_pContextObjRestore << " at level "
                     << d_pContextObjRestore->getLevel() << ":" << std::endl
                     << *getContext() << std::endl;
    restoreAndContinue();
  }
  Debug("context") << "after destroy " << this << ":" << std::endl
                   << *getContext() << std::endl;
}


ContextObj::ContextObj(Context* pContext) :
  d_pContextObjRestore(NULL) {

  Assert(pContext != NULL, "NULL context pointer");

  Debug("context") << "create new ContextObj(" << this << ")" << std::endl;
  d_pScope = pContext->getBottomScope();
  d_pScope->addToChain(this);
}


ContextObj::ContextObj(bool allocatedInCMM, Context* pContext) :
  d_pContextObjRestore(NULL) {

  Assert(pContext != NULL, "NULL context pointer");

  Debug("context") << "create new ContextObj(" << this << ")" << std::endl;
  if(allocatedInCMM) {
    d_pScope = pContext->getTopScope();
  } else {
    d_pScope = pContext->getBottomScope();
  }
  d_pScope->addToChain(this);
}


ContextNotifyObj::ContextNotifyObj(Context* pContext, bool preNotify) {
  if(preNotify) {
    pContext->addNotifyObjPre(this);
  } else {
    pContext->addNotifyObjPost(this);
  }
}


ContextNotifyObj::~ContextNotifyObj() throw(AssertionException) {
  if(d_pCNOnext != NULL) {
    d_pCNOnext->d_ppCNOprev = d_ppCNOprev;
  }
  if(d_ppCNOprev != NULL) {
    *d_ppCNOprev = d_pCNOnext;
  }
}


std::ostream& operator<<(std::ostream& out,
                         const Context& context) throw(AssertionException) {
  static const std::string separator(79, '-');

  int level = context.d_scopeList.size() - 1;
  typedef std::vector<Scope*>::const_reverse_iterator const_reverse_iterator;
  for(const_reverse_iterator i = context.d_scopeList.rbegin();
      i != context.d_scopeList.rend();
      ++i, --level) {
    Scope* pScope = *i;
    Assert(pScope->getLevel() == level);
    Assert(pScope->getContext() == &context);
    out << separator << std::endl
        << *pScope << std::endl;
  }
  return out << separator << std::endl;
}


std::ostream& operator<<(std::ostream& out,
                         const Scope& scope) throw(AssertionException) {
  out << "Scope " << scope.d_level << ":";
  ContextObj* pContextObj = scope.d_pContextObjList;
  Assert(pContextObj == NULL ||
         pContextObj->prev() == &scope.d_pContextObjList);
  while(pContextObj != NULL) {
    out << " <--> " << pContextObj;
    Assert(pContextObj->d_pScope == &scope);
    Assert(pContextObj->next() == NULL ||
           pContextObj->next()->prev() == &pContextObj->next());
    pContextObj = pContextObj->next();
  }
  return out << " --> NULL";
}


} /* CVC4::context namespace */
} /* CVC4 namespace */
