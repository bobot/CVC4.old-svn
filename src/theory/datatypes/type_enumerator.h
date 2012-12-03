/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for bitvectors
 **
 ** An enumerator for bitvectors.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/type.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesEnumerator : public TypeEnumeratorBase<DatatypesEnumerator> {
  /** The datatype we're enumerating */
  const Datatype& d_datatype;
  /** The datatype constructor we're currently enumerating */
  size_t d_ctor;
  /** The "first" constructor to consider; it's non-recursive */
  size_t d_zeroCtor;
  /** Delegate enumerators for the arguments of the current constructor */
  TypeEnumerator** d_argEnumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    d_argEnumerators = new TypeEnumerator*[d_datatype[d_ctor].getNumArgs()];
    for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
      d_argEnumerators[a] = NULL;
    }
  }

  /** Delete the delegate enumerators */
  void deleteEnumerators() {
    if(d_argEnumerators != NULL) {
      for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
        delete d_argEnumerators[a];
      }
      delete [] d_argEnumerators;
      d_argEnumerators = NULL;
    }
  }

public:

  DatatypesEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(type),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_ctor(0),
    d_zeroCtor(0),
    d_argEnumerators(NULL) {

    //Assert(type.isDatatype());
    Debug("te") << "datatype is datatype? " << type.isDatatype() << std::endl;
    Debug("te") << "datatype is kind " << type.getKind() << std::endl;
    Debug("te") << "datatype is " << type << std::endl;

    /* find the "zero" constructor (the first non-recursive one) */
    /* FIXME: this isn't sufficient for mutually-recursive datatypes! */
    while(d_zeroCtor < d_datatype.getNumConstructors()) {
      bool recursive = false;
      for(size_t a = 0; a < d_datatype[d_zeroCtor].getNumArgs() && !recursive; ++a) {
        recursive = (Node::fromExpr(d_datatype[d_zeroCtor][a].getSelector()).getType()[1] == type);
      }
      if(!recursive) {
        break;
      }
      ++d_zeroCtor;
    }

    /* start with the non-recursive constructor */
    d_ctor = d_zeroCtor;

    /* allocate space for the enumerators */
    newEnumerators();
  }

  ~DatatypesEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(d_ctor < d_datatype.getNumConstructors()) {
      DatatypeConstructor ctor = d_datatype[d_ctor];
      NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
      b << ctor.getConstructor();
      try {
        for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
          if(d_argEnumerators[a] == NULL) {
            d_argEnumerators[a] = new TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a].getSelector()).getType()[1]);
          }
          b << **d_argEnumerators[a];
        }
      } catch(NoMoreValuesException&) {
        InternalError();
      }
      return Node(b);
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    if(d_ctor < d_datatype.getNumConstructors()) {
      for(size_t a = d_datatype[d_ctor].getNumArgs(); a > 0; --a) {
        try {
          *++*d_argEnumerators[a - 1];
          return *this;
        } catch(NoMoreValuesException&) {
          *d_argEnumerators[a - 1] = TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a - 1].getSelector()).getType()[1]);
        }
      }

      // Here, we need to step from the current constructor to the next one

      // first, delete the current delegate enumerators
      deleteEnumerators();

      // Find the next constructor (only complicated by the notion of the "zero" constructor
      d_ctor = (d_ctor == d_zeroCtor) ? 0 : d_ctor + 1;
      if(d_ctor == d_zeroCtor) {
        ++d_ctor;
      }

      // If we aren't out of constructors, allocate space for the new delegate enumerators
      if(d_ctor < d_datatype.getNumConstructors()) {
        newEnumerators();
      }
    }
    return *this;
  }

  bool isFinished() throw() {
    return d_ctor >= d_datatype.getNumConstructors();
  }

};/* DatatypesEnumerator */

class TupleEnumerator : public TypeEnumeratorBase<TupleEnumerator> {
  TypeEnumerator** d_enumerators;

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  TupleEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<TupleEnumerator>(type) {
    Assert(type.isTuple());
    d_enumerators = new TypeEnumerator*[type.getNumChildren()];
    for(size_t i = 0; i < type.getNumChildren(); ++i) {
      d_enumerators[i] = new TypeEnumerator(type[i]);
    }
  }

  ~TupleEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::TUPLE);
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  TupleEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    for(i = 0; i < getType().getNumChildren(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(getType()[i]);
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* TupleEnumerator */

class RecordEnumerator : public TypeEnumeratorBase<RecordEnumerator> {
  TypeEnumerator** d_enumerators;

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  RecordEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<RecordEnumerator>(type) {
    Assert(type.isRecord());
    const Record& rec = getType().getConst<Record>();
    Debug("te") << "creating record enumerator for " << type << std::endl;
    d_enumerators = new TypeEnumerator*[rec.getNumFields()];
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      Debug("te") << " - sub-enumerator for " << rec[i].second << std::endl;
      d_enumerators[i] = new TypeEnumerator(TypeNode::fromType(rec[i].second));
    }
  }

  ~RecordEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::RECORD);
    Debug("te") << "record enumerator: creating record of type " << getType() << std::endl;
    nb << getType();
    const Record& rec = getType().getConst<Record>();
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      Debug("te") << " - " << i << " " << std::flush << "=> " << **d_enumerators[i] << std::endl;
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  RecordEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    const Record& rec = getType().getConst<Record>();
    for(i = 0; i < rec.getNumFields(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(TypeNode::fromType(rec[i].second));
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* RecordEnumerator */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
