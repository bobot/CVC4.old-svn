/*********************                                                        */
/*! \file model_engine_model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model Engine model classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_ENGINE_MODEL_H
#define __CVC4__MODEL_ENGINE_MODEL_H

#include "theory/quantifiers_engine.h"
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

namespace quantifiers {

/*
class ExtendedModelComponent
{
public:
  ExtendedModelComponent(){}
  virtual ~ExtendedModelComponent(){}
};
*/

class ModelEngine;
class RepSetIterator;

class ExtendedModel : public Model
{
  friend class ModelEngine;
  friend class RepSetIterator;
private:
  //quantifiers engine
  QuantifiersEngine* d_qe;
public: //for Theory UF:
  //models for each UF operator
  std::map< Node, uf::UfModel > d_uf_model;
public:
  ExtendedModel( QuantifiersEngine* qe, context::Context* c );
  virtual ~ExtendedModel(){}
  /** build model */
  void buildModel();
  /** get interpreted value */
  Node getInterpretedValue( TNode n );
public:
  void debugPrint( const char* c );
};

}
}
}

#endif
