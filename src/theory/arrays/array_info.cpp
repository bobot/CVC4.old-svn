/*********************                                                        */
/*! \file array_info.cpp
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Contains additional classes to store context dependent information
 ** for each term of type array
 **
 **
 **/

#include "array_info.h"

namespace CVC4 {
namespace theory {
namespace arrays {

bool ArrayInfo::inList(CTNodeList* l, TNode el) {
  CTNodeList::const_iterator it = l->begin();
  for ( ; it!= l->end(); it ++) {
    if(*it == el)
      return true;
  }
  return false;
}

void ArrayInfo::mergeLists(CTNodeList* la, CTNodeList* lb) {
  std::set<TNode> temp;
  CTNodeList::const_iterator it;
  for(it = la->begin() ; it != la->end(); it++ ) {
    temp.insert((*it));
  }

  for(it = lb->begin() ; it!= lb->end(); it++ ) {
    if(temp.count(*it) == 0) {
      la->push_back(*it);
    }
  }
}

void ArrayInfo::addIndex(const Node a, const TNode i) {
  Assert(a.getType().isArray());
  Assert(!i.getType().isArray()); // temporary for flat arrays

  CTNodeList* temp_indices;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_indices = new(true) CTNodeList(ct);
    temp_indices->push_back(i);

    temp_info = new Info(ct);
    temp_info->indices = temp_indices;

    info_map.insert(a, temp_info);
  } else {
    temp_indices = (*it).second->indices;
    if(! inList(temp_indices, i)) {
      temp_indices->push_back(i);
    }
  }

}

void ArrayInfo::addEqStore(const Node a, const TNode st){
  Assert(a.getType().isArray());
  Assert(st.getKind()== kind::STORE); // temporary for flat arrays

  CTNodeList* temp_eqstore;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_eqstore = new(true) CTNodeList(ct);
    temp_eqstore->push_back(st);

    temp_info = new Info(ct);
    temp_info->eq_stores = temp_eqstore;
    info_map.insert(a, temp_info);
  } else {
    temp_eqstore = (*it).second->eq_stores;
    if(! inList(temp_eqstore, st)) {
      temp_eqstore->push_back(st);
    }
  }
};

void ArrayInfo::addInStore(const Node a, const TNode st){
  Assert(a.getType().isArray());
  Assert(st.getKind()== kind::STORE); // temporary for flat arrays

  CTNodeList* temp_instore;
  Info* temp_info;

  CNodeInfoMap::iterator it = info_map.find(a);
  if(it == info_map.end()) {
    temp_instore = new(true) CTNodeList(ct);
    temp_instore->push_back(st);

    temp_info = new Info(ct);
    temp_info->in_stores = temp_instore;
    info_map.insert(a, temp_info);
  } else {
    temp_instore = (*it).second->in_stores;
    if(! inList(temp_instore, st)) {
      temp_instore->push_back(st);
    }
  }
};

/**
 * Maps a to the emptyInfo if a is not already in the map
 */
void ArrayInfo::addEmptyEntry(TNode a) {
  Assert(a.getType().isArray());

  if(info_map.find(a) == info_map.end()) {
    info_map.insert(a, emptyInfo);
  }
}

/**
 * Returns the information associated with TNode a
 */

Info* ArrayInfo::getInfo(TNode a) {
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it!= info_map.end())
      return (*it).second;
  return emptyInfo;
}

CTNodeList* ArrayInfo::getIndices(TNode a) {
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->indices;
  }
  return emptyList;
}

CTNodeList* ArrayInfo::getInStores(TNode a) {
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->in_stores;
  }
  return emptyList;
}

CTNodeList* ArrayInfo::getEqStores(TNode a) {
  CNodeInfoMap::iterator it = info_map.find(a);
  if(it!= info_map.end()) {
    return (*it).second->eq_stores;
  }
  return emptyList;
}


void ArrayInfo::mergeInfo(TNode a, TNode b){
  // can't have assertion that find(b) = a !

  Debug("arrays-mergei")<<"Arrays::mergeInfo merging "<<a<<"\n";
  Debug("arrays-mergei")<<"                      and "<<b<<"\n";


  CNodeInfoMap::iterator ita = info_map.find(a);
  CNodeInfoMap::iterator itb = info_map.find(b);
  if(ita != info_map.end()) {
    Debug("arrays-mergei")<<"Arrays::mergeInfo info "<<a<<"\n";
    if(Debug.isOn("arrays-mergei"))
      (*ita).second->print();

    if(itb != info_map.end()) {
      Debug("arrays-mergei")<<"Arrays::mergeInfo info "<<b<<"\n";
      if(Debug.isOn("arrays-mergei"))
        (*itb).second->print();
      CTNodeList* lista_i = (*ita).second->indices;
      CTNodeList* lista_inst = (*ita).second->in_stores;
      CTNodeList* lista_eqst = (*ita).second->eq_stores;

      CTNodeList* listb_i = (*itb).second->indices;
      CTNodeList* listb_inst = (*itb).second->in_stores;
      CTNodeList* listb_eqst = (*itb).second->eq_stores;

      mergeLists(lista_i, listb_i);
      mergeLists(lista_inst, listb_inst);
      mergeLists(lista_eqst, listb_eqst);
    }
  }
  Debug("arrays-mergei")<<"Arrays::mergeInfo merged info \n";
  if(Debug.isOn("arrays-mergei"))
    (*ita).second->print();
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
