/*! \file array_info.h
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__ARRAY_INFO_H
#define __CVC4__THEORY__ARRAYS__ARRAY_INFO_H

#include "context/cdlist.h"
#include "context/cdmap.h"
#include "expr/node.h"
#include <ext/hash_set>
#include <iostream>
#include <map>
namespace CVC4 {
namespace theory {
namespace arrays {

typedef context::CDList<TNode> CTNodeList;


/**
 * Small class encapsulating the information
 * in the map. It's a class and not a struct to
 * call the destructor.
 */

class Info {
public:
  CTNodeList* indices;
  CTNodeList* eq_stores;
  CTNodeList* in_stores; //FIXME: maybe need only one store list

  Info(context::Context* c) {
    indices = new(true)CTNodeList(c);
    eq_stores = new(true)CTNodeList(c);
    in_stores = new(true)CTNodeList(c);
  }

  ~Info() {
    indices->deleteSelf();
    eq_stores->deleteSelf();
    in_stores->deleteSelf();
  }

  /**
   * debug method to print a list
   */

  static void printList(CTNodeList* list) {
    CTNodeList::const_iterator it = list->begin();
    Debug("arrays-info")<<"   [ ";
    for(; it != list->end(); it++ ) {
      Debug("arrays-info")<<(*it)<<" ";
    }
    Debug("arrays-info")<<"] \n";
  }

  /**
   * prints the information
   */
  void print() {
    Assert(indices != NULL && eq_stores!= NULL && in_stores != NULL);
    Debug("arrays-info")<<"  indices   ";
    printList(indices);
    Debug("arrays-info")<<"  eq_stores ";
    printList(eq_stores);
    Debug("arrays-info")<<"  in_stores ";
    printList(in_stores);
  }
};

typedef context::CDMap <Node, Info*, NodeHashFunction> CNodeInfoMap;

/**
 * Class keeping track of the following information for canonical
 * representatives of type array [a] :
 *    indices at which it is being read (all i for which there is a
 *            term of the form SELECT a i)
 *    all store terms in the congruence class
 *    stores in which it appears (terms of the form STORE a _ _ )
 *
 */
class ArrayInfo {
private:
  context::Context* ct;
  CNodeInfoMap info_map;

  CTNodeList* emptyList;
  Info* emptyInfo;

  /**
   * checks if a certain element is in the list l
   * FIXME: better way to check for duplicates?
   */
  bool inList(CTNodeList* l, TNode el);

  /**
   * helper method that merges two lists into the first
   * without adding duplicates
   */
  void mergeLists(CTNodeList* la, CTNodeList* lb);

public:

  ArrayInfo(context::Context* c): ct(c), info_map(ct) {
    emptyList = new(true) CTNodeList(ct);
    emptyInfo = new Info(ct);
  }
  ~ArrayInfo(){
    CNodeInfoMap::iterator it = info_map.begin();
    for( ; it != info_map.end(); it++ ) {
      if((*it).second!= emptyInfo) {
        delete (*it).second;
      }
    }
    emptyList->deleteSelf();
    delete emptyInfo;
  };

  /**
   * adds the node a to the map if it does not exist
   * and it initializes the info. checks for duplicate i's
   */
  void addIndex(const Node a, const TNode i);
  void addEqStore(const Node a, const TNode st);
  void addInStore(const Node a, const TNode st);

  /**
   * Maps a to the emptyInfo if a is not already in the map
   */
  void addEmptyEntry(TNode a);

  /**
   * Returns the information associated with TNode a
   */

  Info* getInfo(TNode a);

  CTNodeList* getIndices(TNode a);

  CTNodeList* getInStores(TNode a);

  CTNodeList* getEqStores(TNode a);

  /**
   * merges the information of  nodes a and b
   * the nodes do not have to actually be in the map.
   * pre-condition
   *  a should be the canonical representative of b
   */
  void mergeInfo(TNode a, TNode b);
};


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__ARRAY_INFO_H */
