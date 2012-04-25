/*********************                                                        */
/*! \file arithvar_set.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>
#include <boost/integer_traits.hpp>

#include "theory/arith/arithvar.h"
#include "context/context.h"
#include "context/cdlist.h"


namespace CVC4 {
namespace theory {
namespace arith {

/**
 * This is an abstraction of a set of ArithVars.
 * This class is designed to provide constant time insertion, deletion, and element_of
 * and fast iteration.
 *
 * ArithVarSets come in 2 varieties: ArithVarSet, and PermissiveBackArithVarSet.
 * The default ArithVarSet assumes that there is no knowledge assumed about ArithVars
 * that are greater than allocated(). Asking isMember() of such an ArithVar
 * is an assertion failure. The cost of doing this is that it takes O(M)
 * where M is the total number of ArithVars in memory.
 *
 * PermissiveBackArithVarSet means that all ArithVars are implicitly not in the set,
 * and any ArithVar past the end of d_posVector is not in the set.
 * A permissiveBack allows for less memory to be consumed on average.
 *
 */
// template <bool permissiveBack>
// class ArithVarSetImpl {
// public:
//   typedef std::vector<ArithVar> VarList;
// private:
//   //List of the ArithVars in the set.
//   VarList d_list;

//   //Each ArithVar in the set is mapped to its position in d_list.
//   //Each ArithVar not in the set is mapped to ARITHVAR_SENTINEL
//   std::vector<unsigned> d_posVector;

// public:
//   typedef VarList::const_iterator const_iterator;

//   ArithVarSetImpl() :  d_list(), d_posVector() {}

//   size_t size() const {
//     return d_list.size();
//   }
//   bool empty() const {
//     return d_list.empty();
//   }

//   size_t allocated() const {
//     return d_posVector.size();
//   }

//   void purge() {
//     for(VarList::const_iterator i=d_list.begin(), endIter=d_list.end();i!= endIter; ++i){
//       d_posVector[*i] = ARITHVAR_SENTINEL;
//     }
//     d_list.clear();
//     Assert(empty());
//   }

//   void increaseSize(ArithVar max){
//     Assert(max >= allocated());
//     d_posVector.resize(max+1, ARITHVAR_SENTINEL);
//   }

//   void increaseSize(){
//     increaseSize(allocated());
//   }

//   bool isMember(ArithVar x) const{
//     if(permissiveBack && x >=  allocated()){
//       return false;
//     }else{
//       Assert(x <  allocated());
//       return d_posVector[x] != ARITHVAR_SENTINEL;
//     }
//   }

//   /** Invalidates iterators */
//   void init(ArithVar x, bool val) {
//     Assert(x >= allocated());
//     increaseSize(x);
//     if(val){
//       add(x);
//     }
//   }

//   /** Invalidates iterators */
//   void add(ArithVar x){
//     Assert(!isMember(x));
//     if(permissiveBack && x >=  allocated()){
//       increaseSize(x);
//     }
//     d_posVector[x] = size();
//     d_list.push_back(x);
//   }

//   const_iterator begin() const{ return d_list.begin(); }
//   const_iterator end() const{ return d_list.end(); }

//   /**
//    * Invalidates iterators.
//    * Adds x to the set if it is not already in the set.
//    */
//   void softAdd(ArithVar x){
//     if(!isMember(x)){
//       add(x);
//     }
//   }

//   const VarList& getList() const{
//     return d_list;
//   }

//   /** Invalidates iterators */
//   void remove(ArithVar x){
//     Assert(isMember(x));
//     swapToBack(x);
//     Assert(d_list.back() == x);
//     pop_back();
//   }

//   ArithVar pop_back() {
//     Assert(!empty());
//     ArithVar atBack = d_list.back();
//     d_posVector[atBack] = ARITHVAR_SENTINEL;
//     d_list.pop_back();
//     return atBack;
//   }

//  private:

//   /** This should be true of all x < allocated() after every operation. */
//   bool wellFormed(ArithVar x){
//     if(d_posVector[x] == ARITHVAR_SENTINEL){
//       return true;
//     }else{
//       return d_list[d_posVector[x]] == x;
//     }
//   }

//   /** Swaps a member x to the back of d_list. */
//   void swapToBack(ArithVar x){
//     Assert(isMember(x));

//     unsigned currentPos = d_posVector[x];
//     ArithVar atBack = d_list.back();

//     d_list[currentPos] = atBack;
//     d_posVector[atBack] = currentPos;

//     d_list[size() - 1] = x;
//     d_posVector[x] = size() - 1;
//   }
// };

// typedef ArithVarSetImpl<false> ArithVarSet;
// typedef ArithVarSetImpl<true> PermissiveBackArithVarSet;

/**
 * This is an abstraction of a Map from an unsigned integer to elements of type T.
 *
 * This class is designed to provide constant time insertion, deletion, element_of,
 * and fast iteration. This is done by storing backing vectors of size greater than
 * the maximum key.  This datastructure is appropraite for heavy use datastructures
 * where the Keys are a dense set of integers.
 *
 * T must support T(), and opertor=().
 */
template <class T>
class DenseMap {
public:
  typedef size_t Key;
  typedef std::vector<Key> KeyList;
  typedef KeyList::const_iterator const_iterator;

private:
  //List of the keys in the dense map.
  KeyList d_list;

  typedef size_t Position;
  typedef std::vector<Position> PositionMap;
  static const Position POSITION_SENTINEL = boost::integer_traits<Position>::const_max;

  //Each Key in the set is mapped to its position in d_list.
  //Each Key not in the set is mapped to KEY_SENTINEL
  PositionMap d_posVector;

  typedef std::vector<T> ImageMap;
  //d_image : Key |-> T
  ImageMap d_image;

public:

  DenseMap() :  d_list(), d_posVector(), d_image() {}

  /** Returns the number of elements in the set. */
  size_t size() const {
    return d_list.size();
  }

  /** Returns true if the map is empty(). */
  bool empty() const {
    return d_list.empty();
  }

  /**
   * Similar to a std::vector::clear().
   *
   * Invalidates iterators.
   */
  void clear() {
    d_list.clear();
    d_posVector.clear();
    d_image.clear();
    Assert(empty());
  }

  /**
   * Similar to a clear(), but the datastructures are not reset in size.
   * Invalidates iterators.
   */
  void purge() {
    while(!empty()){
      pop_back();
    }
    Assert(empty());
  }

  /** Returns true if k is a key of this datastructure. */
  bool isKey(Key x) const{
    if( x >= allocated()){
      return false;
    }else{
      Assert(x <  allocated());
      return d_posVector[x] != POSITION_SENTINEL;
    }
  }

  /**
   * Maps the key to value in the map.
   * Invalidates iterators.
   */
  void set(Key key, const T& value){
    if( key >= allocated()){
      increaseSize(key);
    }

    if(!isKey(key)){
      d_posVector[key] = size();
      d_list.push_back(key);
    }
    d_image[key] = value;
  }

  /** Returns a mutable reference to the element mapped by key. */
  T& get(Key key){
    Assert(isKey(key));
    return d_image[key];
  }

  /** Returns a const reference to the element mapped by key.*/
  const T& operator[](Key key) const {
    Assert(isKey(key));
    return d_image[key];
  }

  /** Returns an iterator over the keys of the map. */
  const_iterator begin() const{ return d_list.begin(); }
  const_iterator end() const{ return d_list.end(); }

  const KeyList& getKeys() const{
    return d_list;
  }

  /**
   * Removes the mapping associated with key.
   * This changes the order of the keys.
   *
   * Invalidates iterators.
   */
  void remove(ArithVar x){
    Assert(isKey(x));
    swapToBack(x);
    Assert(d_list.back() == x);
    pop_back();
  }

  Key back() const {
    return d_list.back();
  }

  /** Removes the element associated with the last Key from the map. */
  void pop_back() {
    Assert(!empty());
    Key atBack = back();
    d_posVector[atBack] = POSITION_SENTINEL;
    d_image[atBack] = T();
    d_list.pop_back();
  }

 private:

  size_t allocated() const {
    Assert(d_posVector.size() == d_image.size());
    return d_posVector.size();
  }

  void increaseSize(Key max){
    Assert(max >= allocated());
    d_posVector.resize(max+1, POSITION_SENTINEL);
    d_image.resize(max+1);
  }

  /** Swaps a member x to the back of d_list. */
  void swapToBack(Key x){
    Assert(isKey(x));

    Position currentPos = d_posVector[x];
    Key atBack = back();

    d_list[currentPos] = atBack;
    d_posVector[atBack] = currentPos;

    Position last = size() - 1;

    d_list[last] = x;
    d_posVector[x] = last;
  }
}; /* class DenseMap<T> */

class ArithVarSetNew {
private:
  typedef DenseMap<bool> BackingMap;
  BackingMap d_map;
public:
  typedef BackingMap::const_iterator const_iterator;

  size_t size() const { return d_map.size(); }
  bool empty() const { return d_map.empty(); }

  void purge() { d_map.purge(); }
  void clear() { d_map.clear(); }

  bool isMember(ArithVar x) const{ return d_map.isKey(x); }

  void add(ArithVar x){
    Assert(!isMember(x));
    return d_map.set(x, true);
  }

  void softAdd(ArithVar x){ return d_map.set(x, true); }
  void remove(ArithVar x){ return d_map.remove(x); }

  const_iterator begin() const{ return d_map.begin(); }
  const_iterator end() const{ return d_map.end(); }

  ArithVar back() { return d_map.back(); }
  void pop_back() { d_map.pop_back(); }

};

/**
 * ArithVarMultiset
 */
class ArithVarMultiset {
private:
  typedef DenseMap<uint32_t> BackingMap;
  BackingMap d_map;

public:
  typedef BackingMap::const_iterator const_iterator;

  ArithVarMultiset() :  d_map() {}

  size_t size() const { return d_map.size(); }
  bool empty() const { return d_map.empty(); }

  void purge() { d_map.purge(); }
  void clear() { d_map.clear(); }

  bool isMember(ArithVar x) const{ return d_map.isKey(x); }

  void add(ArithVar x){
    if(d_map.isKey(x)){
      d_map.set(x, d_map.get(x)+1);
    }else{
      d_map.set(x,1);
    }
  }

  void remove(ArithVar x){ return d_map.remove(x); }

  uint32_t count(ArithVar x) const {
    if(d_map.isKey(x)){
      return d_map[x];
    }else {
      return 0;
    }
  }

  const_iterator begin() const{ return d_map.begin(); }
  const_iterator end() const{ return d_map.end(); }
  ArithVar back() { return d_map.back(); }
  void pop_back() { d_map.pop_back(); }

 //  size_t size() const {
 //    return d_list.size();
 //  }

 //  bool empty() const {
 //    return d_list.empty();
 //  }

 //  size_t allocated() const {
 //    Assert(d_posVector.size() == d_counts.size());
 //    return d_posVector.size();
 //  }

 //  void purge() {
 //    for(VarList::const_iterator i=d_list.begin(), endIter=d_list.end(); i!= endIter; ++i){
 //      d_posVector[*i] = ARITHVAR_SENTINEL;
 //      d_counts[*i] = 0;
 //    }
 //    d_list.clear();
 //    Assert(empty());
 //  }

 //  void increaseSize(ArithVar max){
 //    Assert(max >= allocated());
 //    d_posVector.resize(max+1, ARITHVAR_SENTINEL);
 //    d_counts.resize(max+1, 0);
 //  }

 //  void increaseSize(){
 //    increaseSize(allocated());
 //  }

 //  bool isMember(ArithVar x) const{
 //    if( x >=  allocated()){
 //      return false;
 //    }else{
 //      Assert(x <  allocated());
 //      return d_posVector[x] != ARITHVAR_SENTINEL;
 //    }
 //  }

 //  /**
 //   * Invalidates iterators.
 //   */
 //  void addMultiset(ArithVar x){
 //    if( x >=  allocated()){
 //      increaseSize(x);
 //    }
 //    if(d_counts[x] == 0){
 //      d_posVector[x] = size();
 //      d_list.push_back(x);
 //    }
 //    d_counts[x]++;
 //  }

 //  unsigned count(ArithVar x){
 //    if( x >=  allocated()){
 //      return 0;
 //    }else{
 //      return d_counts[x];
 //    }
 //  }

 //  const_iterator begin() const{ return d_list.begin(); }
 //  const_iterator end() const{ return d_list.end(); }

 //  const VarList& getList() const{
 //    return d_list;
 //  }

 //  /** Invalidates iterators */
 //  void remove(ArithVar x){
 //    Assert(isMember(x));
 //    swapToBack(x);
 //    Assert(d_list.back() == x);
 //    pop_back();
 //  }

 //  ArithVar pop_back() {
 //    Assert(!empty());
 //    ArithVar atBack = d_list.back();
 //    d_posVector[atBack] = ARITHVAR_SENTINEL;
 //    d_counts[atBack] = 0;
 //    d_list.pop_back();
 //    return atBack;
 //  }

 // private:

 //  /** This should be true of all x < allocated() after every operation. */
 //  bool wellFormed(ArithVar x){
 //    if(d_posVector[x] == ARITHVAR_SENTINEL){
 //      return true;
 //    }else{
 //      return d_list[d_posVector[x]] == x;
 //    }
 //  }

 //  /** Swaps a member x to the back of d_list. */
 //  void swapToBack(ArithVar x){
 //    Assert(isMember(x));

 //    unsigned currentPos = d_posVector[x];
 //    ArithVar atBack = d_list.back();

 //    d_list[currentPos] = atBack;
 //    d_posVector[atBack] = currentPos;

 //    d_list[size() - 1] = x;
 //    d_posVector[x] = size() - 1;
 //  }
};


class CDArithVarSet {
private:

  class RemoveIntCleanup {
  private:
    std::vector<bool>& d_set;
  public:
    RemoveIntCleanup(std::vector<bool>& set)
      : d_set(set)
    {}

    void operator()(ArithVar* p){
      ArithVar x = *p;
      Assert(d_set[x]);
      d_set[x] = false;
    }
  };

  std::vector<bool> d_set;
  context::CDList<ArithVar, RemoveIntCleanup> d_list;

public:
  CDArithVarSet(context::Context* c)
    : d_set(), d_list(c, true, RemoveIntCleanup(d_set))
  { }

  /** This cannot be const as garbage collection is done lazily. */
  bool contains(ArithVar x) const{
    if(x < d_set.size()){
      return d_set[x];
    }else{
      return false;
    }
  }

  void insert(ArithVar x){
    Assert(!contains(x));
    if(x >= d_set.size()){
      d_set.resize(x+1, false);
    }
    d_list.push_back(x);
    d_set[x] = true;
  }
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
