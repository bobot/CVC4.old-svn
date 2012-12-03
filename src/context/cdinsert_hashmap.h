/*********************                                                        */
/*! \file cdtrail_hashmap.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent hashmap built using trail of elements
 **
 ** Context-dependent hashmap that explicitly keeps track of its full edit
 ** history.  This is similar in functionality to CDHashMap with fewer
 ** capabilites, with the advantage of potentially being much lighter in memory
 ** usage.  If it is used a "write-once per context" fashion, it can use up to
 ** %X percent of the memory as CDHashMaps. The cost is that it explicitly keeps
 ** its full edit history.
 **
 ** Insertions to the map are done with respect to a context.
 ** Insertions can be done in two manors either with insert() or insertSafe().
 **  - insert(k,d) inserts the key data pair into the hashtable and returns a false if it overwrote
 **   the previous value. This always extends the trail length.
 **  - insertSafe(k,d) inserts key data pair into the hashtable only if the value is not already
 **   there. It returns true, if an element was added. This conditionally extends the trail length
 **   if it returns true.
 **
 ** Iterating over const_iterators has amortized time proportional to O(trail length).
 **
 ** contains() and operator[] are slightly faster than using stl style iterator comparisons:
 **  find(), end(), etc.
 **/


#include "cvc4_private.h"

#pragma once

#include "context/context.h"
#include <utility>
#include <ext/hash_map>
#include <deque>
#include "util/cvc4_assert.h"
#include "util/output.h"


namespace CVC4 {
namespace context {


template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class InsertHashMap {
public:
  typedef std::pair<Key, Data> value_type;

private:
  typedef std::deque<Key> KeyVec;
public:
  typedef typename KeyVec::const_iterator key_iterator;

private:
  typedef __gnu_cxx::hash_map<Key, Data, HashFcn> HashMap;
  typedef typename HashMap::iterator HM_iterator;

public:
  typedef typename HashMap::const_iterator const_iterator;

private:
  HashMap d_hashMap;
  KeyVec d_keys;

public:

  const_iterator begin() const{
    return d_hashMap.end();
  }
  const_iterator find(const Key& k) const{
    return d_hashMap.find(k);
  }
  const_iterator end() const{
    return d_hashMap.end();
  }

  key_iterator key_begin() const{
    return d_keys.begin();
  }
  key_iterator key_end() const{
    return d_keys.end();
  }

  bool empty() const { return d_keys.empty(); }
  size_t size() const { return d_keys.size(); }

  bool contains(const Key& k) const {
    return find(k) != end();
  }

  const Data& operator[](const Key& k) const {
    const_iterator ci = find(k);
    Assert(ci != end());
    return (*ci).second;
  }

  void insert(const Key& k, const Data& d){
    Assert(!contains(k));
    d_hashMap.insert(std::make_pair(k, d));
    d_keys.push_back(k);
  }

  bool insert_safe(const Key& k, const Data& d){
    HM_iterator it = d_hashMap.find(k);

    if(it == d_hashMap.end()){
      insert(k, d);
      return true;
    }else{
      return false;
    }
  }

  void pop_back(){
    Assert(!empty());
    const Key& back = d_keys.back();
    d_hashMap.erase(back);

    Debug("TrailHashMap") <<"TrailHashMap pop_back " << size() << " " << back << std::endl;
    d_keys.pop_back();
  }

  void pop_to_size(size_t s){
    while(size() > s){
      pop_back();
    }
  }
};/* class TrailHashMap<> */

template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class CDInsertHashMap : public ContextObj {
private:
  typedef InsertHashMap<Key, Data, HashFcn> IHM;
  typedef typename IHM::value_type value_type;
public:
  typedef typename IHM::const_iterator const_iterator;
  typedef typename IHM::key_iterator key_iterator;
private:

  IHM* d_insertMap;

  size_t d_size;

  /**
   * Private copy constructor used only by save().  d_list and
   * d_sizeAlloc are not copied: only the base class information and
   * d_size are needed in restore.
   */
  CDInsertHashMap(const CDInsertHashMap<Key, Data, HashFcn>& l) :
    ContextObj(l),
    d_insertMap(NULL),
    d_size(l.d_size){
    Debug("CDInsertHashMap") << "copy ctor: " << this
                    << " from " << &l
                    << " size " << d_size << std::endl;
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current size to a copy using the copy constructor (the
   * pointer and the allocated size are *not* copied as they are not
   * restored on a pop).  The saved information is allocated using the
   * ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDInsertHashMap<Key, Data, HashFcn>(*this);
    Debug("CDInsertHashMap") << "save " << this
                            << " at level " << this->getContext()->getLevel()
                            << " size at " << this->d_size
                            << " d_list is " << this->d_insertMap
                            << " data:" << data << std::endl;
    return data;
  }
protected:
  /**
   * Implementation of mandatory ContextObj method restore: simply
   * restores the previous size.  Note that the list pointer and the
   * allocated size are not changed.
   */
  void restore(ContextObj* data) {
    Debug("CDInsertHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " data == " << data
                            << " d_insertMap == " << this->d_insertMap << std::endl;
    size_t oldSize = ((CDInsertHashMap<Key, Data, HashFcn>*)data)->d_size;
    d_insertMap->pop_to_size(oldSize);
    d_size = oldSize;
    Assert(d_insertMap->size() == d_size);
    Debug("CDInsertHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " size back to " << this->d_size << std::endl;
  }
public:

 /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDInsertHashMap(Context* context) :
    ContextObj(context),
    d_insertMap(new IHM()),
    d_size(0){
    Assert(d_insertMap->size() == d_size);
  }

  /**
   * Destructor: delete the list
   */
  ~CDInsertHashMap() throw(AssertionException) {
    this->destroy();
    delete d_insertMap;
  }

  /** Returns true if the queue is empty in the current context. */
  bool empty() const{
    return d_size == 0;
  }

  size_t size() const {
    return d_insertMap->size();
  }

  void insert(const Key& k, const Data& d){
    makeCurrent();
    ++d_size;
    d_insertMap->insert(k, d);
    Assert(d_insertMap->size() == d_size);
  }

  bool insert_safe(const Key& k, const Data& d){
    bool res = d_insertMap->insert_safe(k, d);
    if(res){
      makeCurrent();
      ++d_size;
    }
    Assert(d_insertMap->size() == d_size);
    return res;
  }

  bool contains(const Key& k) const {
    return d_insertMap->contains(k);
  }

  const Data& operator[](const Key& k) const {
    return (*d_insertMap)[k];
  }

  const_iterator find(const Key& k) const {
    return d_insertMap->find(k);
  }
  const_iterator begin() const{
    return d_insertMap->begin();
  }
  const_iterator end() const{
    return d_insertMap->end();
  }

};/* class CDInsertHashMap<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */
