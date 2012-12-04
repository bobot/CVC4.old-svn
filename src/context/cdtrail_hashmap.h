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
#include "context/cdtrail_hashmap_forward.h"
#include <utility>
#include <ext/hash_map>
#include <deque>
#include "util/cvc4_assert.h"
#include "util/output.h"


namespace CVC4 {
namespace context {


template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class TrailHashMap {
public:
  typedef std::pair<Key, Data> value_type;
  struct KDT {
    value_type d_kd;
    size_t d_prev;
    bool d_head;
    KDT(const Key& key, const Data& data, size_t prev, bool head = true):
      d_kd(std::make_pair(key, data)), d_prev(prev), d_head(true){ }
    KDT(){}
  };

private:
  typedef std::deque<KDT> KDTVec;
  typedef typename KDTVec::const_iterator KDTVec_const_iterator;

  typedef __gnu_cxx::hash_map<Key, size_t, HashFcn> PositionMap;
  typedef typename PositionMap::iterator PM_iterator;
  typedef typename PositionMap::const_iterator PM_const_iterator;

  PositionMap d_posMap;
  KDTVec d_kdts;
  size_t d_uniqueKeys;


  PM_iterator ncfind(const Key& k) {
    return d_posMap.find(k);
  }

  PM_const_iterator pmfind(const Key& k) const{
    return d_posMap.find(k);
  }
  PM_const_iterator pmend() const{
    return d_posMap.end();
  }

  bool selfLoop(size_t pos, const KDT& kdt) const {
    return pos == kdt.d_prev;
  }
public:
  class const_iterator {
    const TrailHashMap* d_container;
    KDTVec_const_iterator d_it;
    void findCurrent(){
      KDTVec_const_iterator end = d_container->d_kdts.end();
      while(d_it != end && !(*d_it).d_head){
        ++d_it;
      }
    }

  public:
    const_iterator(const TrailHashMap* con, KDTVec_const_iterator it)
    : d_container(con)
    , d_it(it){
      findCurrent();
    }

    const_iterator(const const_iterator& other)
    :  d_container(other.d_container)
    ,  d_it(other.d_it){
    }

    bool operator==(const const_iterator& other) const {
      return d_it == other.d_it;
    }
    bool operator!=(const const_iterator& other) const {
      return d_it != other.d_it;
    }
    inline const value_type& operator*() const {
      return (*d_it).d_kd;
    }
    /** Prefix increment */
    const_iterator& operator++() {
      ++d_it;
      findCurrent();
      return *this;
    }
  };
  const_iterator begin() const{
    return const_iterator(this, d_kdts.begin());
  }

  const_iterator end() const{
    return const_iterator(this, d_kdts.end());
  }

  bool empty() const { return d_kdts.empty(); }
  size_t trailSize() const { return d_kdts.size(); }
  size_t uniqueKeys() const { return d_uniqueKeys; }

  bool contains(const Key& k) const {
    return pmfind(k) != pmend();
  }

  /** DO NOT USE THIS UNLESS YOU ARE CONFIDENT THE CHANGES MAKE SENSE.*/
  Data& lookup(const Key& k){
    PM_iterator ci = ncfind(k);
    KDT& kdt = d_kdts[(*ci).second];
    return kdt.d_kd.second;
  }

  const Data& operator[](const Key& k) const {
    PM_const_iterator pci = pmfind(k);
    Assert(pci != pmend());
    return d_kdts[(*pci).second].d_kd.second;
  }

  const_iterator find(const Key& k) const {
    PM_const_iterator pci = pmfind(k);
    if(pci == pmend()){
      return end();
    }else{
      size_t pos = (*pci).second;
      return const_iterator(this, d_kdts.begin() + pos);
    }
  }

  std::pair<bool, bool> hasAfter(const Key& k, size_t pos) {
    PM_iterator it = ncfind(k);
    if(it != d_posMap.end()){
      return std::make_pair(true, (*it).second >= pos );
    }
    return std::make_pair(false, false);
  }

  bool push_back(const Key& k, const Data& d){
    std::pair<bool, bool> res = compacting_push_back(k, d, trailSize());
    return res.first;
  }

  std::pair<bool, bool> compacting_push_back(const Key& k, const Data& d, size_t threshold){
    size_t backPos = d_kdts.size();
    std::pair<PM_iterator, bool> res = d_posMap.insert(std::make_pair(k, backPos));
    if(!res.second){
      size_t& prevPosInPM = (*res.first).second;

      Assert(d_kdts[prevPosInPM].d_head);

      if(prevPosInPM < threshold){
        d_kdts.push_back(KDT(k,d, prevPosInPM));
        d_kdts[prevPosInPM].d_head = false;
        prevPosInPM = backPos;

        return std::make_pair(false, true);
      }else{
        d_kdts[prevPosInPM].d_kd.second = d;
        return std::make_pair(false, false);
      }
    }else{
      d_kdts.push_back(KDT(k,d, backPos));
      ++d_uniqueKeys;
      return std::make_pair(true, true);
    }
  }


  bool insert_no_overwrite(const Key& k, const Data& d){
    size_t backPos = d_kdts.size();
    std::pair<PM_iterator, bool> res = d_posMap.insert(std::make_pair(k, backPos));
    if(res.second){
      d_kdts.push_back(KDT(k,d, backPos));
      ++d_uniqueKeys;
    }
    Debug("TrailHashMap") <<"TrailHashMap insert" << k << " d " << d << " " << backPos << std::endl;
    return res.second;
  }

  void pop_back(){
    Assert(!empty());
    const KDT& back = d_kdts.back();
    const Key& k = back.d_kd.first;
    if(selfLoop(trailSize()-1, back)){
      d_posMap.erase(k);
      --d_uniqueKeys;
      Debug("TrailHashMap") <<"TrailHashMap pop_back erase " << trailSize() <<" " << std::endl;

    }else{
      Debug("TrailHashMap") <<"TrailHashMap reset " << trailSize() <<" " << " " << back.d_prev << std::endl;
      d_posMap[k] = back.d_prev;
      d_kdts[back.d_prev].d_head = true;
    }
    d_kdts.pop_back();
  }

  void pop_to_size(size_t s){
    while(trailSize() > s){
      pop_back();
    }
  }
};/* class TrailHashMap<> */

template <class Key, class Data, class HashFcn >
class CDTrailHashMap : public ContextObj {
private:
  typedef TrailHashMap<Key, Data, HashFcn> THM;
  typedef typename THM::value_type value_type;
public:
  typedef typename THM::const_iterator const_iterator;
private:

  THM* d_trailMap;

  size_t d_trailSize;
  size_t d_prevTrailSize;

  /**
   * Private copy constructor used only by save().  d_list and
   * d_sizeAlloc are not copied: only the base class information and
   * d_size are needed in restore.
   */
  CDTrailHashMap(const CDTrailHashMap<Key, Data, HashFcn>& l) :
    ContextObj(l),
    d_trailMap(NULL),
    d_trailSize(l.d_trailSize),
    d_prevTrailSize(l.d_prevTrailSize){
    Debug("CDTrailHashMap") << "copy ctor: " << this
                    << " from " << &l
                    << " size " << d_trailSize << std::endl;
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current size to a copy using the copy constructor (the
   * pointer and the allocated size are *not* copied as they are not
   * restored on a pop).  The saved information is allocated using the
   * ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDTrailHashMap<Key, Data, HashFcn>(*this);
    Debug("CDTrailHashMap") << "save " << this
                            << " at level " << this->getContext()->getLevel()
                            << " size at " << this->d_trailSize
                            << " d_list is " << this->d_trailMap
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
    Debug("CDTrailHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " data == " << data
                            << " d_trailMap == " << this->d_trailMap << std::endl;
    size_t oldSize = ((CDTrailHashMap<Key, Data, HashFcn>*)data)->d_trailSize;
    d_trailMap->pop_to_size(oldSize);
    d_trailSize = oldSize;
    Assert(d_trailMap->trailSize() == d_trailSize);

    d_prevTrailSize = ((CDTrailHashMap<Key, Data, HashFcn>*)data)->d_prevTrailSize;
    Debug("CDTrailHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " size back to " << this->d_trailSize << std::endl;
  }
public:

 /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDTrailHashMap(Context* context) :
    ContextObj(context),
    d_trailMap(new THM()),
    d_trailSize(0),
    d_prevTrailSize(0){
    Assert(d_trailMap->trailSize() == d_trailSize);
  }

  /**
   * Destructor: delete the list
   */
  ~CDTrailHashMap() throw(AssertionException) {
    this->destroy();
    delete d_trailMap;
  }

  void internalMakeCurrent () {
    if(!isCurrent()){
      makeCurrent();
      d_prevTrailSize = d_trailSize;
    }
  }

  /** Returns true if the queue is empty in the current context. */
  bool empty() const{
    return d_trailSize == 0;
  }

  size_t size() const {
    return d_trailMap->uniqueKeys();
  }

  bool insert(const Key& k, const Data& d){
    internalMakeCurrent();
    std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, d, d_prevTrailSize);
    if(res.second){
      ++d_trailSize;
    }
    Assert(d_trailMap->trailSize() == d_trailSize);
    return res.first;
  }

  bool insert_no_overwrite(const Key& k, const Data& d){
    bool res = d_trailMap->insert_no_overwrite(k, d);
    if(res){
      internalMakeCurrent();
      ++d_trailSize;
    }
    Assert(d_trailMap->trailSize() == d_trailSize);
    return res;
  }

  bool contains(const Key& k) const {
    return d_trailMap->contains(k);
  }

  const Data& operator[](const Key& k) const {
    return (*d_trailMap)[k];
  }
/*
  Data& operator[](const Key& k) {
    internalMakeCurrent();
    std::pair<bool, bool> res = d_trailMap->hasAfter(k, d_prevTrailSize);
    if(!res.first){
      std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, Data(), d_prevTrailSize);
      if(res.second){
        ++d_trailSize;
      }
    }else if(!res.second){
      std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, (*d_trailMap)[k], d_prevTrailSize);
      if(res.second){
        ++d_trailSize;
      }
    }
    return d_trailMap->lookup(k);
  }
*/
  const_iterator find(const Key& k) const {
    return d_trailMap->find(k);
  }
  const_iterator begin() const{
    return d_trailMap->begin();
  }
  const_iterator end() const{
    return d_trailMap->end();
  }

};/* class CDTrailHashMap<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */
