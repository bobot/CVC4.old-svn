
#ifndef __CVC4__STATS_H
#define __CVC4__STATS_H

#include <string>
#include <ostream>
#include <set>
#include "util/Assert.h"

namespace CVC4 {


#ifdef CVC4_STATISTICS_ON
#define USE_STATISTICS true
#else
#define USE_STATISTICS false
#endif

class Stat;

class StatisticsRegistry {
private:
  struct StatCmp;

  typedef std::set< Stat*, StatCmp > StatSet;
  static StatSet d_registeredStats;

public:
  static void flushStatistics(std::ostream& out);

  static inline void registerStat(Stat* s) throw (AssertionException);
}; /* class StatisticsRegistry */


class Stat {
private:
  std::string d_name;

  static std::string s_delim;

public:

  Stat(const std::string& s) throw (CVC4::AssertionException) : d_name(s)
  {
    if(USE_STATISTICS){
      AlwaysAssert(d_name.find(s_delim) == std::string::npos);
    }
  }

  virtual void flushInformation(std::ostream& out) const = 0;

  void flushStat(std::ostream& out) const{
    if(USE_STATISTICS){
      out << d_name << s_delim;
      flushInformation(out);
    }
  }

  const std::string& getName() const {
    return d_name;
  }
};

struct StatisticsRegistry::StatCmp {
  bool operator()(const Stat* s1, const Stat* s2) const
  {
    return (s1->getName()) < (s2->getName());
  }
};

inline void StatisticsRegistry::registerStat(Stat* s) throw (AssertionException){
  if(USE_STATISTICS){
    AlwaysAssert(d_registeredStats.find(s) == d_registeredStats.end());
    d_registeredStats.insert(s);
  }
}


template<class T>
class DataStat : public Stat{
public:
  DataStat(const std::string& s) : Stat(s) {}

  virtual const T& getData() const = 0;
  virtual void setData(const T&) = 0;

  void flushInformation(std::ostream& out) const{
    if(USE_STATISTICS){
      out << getData();
    }
  }
};

template <class T>
class ReferenceStat: public DataStat<T>{
private:
  const T* d_data;

public:
  ReferenceStat(const std::string& s): DataStat<T>(s), d_data(NULL){}

  ReferenceStat(const std::string& s, const T& data):ReferenceStat<T>(s){
    setData(data);
  }

  void setData(const T& t){
    if(USE_STATISTICS){
      d_data = &t;
    }
  }
  const T& getData() const{
    if(USE_STATISTICS){
      return *d_data;
    }else{
      Unreachable();
    }
  }
};

template <class T>
class BackedStat: public DataStat<T>{
protected:
  T d_data;

public:

  BackedStat(const std::string& s, const T& init): DataStat<T>(s), d_data(init)
  {}

  void setData(const T& t) {
    if(USE_STATISTICS){
      d_data = t;
    }
  }

  const T& getData() const{
    if(USE_STATISTICS){
      return d_data;
    }else{
      Unreachable();
    }
  }
};

class IntStat : public BackedStat<int64_t>{
public:

  IntStat(const std::string& s, int64_t init): BackedStat<int64_t>(s, init)
  {}

  IntStat& operator++(){
    if(USE_STATISTICS){
      ++d_data;
    }
    return *this;
  }

  IntStat& operator+=(int64_t val){
    if(USE_STATISTICS){
      d_data+= val;
    }
    return *this;
  }
};

#undef USE_STATISTICS

}/* CVC4 namespace */

#endif /* __CVC4__STATS_H */
