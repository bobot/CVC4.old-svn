/*********************                                                        */
/*! \file stats.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters, kshitij
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Statistics utility classes
 **
 ** Statistics utility classes, including classes for holding (and referring
 ** to) statistics, the statistics registry, and some other associated
 ** classes.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__STATS_H
#define __CVC4__STATS_H

#include <string>
#include <ostream>
#include <sstream>
#include <iomanip>
#include <set>
#include <ctime>
#include <vector>

#include "util/Assert.h"
#include "lib/clock_gettime.h"

namespace CVC4 {

#ifdef CVC4_STATISTICS_ON
#  define __CVC4_USE_STATISTICS true
#else
#  define __CVC4_USE_STATISTICS false
#endif

class ExprManager;

class CVC4_PUBLIC Stat;

inline std::ostream& operator<<(std::ostream& os, const ::timespec& t);

/**
 * The main statistics registry.  This registry maintains the list of
 * currently active statistics and is able to "flush" them all.
 */
class CVC4_PUBLIC StatisticsRegistry {
private:
  /** A helper class for comparing two statistics */
  struct StatCmp {
    inline bool operator()(const Stat* s1, const Stat* s2) const;
  };/* class StatisticsRegistry::StatCmp */

  /** A type for a set of statistics */
  typedef std::set< Stat*, StatCmp > StatSet;

  /** The set of currently active statistics */
  StatSet d_registeredStats;

  /** Private copy constructor undefined (no copy permitted). */
  StatisticsRegistry(const StatisticsRegistry&) CVC4_UNDEFINED;

public:

  /** Construct a statistics registry */
  StatisticsRegistry() { }

  /** An iterator type over a set of statistics */
  typedef StatSet::const_iterator const_iterator;

  /** Get a pointer to the current statistics registry */
  static StatisticsRegistry* current();

  /** Flush all statistics to the given output stream. */
  void flushStatistics(std::ostream& out, std::string d_tag = "");

  /** Register a new statistic, making it active. */
  static void registerStat(Stat* s) throw(AssertionException);

  /** Register a new statistic */
  void registerStat_(Stat* s) throw(AssertionException);

  /** Unregister an active statistic, making it inactive. */
  static void unregisterStat(Stat* s) throw(AssertionException);

  /** Unregister a new statistic */
  void unregisterStat_(Stat* s) throw(AssertionException);

  /**
   * Get an iterator to the beginning of the range of the set of active
   * (registered) statistics.
   */
  static const_iterator begin();

  /**
   * Get an iterator to the end of the range of the set of active
   * (registered) statistics.
   */
  static const_iterator end();

};/* class StatisticsRegistry */


/**
 * The base class for all statistics.
 *
 * This base class keeps the name of the statistic and declares the (pure)
 * virtual function flushInformation().  Derived classes must implement
 * this function and pass their name to the base class constructor.
 *
 * This class also (statically) maintains the delimiter used to separate
 * the name and the value when statistics are output.
 */
class CVC4_PUBLIC Stat {
private:
  /** The name of this statistic */
  std::string d_name;

  /**
   * The delimiter between name and value to use when outputting a
   * statistic.
   */
  static std::string s_delim;

public:

  /**
   * Construct a statistic with the given name.  Debug builds of CVC4
   * will throw an assertion exception if the given name contains the
   * statistic delimiter string.
   */
  Stat(const std::string& name) throw(CVC4::AssertionException) :
    d_name(name) {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(d_name.find(s_delim) == std::string::npos);
    }
  }

  /** Destruct a statistic.  This base-class version does nothing. */
  virtual ~Stat() {}

  /**
   * Flush the value of this statistic to an output stream.  Should
   * finish the output with an end-of-line character.
   */
  virtual void flushInformation(std::ostream& out) const = 0;

  /**
   * Flush the name,value pair of this statistic to an output stream.
   * Uses the statistic delimiter string between name and value.
   *
   * May be redefined by a child class
   */
  virtual void flushStat(std::ostream& out) const {
    if(__CVC4_USE_STATISTICS) {
      out << d_name << s_delim;
      flushInformation(out);
    }
  }

  /** Get the name of this statistic. */
  const std::string& getName() const {
    return d_name;
  }

  /** Get the value of this statistic as a string. */
  std::string getValue() const {
    std::stringstream ss;
    flushInformation(ss);
    return ss.str();
  }

};/* class Stat */

inline bool StatisticsRegistry::StatCmp::operator()(const Stat* s1,
                                                    const Stat* s2) const {
  return s1->getName() < s2->getName();
}

/**
 * A class to represent a "read-only" data statistic of type T.  Adds to
 * the Stat base class the pure virtual function getData(), which returns
 * type T, and flushInformation(), which outputs the statistic value to an
 * output stream (using the same existing stream insertion operator).
 *
 * Template class T must have stream insertion operation defined:
 * std::ostream& operator<<(std::ostream&, const T&)
 */
template <class T>
class CVC4_PUBLIC ReadOnlyDataStat : public Stat {
public:
  /** The "payload" type of this data statistic (that is, T). */
  typedef T payload_t;

  /** Construct a read-only data statistic with the given name. */
  ReadOnlyDataStat(const std::string& name) :
    Stat(name) {
  }

  /** Get the value of the statistic. */
  virtual const T& getData() const = 0;

  /** Flush the value of the statistic to the given output stream. */
  void flushInformation(std::ostream& out) const {
    if(__CVC4_USE_STATISTICS) {
      out << getData();
    }
  }

};/* class DataStat<T> */


/**
 * A data statistic class.  This class extends a read-only data statistic
 * with assignment (the statistic can be set as well as read).  This class
 * adds to the read-only case a pure virtual function setData(), thus
 * providing the basic interface for a data statistic: getData() to get the
 * statistic value, and setData() to set it.
 *
 * As with the read-only data statistic class, template class T must have
 * stream insertion operation defined:
 * std::ostream& operator<<(std::ostream&, const T&)
 */
template <class T>
class CVC4_PUBLIC DataStat : public ReadOnlyDataStat<T> {
public:

  /** Construct a data statistic with the given name. */
  DataStat(const std::string& name) :
    ReadOnlyDataStat<T>(name) {
  }

  /** Set the data statistic. */
  virtual void setData(const T&) = 0;

};/* class DataStat<T> */


/**
 * A data statistic that references a data cell of type T,
 * implementing getData() by referencing that memory cell, and
 * setData() by reassigning the statistic to point to the new
 * data cell.  The referenced data cell is kept as a const
 * reference, meaning the referenced data is never actually
 * modified by this class (it must be externally modified for
 * a reference statistic to make sense).  A common use for
 * this type of statistic is to output a statistic that is kept
 * outside the statistics package (for example, one that's kept
 * by a theory implementation for internal heuristic purposes,
 * which is important to keep even if statistics are turned off).
 *
 * Template class T must have an assignment operator=().
 */
template <class T>
class CVC4_PUBLIC ReferenceStat : public DataStat<T> {
private:
  /** The referenced data cell */
  const T* d_data;

public:
  /**
   * Construct a reference stat with the given name and a reference
   * to NULL.
   */
  ReferenceStat(const std::string& name) :
    DataStat<T>(name),
    d_data(NULL) {
  }

  /**
   * Construct a reference stat with the given name and a reference to
   * the given data.
   */
  ReferenceStat(const std::string& name, const T& data) :
    DataStat<T>(name),
    d_data(NULL) {
    setData(data);
  }

  /** Set this reference statistic to refer to the given data cell. */
  void setData(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = &t;
    }
  }

  /** Get the value of the referenced data cell. */
  const T& getData() const {
    if(__CVC4_USE_STATISTICS) {
      return *d_data;
    } else {
      Unreachable();
    }
  }

};/* class ReferenceStat<T> */


/**
 * A data statistic that keeps a T and sets it with setData().
 *
 * Template class T must have an operator=() and a copy constructor.
 */
template <class T>
class CVC4_PUBLIC BackedStat : public DataStat<T> {
protected:
  /** The internally-kept statistic value */
  T d_data;

public:

  /** Construct a backed statistic with the given name and initial value. */
  BackedStat(const std::string& name, const T& init) :
    DataStat<T>(name),
    d_data(init) {
  }

  /** Set the underlying data value to the given value. */
  void setData(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = t;
    }
  }

  /** Identical to setData(). */
  BackedStat<T>& operator=(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = t;
    }
    return *this;
  }

  /** Get the underlying data value. */
  const T& getData() const {
    if(__CVC4_USE_STATISTICS) {
      return d_data;
    } else {
      Unreachable();
    }
  }

};/* class BackedStat<T> */


/**
 * A wrapper Stat for another Stat.
 *
 * This type of Stat is useful in cases where a module (like the
 * CongruenceClosure module) might keep its own statistics, but might
 * be instantiated in many contexts by many clients.  This makes such
 * a statistic inappopriate to register with the StatisticsRegistry
 * directly, as all would be output with the same name (and may be
 * unregistered too quickly anyway).  A WrappedStat allows the calling
 * client (say, TheoryUF) to wrap the Stat from the client module,
 * giving it a globally unique name.
 */
template <class Stat>
class CVC4_PUBLIC WrappedStat : public ReadOnlyDataStat<typename Stat::payload_t> {
  typedef typename Stat::payload_t T;

  const ReadOnlyDataStat<T>& d_stat;

  /** Private copy constructor undefined (no copy permitted). */
  WrappedStat(const WrappedStat&) CVC4_UNDEFINED;
  /** Private assignment operator undefined (no copy permitted). */
  WrappedStat<T>& operator=(const WrappedStat&) CVC4_UNDEFINED;

public:

  /**
   * Construct a wrapped statistic with the given name that wraps the
   * given statistic.
   */
  WrappedStat(const std::string& name, const ReadOnlyDataStat<T>& stat) :
    ReadOnlyDataStat<T>(name),
    d_stat(stat) {
  }

  /** Get the data of the underlying (wrapped) statistic. */
  const T& getData() const {
    if(__CVC4_USE_STATISTICS) {
      return d_stat.getData();
    } else {
      Unreachable();
    }
  }

};/* class WrappedStat<T> */


/**
 * A backed integer-valued (64-bit signed) statistic.
 * This doesn't functionally differ from its base class BackedStat<int64_t>,
 * except for adding convenience functions for dealing with integers.
 */
class CVC4_PUBLIC IntStat : public BackedStat<int64_t> {
public:

  /**
   * Construct an integer-valued statistic with the given name and
   * initial value.
   */
  IntStat(const std::string& name, int64_t init) :
    BackedStat<int64_t>(name, init) {
  }

  /** Increment the underlying integer statistic. */
  IntStat& operator++() {
    if(__CVC4_USE_STATISTICS) {
      ++d_data;
    }
    return *this;
  }

  /** Increment the underlying integer statistic by the given amount. */
  IntStat& operator+=(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      d_data+= val;
    }
    return *this;
  }

  /** Keep the maximum of the current statistic value and the given one. */
  void maxAssign(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      if(d_data < val) {
        d_data = val;
      }
    }
  }

  /** Keep the minimum of the current statistic value and the given one. */
  void minAssign(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      if(d_data > val) {
        d_data = val;
      }
    }
  }

};/* class IntStat */


/**
 * The value for an AverageStat is the running average of (e1, e_2, ..., e_n),
 *   (e1 + e_2 + ... + e_n)/n,
 * where e_i is an entry added by an addEntry(e_i) call.
 * The value is initially always 0.
 * (This is to avoid making parsers confused.)
 *
 * A call to setData() will change the running average but not reset the
 * running count, so should generally be avoided.  Call addEntry() to add
 * an entry to the average calculation.
 */
class CVC4_PUBLIC AverageStat : public BackedStat<double> {
private:
  /**
   * The number of accumulations of the running average that we
   * have seen so far.
   */
  uint32_t d_count;
  double d_sum;

public:
  /** Construct an average statistic with the given name. */
  AverageStat(const std::string& name) :
    BackedStat<double>(name, 0.0), d_count(0), d_sum(0.0) {
  }

  /** Add an entry to the running-average calculation. */
  void addEntry(double e) {
    if(__CVC4_USE_STATISTICS) {
      ++d_count;
      d_sum += e;
      setData(d_sum / d_count);
    }
  }

};/* class AverageStat */

template <class T>
class CVC4_PUBLIC ListStat : public Stat{
private:
  typedef std::vector<T> List;
  List d_list;
public:

  /**
   * Construct an integer-valued statistic with the given name and
   * initial value.
   */
  ListStat(const std::string& name) : Stat(name) {}
  ~ListStat() {}

  void flushInformation(std::ostream& out) const{
    if(__CVC4_USE_STATISTICS) {
      typename List::const_iterator i = d_list.begin(), end =  d_list.end();
      out << "[";
      if(i != end){
        out << *i;
        ++i;
        for(; i != end; ++i){
          out << ", " << *i;
        }
      }
      out << "]";
    }
  }

  ListStat& operator<<(const T& val){
    if(__CVC4_USE_STATISTICS) {
      d_list.push_back(val);
    }
    return (*this);
  }

};/* class ListStat */

class CVC4_PUBLIC StatsRegistryStat : public Stat {
private:
  StatisticsRegistry* d_reg;
public:
  StatsRegistryStat(const std::string& name) : Stat(name) {}
  StatsRegistryStat(const std::string& name, StatisticsRegistry *reg) :
    Stat(name),
    d_reg(reg) {
  }

  void flushInformation(std::ostream& out) const {
    if(__CVC4_USE_STATISTICS) {
      d_reg->flushStatistics(out, getName() + "::");
    }
  }

  void flushStat(std::ostream &out) const {
    // overridden to avoid the name being printed
    if(__CVC4_USE_STATISTICS) {
      d_reg->flushStatistics(out, getName() + "::");
    }
  }
};/* class StatsRegistryStat */

/****************************************************************************/
/* Some utility functions for ::timespec                                    */
/****************************************************************************/

/** Compute the sum of two timespecs. */
inline ::timespec& operator+=(::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  Assert(a.tv_nsec >= 0 && a.tv_nsec < nsec_per_sec);
  Assert(b.tv_nsec >= 0 && b.tv_nsec < nsec_per_sec);
  a.tv_sec += b.tv_sec;
  long nsec = a.tv_nsec + b.tv_nsec;
  Assert(nsec >= 0);
  if(nsec < 0) {
    nsec += nsec_per_sec;
    --a.tv_sec;
  }
  if(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    ++a.tv_sec;
  }
  Assert(nsec >= 0 && nsec < nsec_per_sec);
  a.tv_nsec = nsec;
  return a;
}

/** Compute the difference of two timespecs. */
inline ::timespec& operator-=(::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  Assert(a.tv_nsec >= 0 && a.tv_nsec < nsec_per_sec);
  Assert(b.tv_nsec >= 0 && b.tv_nsec < nsec_per_sec);
  a.tv_sec -= b.tv_sec;
  long nsec = a.tv_nsec - b.tv_nsec;
  if(nsec < 0) {
    nsec += nsec_per_sec;
    --a.tv_sec;
  }
  if(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    ++a.tv_sec;
  }
  Assert(nsec >= 0 && nsec < nsec_per_sec);
  a.tv_nsec = nsec;
  return a;
}

/** Add two timespecs. */
inline ::timespec operator+(const ::timespec& a, const ::timespec& b) {
  ::timespec result = a;
  return result += b;
}

/** Subtract two timespecs. */
inline ::timespec operator-(const ::timespec& a, const ::timespec& b) {
  ::timespec result = a;
  return result -= b;
}

/** Compare two timespecs for equality. */
inline bool operator==(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec == b.tv_sec && a.tv_nsec == b.tv_nsec;
}

/** Compare two timespecs for disequality. */
inline bool operator!=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a == b);
}

/** Compare two timespecs, returning true iff a < b. */
inline bool operator<(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec < b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec < b.tv_nsec);
}

/** Compare two timespecs, returning true iff a > b. */
inline bool operator>(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec > b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec > b.tv_nsec);
}

/** Compare two timespecs, returning true iff a <= b. */
inline bool operator<=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a > b);
}

/** Compare two timespecs, returning true iff a >= b. */
inline bool operator>=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a < b);
}

/** Output a timespec on an output stream. */
inline std::ostream& operator<<(std::ostream& os, const ::timespec& t) {
  // assumes t.tv_nsec is in range
  return os << t.tv_sec << "."
            << std::setfill('0') << std::setw(8) << std::right << t.tv_nsec;
}


/**
 * A timer statistic.  The timer can be started and stopped
 * arbitrarily, like a stopwatch; the value of the statistic at the
 * end is the accumulated time over all (start,stop) pairs.
 */
class CVC4_PUBLIC TimerStat : public BackedStat< ::timespec > {

  // strange: timespec isn't placed in 'std' namespace ?!
  /** The last start time of this timer */
  ::timespec d_start;

  /** Whether this timer is currently running */
  bool d_running;

public:

  /**
   * Utility class to make it easier to call stop() at the end of a
   * code block.  When constructed, it starts the timer.  When
   * destructed, it stops the timer.
   */
  class CodeTimer {
    TimerStat& d_timer;

    /** Private copy constructor undefined (no copy permitted). */
    CodeTimer(const CodeTimer& timer) CVC4_UNDEFINED;
    /** Private assignment operator undefined (no copy permitted). */
    CodeTimer& operator=(const CodeTimer& timer) CVC4_UNDEFINED;

  public:
    CodeTimer(TimerStat& timer) : d_timer(timer) {
      d_timer.start();
    }
    ~CodeTimer() {
      d_timer.stop();
    }
  };/* class TimerStat::CodeTimer */

  /**
   * Construct a timer statistic with the given name.  Newly-constructed
   * timers have a 0.0 value and are not running.
   */
  TimerStat(const std::string& name) :
    BackedStat< ::timespec >(name, ::timespec()),
    d_running(false) {
    /* ::timespec is POD and so may not be initialized to zero;
     * here, ensure it is */
    d_data.tv_sec = d_data.tv_nsec = 0;
  }

  /** Start the timer. */
  void start() {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(!d_running);
      clock_gettime(CLOCK_MONOTONIC, &d_start);
      d_running = true;
    }
  }

  /**
   * Stop the timer and update the statistic value with the
   * accumulated time.
   */
  void stop() {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(d_running);
      ::timespec end;
      clock_gettime(CLOCK_MONOTONIC, &end);
      d_data += end - d_start;
      d_running = false;
    }
  }

};/* class TimerStat */


/**
 * To use a statistic, you need to declare it, initialize it in your
 * constructor, register it in your constructor, and deregister it in
 * your destructor.  Instead, this macro does it all for you (and
 * therefore also keeps the statistic type, field name, and output
 * string all in the same place in your class's header.  Its use is
 * like in this example, which takes the place of the declaration of a
 * statistics field "d_checkTimer":
 *
 *   KEEP_STATISTIC(TimerStat, d_checkTimer, "theory::uf::morgan::checkTime");
 *
 * If any args need to be passed to the constructor, you can specify
 * them after the string.
 *
 * The macro works by creating a nested class type, derived from the
 * statistic type you give it, which declares a registry-aware
 * constructor/destructor pair.
 */
#define KEEP_STATISTIC(_StatType, _StatField, _StatName, _CtorArgs...)  \
  struct Statistic_##_StatField : public _StatType {                    \
    Statistic_##_StatField() : _StatType(_StatName, ## _CtorArgs) {     \
      StatisticsRegistry::registerStat(this);                           \
    }                                                                   \
    ~Statistic_##_StatField() {                                         \
      StatisticsRegistry::unregisterStat(this);                         \
    }                                                                   \
  } _StatField

/**
 * Resource-acquisition-is-initialization idiom for statistics
 * registry.  Useful for stack-based statistics (like in the driver).
 * Generally, for statistics kept in a member field of class, it's
 * better to use the above KEEP_STATISTIC(), which does declaration of
 * the member, construction of the statistic, and
 * registration/unregistration.  This RAII class only does
 * registration and unregistration.
 */
class CVC4_PUBLIC RegisterStatistic {
  StatisticsRegistry* d_reg;
  Stat* d_stat;
public:
  RegisterStatistic(Stat* stat) :
      d_reg(StatisticsRegistry::current()),
      d_stat(stat) {
    Assert(d_reg != NULL, "There is no current statistics registry!");
    StatisticsRegistry::registerStat(d_stat);
  }

  RegisterStatistic(StatisticsRegistry* reg, Stat* stat) :
    d_reg(reg),
    d_stat(stat) {
    Assert(d_reg != NULL,
           "You need to specify a statistics registry"
           "on which to set the statistic");
    d_reg->registerStat_(d_stat);
  }

  RegisterStatistic(ExprManager& em, Stat* stat);

  ~RegisterStatistic() {
    d_reg->unregisterStat_(d_stat);
  }

};/* class RegisterStatistic */

#undef __CVC4_USE_STATISTICS

}/* CVC4 namespace */

#endif /* __CVC4__STATS_H */
