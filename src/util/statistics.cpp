/*********************                                                        */
/*! \file statistics.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/statistics.h"
#include "util/statistics_registry.h" // for details about class Stat

#include <typeinfo>

namespace CVC4 {

std::string StatisticsBase::s_regDelim("::");

bool StatisticsBase::StatCmp::operator()(const Stat* s1, const Stat* s2) const {
  return s1->getName() < s2->getName();
}

StatisticsBase::iterator::value_type StatisticsBase::iterator::operator*() const {
  return std::make_pair((*d_it)->getName(), (*d_it)->getValue());
}

StatisticsBase::StatisticsBase() :
  d_prefix(),
  d_stats() {
}

StatisticsBase::StatisticsBase(const StatisticsBase& stats) :
  d_prefix(stats.d_prefix),
  d_stats() {
}

StatisticsBase& StatisticsBase::operator=(const StatisticsBase& stats) {
  d_prefix = stats.d_prefix;
  return *this;
}

void Statistics::copyFrom(const StatisticsBase& stats) {
  // This is ugly, but otherwise we have to introduce a "friend" relation for
  // Base to its derived class (really obnoxious).
  StatSet::const_iterator i_begin = ((const Statistics*) &stats)->d_stats.begin();
  StatSet::const_iterator i_end = ((const Statistics*) &stats)->d_stats.end();
  for(StatSet::const_iterator i = i_begin; i != i_end; ++i) {
    SExprStat* p = new SExprStat((*i)->getName(), (*i)->getValue());
    d_stats.insert(p);
  }
}

void Statistics::clear() {
  for(StatSet::iterator i = d_stats.begin(); i != d_stats.end(); ++i) {
    delete *i;
  }
  d_stats.clear();
}

Statistics::Statistics(const StatisticsBase& stats) :
  StatisticsBase(stats) {
  copyFrom(stats);
}

Statistics::Statistics(const Statistics& stats) :
  StatisticsBase(stats) {
  copyFrom(stats);
}

Statistics::~Statistics() {
  clear();
}

Statistics& Statistics::operator=(const StatisticsBase& stats) {
  clear();
  this->StatisticsBase::operator=(stats);
  copyFrom(stats);

  return *this;
}

Statistics& Statistics::operator=(const Statistics& stats) {
  return this->operator=((const StatisticsBase&)stats);
}

StatisticsBase::const_iterator StatisticsBase::begin() const {
  return iterator(d_stats.begin());
}

StatisticsBase::const_iterator StatisticsBase::end() const {
  return iterator(d_stats.end());
}

void StatisticsBase::flushInformation(std::ostream &out) const {
#ifdef CVC4_STATISTICS_ON
  for(StatSet::iterator i = d_stats.begin();
      i != d_stats.end();
      ++i) {
    Stat* s = *i;
    if(d_prefix != "") {
      out << d_prefix << s_regDelim;
    }
    s->flushStat(out);
    out << std::endl;
  }
#endif /* CVC4_STATISTICS_ON */
}

SExpr StatisticsBase::getStatistic(std::string name) const {
  SExpr value;
  IntStat s(name, 0);
  StatSet::iterator i = d_stats.find(&s);
  if(i != d_stats.end()) {
    return (*i)->getValue();
  } else {
    return SExpr();
  }
}

void StatisticsBase::setPrefix(const std::string& prefix) {
  d_prefix = prefix;
}

}/* CVC4 namespace */
