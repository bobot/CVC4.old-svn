#include "util/stats.h"

using namespace CVC4;

StatisticsRegistry::StatSet StatisticsRegistry::d_registeredStats;

std::string Stat::s_delim(",");

void StatisticsRegistry::flushStatistics(std::ostream& out){

#ifdef CVC4_STATISTICS_ON
  for(StatSet::iterator i=d_registeredStats.begin();i != d_registeredStats.end();++i){
    Stat* s = *i;
    s->flushStat(out);
    out << std::endl;
  }
#endif

}


