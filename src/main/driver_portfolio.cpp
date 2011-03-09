#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>

#include "main.h"
#include "util/output.h"
#include "util/options.h"

using namespace CVC4;
using namespace std;

struct thread_return_data {
  int thread_id;
  string s_out;
  int returnValue;
};

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
  string d_tag;
public:
  PortfolioLemmaOutputChannel(string tag) :
    d_tag(tag) {
  }

  void notifyNewLemma(Expr lemma) {
    //std::cout << d_tag << ": " << lemma << std::endl;
  }

};/* class PortfolioLemmaOutputChannel */

/* This function should be moved somewhere else eventuall */
std::string intToString(int i)
{
    std::stringstream ss;
    std::string s;
    ss << i;
    s = ss.str();

    return s;
}

bool global_flag_done = false;
thread_return_data global_returnData;

boost::mutex mutex_done;
boost::mutex mutex_main_wait;
boost::condition condition_var_main_wait; 

void runCvc4Thread(int thread_id, int argc, char **argv, Options& options)
{
  int returnValue;

  /* Output to string stream, so that */
  stringstream ss_out(stringstream::out);
  //options.out = &ss_out;
  returnValue = runCvc4(argc, argv, options);

  if(returnValue) {
    while(global_flag_done==false)
      if( mutex_done.try_lock() ) {
        CVC4::Notice("Thread " + intToString(thread_id) + "wins.\n"
                     "Returns " + intToString(returnValue) + ".\n");
    
        global_returnData.thread_id = thread_id;
        global_returnData.returnValue = returnValue;
        global_returnData.s_out = ss_out.str();
    
        global_flag_done = true;
        mutex_done.unlock();
        condition_var_main_wait.notify_all(); //we want main thread to quit
      }
  } 
}

int runCvc4Portfolio(int numThreads, int argc, char *argv[], Options& options)
{
  boost::thread threads[numThreads];

  for(int t=0; t<numThreads; ++t) {
    CVC4::Notice("Driver thread: creating thread " + intToString(t) + "\n" );
    Options o = options;
    o.pivotRule = t == 0 ? Options::MINIMUM : Options::MAXIMUM;
    o.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #" + intToString(t));
    threads[t] = boost::thread(runCvc4Thread, t, argc, argv, o);
  }
  
  while(global_flag_done == false)
    condition_var_main_wait.wait(mutex_main_wait);
  
  CVC4::Notice("Driver thread: Exiting program. " + intToString(global_returnData.returnValue)
               + " return value of the fastest thread.\n" );

  cout << global_returnData.s_out;
  
  //exit(global_returnData.returnValue);  // Hack, no longer needed, thanks to boost

  for(int t=0; t<numThreads; ++t) {
    CVC4::Notice("Driver thread: cancelling thread " + intToString(t) + "\n");
    threads[t].interrupt();
    threads[t].join();
  }
  
  return global_returnData.returnValue;
}
