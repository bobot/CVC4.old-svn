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
  boost::thread::id thread_id;
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

class PortfolioDriver {
  static boost::mutex mutex_done;
  static boost::mutex mutex_main_wait;
  static boost::condition condition_var_main_wait; 
  static bool flag_done;
  static thread_return_data global_returnData;

  static void runThread(int argc, char **argv, Options options)
  {
    int returnValue;

    /* Set output to string to pass back to main thread */
    stringstream ss_out(stringstream::out);
    options.out = &ss_out;
    returnValue = runCvc4(argc, argv, options);

    if( returnValue ) {

      while(flag_done==false)	// Only one thread should output
        if( mutex_done.try_lock() ) {

          //fprintf(stderr, "INFO; Thread %d wins. Rerturns %d.\n", args->thread_id, returnValue);
          //CVC4::Notice("Thread " + intToString(t) + ": creating thread " + intToString(t) + "\n" );
    
          //global_returnData.returnValue = boost::this_thread::get_id();
          global_returnData.returnValue = returnValue;
          global_returnData.s_out = ss_out.str();
    
          //exit(returnValue);  // hack for time being

          flag_done = true;
          mutex_done.unlock();
          condition_var_main_wait.notify_all(); //we want main thread to quit
        }
    } 
  }

public:
  static int runPortfolio(int numThreads, int argc, char *argv[], Options& options)
  {
    boost::thread threads[numThreads];
    flag_done = false;

    for(int t=0; t<numThreads; ++t) {
      CVC4::Notice("In main: creating thread " + intToString(t) + "\n" );
      Options o = options;
      o.pivotRule = t == 0 ? Options::MINIMUM : Options::MAXIMUM;
      o.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #" + intToString(t));
      threads[t] = boost::thread(PortfolioDriver::runThread, argc, argv, o);
    }
  
    while(flag_done == false)
      condition_var_main_wait.wait(mutex_main_wait);
    //fprintf(stderr, "Main thread: Exiting program. %d return value of fastest thread \n", global_returnData.returnValue);
  
    cout << global_returnData.s_out;
    exit(global_returnData.returnValue);

    /*  for ( t=0; t<NUM_THREADS; ++t ) {
        printf("In main: cancelling thread %d\n", t);	
        rc = pthread_cancel(threads[t]);
        if (rc) {
        //fprintf(stderr, "ERROR; return code from pthread_cancel() is %d\n", rc);
        exit(-1);  //if we can't cancel, we just exit
        }
        }

        pthread_exit(NULL);*/
    return 0;
  }
}; /* class PortfolioDriver */

int runCvc4Portfolio(int argc, char *argv[], Options& options)
{
  PortfolioDriver::runPortfolio(2, argc, argv, options);
}
