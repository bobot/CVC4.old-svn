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

bool global_flag_done = false;
thread_return_data global_returnData;

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

boost::mutex mutex_done;
boost::mutex mutex_main_wait;
boost::condition condition_var_main_wait; 
//pthread_mutex_t mutex_self_lock = PTHREAD_MUTEX_INITIALIZER;

//void *runCvc4Thread(void *argsData)
void runCvc4Thread(int argc, char **argv, Options options)
{
  int returnValue;

  /* Set some options so that we process the output before exiting */
  //stringstream sout(stringstream::out);
  //CVC4::main::options.out = &sout ;

  stringstream ss_out(stringstream::out);
  options.out = &ss_out;
  returnValue = runCvc4(argc, argv, options);

  if( returnValue ) {

    while(global_flag_done==false)
    if( mutex_done.try_lock() ) {

    //fprintf(stderr, "INFO; Thread %d wins. Rerturns %d.\n", args->thread_id, returnValue);
    //CVC4::Notice("Thread " + intToString(t) + ": creating thread " + intToString(t) + "\n" );
    
    //global_returnData.returnValue = boost::this_thread::get_id();
    global_returnData.returnValue = returnValue;
    global_returnData.s_out = ss_out.str();
    
    //exit(returnValue);  // hack for time being

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
    //fprintf(stderr, "INFO; In main: creating thread %d\n", t);
    //CVC4::Notice("In main: creating thread " + intToString(t) + "\n" );
    Options o = options;
    o.pivotRule = t == 0 ? Options::MINIMUM : Options::MAXIMUM;
    o.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #" + intToString(t));
    threads[t] = boost::thread(runCvc4Thread, argc, argv, o);
  }
  
  while(global_flag_done == false)
    condition_var_main_wait.wait(mutex_main_wait);
  //fprintf(stderr, "Main thread: Exiting program. %d return value of fastest thread \n", global_returnData.returnValue);
  
  cout << global_returnData.s_out;
  //cout << global_returnData.sout.str();
  exit(global_returnData.returnValue);

  /*  for ( t=0; t<NUM_THREADS; ++t ) {
    printf("In main: cancelling thread %d\n", t);	
    rc = pthread_cancel(threads[t]);
    if (rc) {
      //fprintf(stderr, "ERROR; return code from pthread_cancel() is %d\n", rc);
      exit(-1);  //if we can't cancel, we just exit
    }
    }

  // Hack: Wait for others, because of problem with exceptions (didn't work)
  //for ( t=0; t<NUM_THREADS; ++t ) 
    //pthread_join(threads[t], NULL);
  //sleep(300); // Yet another hack (which didn't work either -- strange)
  //while(true) { }
  
  pthread_exit(NULL);*/
  return 0;
}
