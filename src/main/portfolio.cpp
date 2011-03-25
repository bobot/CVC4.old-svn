#include <boost/function.hpp>
#include <boost/thread.hpp>
#include <boost/bind.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>

using namespace boost;

//struct thread_return_data {
//  int thread_id;
//  int returnValue;
  //string s_out;
  //  bool exceptionOccurred;       // beware: we assume this is false because global variable
  //  boost::exception_ptr exceptionPtr;
//} global_returnData;

mutex mutex_done;
mutex mutex_main_wait;
condition condition_var_main_wait;

bool global_flag_done = false;
int global_winner = -1;

template<typename S>
void runThread(int thread_id, function<S()> threadFn, S &returnValue)
{
  //  try {
  returnValue = threadFn();
  /*  
      } catch(...) {
      while(global_flag_done == false)
      if( mutex_done.try_lock() ) {
      global_flag_done = true;
      mutex_done.unlock();
      condition_var_main_wait.notify_all(); // we want main thread to quit
      }
      }
  */
  
  //  while(global_flag_done == false)
  if( mutex_done.try_lock() ) {
    //      CVC4::Notice("Thread " + intToString(thread_id) + "wins.\n");
    global_flag_done = true;
    global_winner = thread_id;
    mutex_done.unlock();
    condition_var_main_wait.notify_all(); // we want main thread to quit
  }
}

template<typename T, typename S>
std::pair<int,S> runPortfolio(int numThreads, 
			 function<T()> driverFn,
			 function<S()> threadFns[])
{
  thread thread_driver;
  thread threads[numThreads];
  S threads_returnValue[numThreads];
   
  for(int t=0; t<numThreads; ++t) {
    //CVC4::Notice("Driver thread: creating thread " + intToString(t) + "\n");
    threads[t] = thread(bind(runThread<S>, t, threadFns[t], ref(threads_returnValue[t]) ));
  }
  
  if(not driverFn.empty())
    thread_driver = boost::thread(driverFn);
  
  while(global_flag_done == false)
    condition_var_main_wait.wait(mutex_main_wait);

  for(int t=0; t<numThreads; ++t) {
    threads[t].interrupt();
    //threads[t].join();
  }
  
  if(not driverFn.empty())
    thread_driver.interrupt();

  return std::pair<int,S>(global_winner,threads_returnValue[global_winner]);
}
