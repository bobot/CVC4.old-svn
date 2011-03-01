#include <pthread.h>
#include <cstdio>
#include <iostream>
#include <cstdlib>

#include "main.h"
#include "util/output.h"

using namespace std;

// const int NUM_THREADS = 2;
pthread_mutex_t mutex_done = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_self_lock = PTHREAD_MUTEX_INITIALIZER;
/* pthread_cond_t condition_var_main_wait = PTHREAD_COND_INITIALIZER;
   pthread_mutex_t mutex_main_wait = PTHREAD_MUTEX_INITIALIZER; */

struct thread_data {
  int thread_id;
  int argc;
  char **argv;
};

/* This function should be moved somewhere else eventuall */
std::string intToString(int i)
{
    std::stringstream ss;
    std::string s;
    ss << i;
    s = ss.str();

    return s;
}

void *runCvcThread(void *argsData)
{
  thread_data *args;
  int returnValue;

  args = (thread_data *) argsData;

  returnValue=runCvc4(args->argc, args->argv);

  if( returnValue ) {

    pthread_mutex_lock( &mutex_done );   // we never unlock this

    fprintf(stderr, "INFO; Thread %ld wins. Rerturns %d.\n", args->thread_id, returnValue);
    //CVC4::Notice("Thread " + intToString(t) + ": creating thread " + intToString(t) + "\n" );

    exit(returnValue);  // hack for time being

    //pthread_cond_broadcast( &condition_var_main_wait ); //we want main thread to quit
  } else {
    pthread_exit(NULL);
  }
  return NULL;
}

int runCvc4Portfolio(int NUM_THREADS, int argc, char *argv[])
{
  pthread_t threads[NUM_THREADS];
  int rc;
  int t;

  for ( t=0; t<NUM_THREADS; ++t ) {
    fprintf(stderr, "INFO; In main: creating thread %ld\n", t);
    //CVC4::Notice("In main: creating thread " + intToString(t) + "\n" );
    thread_data *args = new thread_data;
    args->thread_id = t;
    args->argc = argc;
    args->argv = argv;
    rc = pthread_create(&threads[t], NULL, runCvcThread, (void *)args);
    if (rc) {
      fprintf(stderr, "ERROR; return code from pthread_create() is %d\n", rc);
      exit(-1);
    }
  }

  /* pthread_cond_wait(&condition_var_main_wait, &mutex_main_wait );
  printf("Main thread: Exiting program.\n");

  for ( t=0; t<NUM_THREADS; ++t ) {
    printf("In main: cancelling thread %ld\n", t);	
    rc = pthread_cancel(threads[t]);
    if (rc) {
      fprintf(stderr, "ERROR; return code from pthread_cancel() is %d\n", rc);
      exit(-1);  //if we can't cancel, we just exit
    }
  }
  printf("We are here\n"); */

  // Hack: Wait for others, because of problem with exceptions (didn't work)
  //for ( t=0; t<NUM_THREADS; ++t ) 
    //pthread_join(threads[t], NULL);
  //sleep(300); // Yet another hack (which didn't work either -- strange)
  //while(true) { }
  
  pthread_exit(NULL);
}
