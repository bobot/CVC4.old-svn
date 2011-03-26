#include <cstdio>
#include <cstdlib>
#include <iostream>

#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>

#include "cvc4autoconfig.h"
#include "main/main.h"
#include "main/interactive_shell.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/Assert.h"
#include "util/configuration.h"
#include "util/options.h"
#include "util/output.h"
#include "util/result.h"
#include "util/stats.h"

#include "main/portfolio.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

// struct thread_return_data {
//   int thread_id;
//   string s_out;
//   int returnValue;
//   bool exceptionOccurred;       // beware: we assume this is false because global variable
//   boost::exception_ptr exceptionPtr;
// };

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
  string d_tag;
public:
  PortfolioLemmaOutputChannel(string tag) :
    d_tag(tag) {
  }

  void notifyNewLemma(Expr lemma) {
    std::cout << d_tag << ": " << lemma << std::endl;
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

// bool global_flag_done = false;
// thread_return_data global_returnData;

// boost::mutex mutex_done;
// boost::mutex mutex_main_wait;
// boost::condition condition_var_main_wait;

// void runCvc4Thread(int thread_id, int argc, char **argv, Options& options)
// {
//   int returnValue;

//   /* Output to string stream, so that */
//   stringstream ss_out(stringstream::out);
//   options.out = &ss_out;

//   try {
//     returnValue = runCvc4(argc, argv, options);
//   }catch(...){
//     while(global_flag_done == false)
//       if( mutex_done.try_lock() ) {
//         global_returnData.exceptionOccurred = true;
//         global_returnData.exceptionPtr = boost::current_exception();  // gets rid of exception?
//         global_returnData.returnValue = 1;

//         global_flag_done = true;
//         mutex_done.unlock();
//         condition_var_main_wait.notify_all(); //we want main thread to quit
//       }
//   }

//   if(returnValue) {
//     while(global_flag_done==false)
//       if( mutex_done.try_lock() ) {
//         CVC4::Notice("Thread " + intToString(thread_id) + "wins.\n"
//                      "Returns " + intToString(returnValue) + ".\n");

//         global_returnData.thread_id = thread_id;
//         global_returnData.returnValue = returnValue;
//         global_returnData.s_out = ss_out.str();

//         global_flag_done = true;
//         mutex_done.unlock();
//         condition_var_main_wait.notify_all(); //we want main thread to quit
//       }
//   }
// }

// int runCvc4Portfolio(int numThreads, int argc, char *argv[], Options& options)
// {
//   boost::thread threads[numThreads];

//   for(int t=0; t<numThreads; ++t) {
//     //CVC4::Notice("Driver thread: creating thread " + intToString(t) + "\n" );
//     Options o = options;
//     o.pivotRule = t == 0 ? Options::MINIMUM : Options::MAXIMUM;
//     o.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #" + intToString(t));
//     threads[t] = boost::thread(runCvc4Thread, t, argc, argv, o);
//   }

//   while(global_flag_done == false)
//     condition_var_main_wait.wait(mutex_main_wait);

//   if( global_returnData.exceptionOccurred )
//     boost::rethrow_exception( global_returnData.exceptionPtr );

//   CVC4::Notice("Driver thread: Exiting program. " + intToString(global_returnData.returnValue)
//                + " return value of the fastest thread.\n" );

//   cout << global_returnData.s_out;

//   //exit(global_returnData.returnValue);  // Hack, no longer needed, thanks to boost

//   for(int t=0; t<numThreads; ++t) {
//     CVC4::Notice("Driver thread: cancelling thread " + intToString(t) + "\n");
//     threads[t].interrupt();
//     threads[t].join();
//   }

//   return global_returnData.returnValue;
// }

void doCommand(SmtEngine&, Command*, Options&);
Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options);

int runCvc4Portfolio(int numThreads, int argc, char *argv[], Options& options)
{
  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

  // Parse the options
  int firstArgIndex = options.parseOptions(argc, argv);

  progName = options.binary_name.c_str();

  if( options.help ) {
    printUsage(options);
    exit(1);
  } else if( options.languageHelp ) {
    Options::printLanguageHelp(*options.out);
    exit(1);
  } else if( options.version ) {
    *options.out << Configuration::about().c_str() << flush;
    exit(0);
  }

  segvNoSpin = options.segvNoSpin;

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *options.out << unitbuf;
#endif

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!options.interactiveSetByUser) {
    options.interactive = inputFromStdin && isatty(fileno(stdin));
  }

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  ReferenceStat< const char* > s_statFilename("filename", filename);
  StatisticsRegistry::registerStat(&s_statFilename);

  if(options.inputLanguage == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      options.inputLanguage = language::input::LANG_CVC4;
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        options.inputLanguage = language::input::LANG_SMTLIB_V2;
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        options.inputLanguage = language::input::LANG_SMTLIB;
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        options.inputLanguage = language::input::LANG_CVC4;
      }
    }
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    Debug.setStream(CVC4::null_os);
    Trace.setStream(CVC4::null_os);
    Notice.setStream(CVC4::null_os);
    Chat.setStream(CVC4::null_os);
    Message.setStream(CVC4::null_os);
    Warning.setStream(CVC4::null_os);
  } else {
    if(options.verbosity < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(options.verbosity < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(options.verbosity < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }

    OutputLanguage language = language::toOutputLanguage(options.inputLanguage);
    Debug.getStream() << Expr::setlanguage(language);
    Trace.getStream() << Expr::setlanguage(language);
    Notice.getStream() << Expr::setlanguage(language);
    Chat.getStream() << Expr::setlanguage(language);
    Message.getStream() << Expr::setlanguage(language);
    Warning.getStream() << Expr::setlanguage(language);
  }


  // Create the expression manager
  ExprManager* exprMgr = new ExprManager(options);

  // Parse commands until we are done
  Command* cmd;
  CommandSequence* seq = new CommandSequence();
  if( options.interactive ) {
    InteractiveShell shell(*exprMgr,options);
    while((cmd = shell.readCommand())) {
      seq->addCommand(cmd);
    }
  } else {
    ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename, options);

    if( inputFromStdin ) {
      parserBuilder.withStreamInput(cin);
    }

    Parser *parser = parserBuilder.build();
    while((cmd = parser->nextCommand())) {
      seq->addCommand(cmd);
      // doCommand(smt, cmd, options);
      // delete cmd;
    }
    // Remove the parser
    delete parser;
  }

  // Brilliant, so what all do we have at this point?
  // - CommandSequence* seq has the sequence of commands
  // - ExprManager exprMgr(options) is the main expression manager

  // What do we need to do next?
  // - Create a second exprMgr, and import everything there

  // Duplication, Individualisation
  ExprManager* exprMgr2 = new ExprManager();
  VariableTypeMap* vmap = new VariableTypeMap();
  Command *seq2 = seq->exportTo(exprMgr2, *vmap);
  Options options2 = options;
  options.pivotRule = Options::MINIMUM;
  options2.pivotRule = Options::MAXIMUM;

  /* Output to string stream, so that */
  stringstream ss_out(stringstream::out);
  options.out = &ss_out;
  stringstream ss_out2(stringstream::out);
  options2.out = &ss_out2;

  /* Lemma output channel */
  // options.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #0");
  // options2.lemmaOutputChannel = new PortfolioLemmaOutputChannel("thread #1");


  assert(numThreads == 2);
  function <Result()> fns[numThreads];

  fns[0] = boost::bind(doSmt, boost::ref(*exprMgr), seq, boost::ref(options));
  fns[1] = boost::bind(doSmt, boost::ref(*exprMgr2), seq2, boost::ref(options2));

  pair<int, Result> portfolioReturn = runPortfolio(numThreads, function<void()>(), fns);
  int winner = portfolioReturn.first;
  Result result = portfolioReturn.second;

  cout << result << endl;
  //cout << "The winner is #" << (winner == 0 ? 0 : 1) << endl;

  Result satRes = result.asSatisfiabilityResult();
  int returnValue;
  if(satRes.isSat() == Result::SAT) {
    returnValue = 10;
  } else if(satRes.isSat() == Result::UNSAT) {
    returnValue = 20;
  } else {
    returnValue = 0;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif

  // ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  // StatisticsRegistry::registerStat(&s_statSatResult);

  // if(options.statistics) {
  //   StatisticsRegistry::flushStatistics(*options.err);
  // }

  // StatisticsRegistry::unregisterStat(&s_statSatResult);
  // StatisticsRegistry::unregisterStat(&s_statFilename);

  // destruction is causing segfaults, let us just exit
  //exit(returnValue);

  delete vmap;

  delete seq;
  delete exprMgr;

  delete seq2;
  delete exprMgr2;

  return returnValue;
}

/***** ***** ***** Copy from driver.cpp ***** ***** *****
 * Sorry, figured making a copy was best for now
 * Will reduce redundancy later
 */

namespace CVC4 {
  namespace main {/* Global options variable */
    //Options options;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;
  }
}

// no more % chars in here without being escaped; it's used as a
// printf() format string
/* const string usageMessage = "                 \
usage: %s [options] [input-file]\n\
\n\
Without an input file, or with `-', CVC4 reads from standard input.\n\
\n\
CVC4 options:\n";
*/
void printUsage(Options& options) {
  stringstream ss;
  ss << "usage: " << options.binary_name << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  Options::printUsage( ss.str(), *options.out );
}

// int runCvc4(int argc, char* argv[], Options& options) {


//   //doCommand(smt, &seq, options);


// }

/** Create the SMT engine and execute the commands */
Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options) {
  // Create the SmtEngine(s)
  SmtEngine smt(&exprMgr, options);
  doCommand(smt, cmd, options);

  return smt.getStatusOfLastCommand();
}

/** Executes a command. Deletes the command after execution. */
void doCommand(SmtEngine& smt, Command* cmd, Options& options) {
  if( options.parseOnly ) {
    return;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      doCommand(smt, *subcmd, options);
    }
  } else {
    if(options.verbosity > 0) {
      *options.out << "Invoking: " << *cmd << endl;
    }

    if(options.verbosity >= 0) {
      cmd->invoke(&smt, *options.out);
    } else {
      cmd->invoke(&smt);
    }
  }
}
