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

#include "expr/pickle.h"
#include "util/channel.h"

#include "main/portfolio.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

void doCommand(SmtEngine&, Command*, Options&);
Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options);

/* defined in sharing_manager.cpp */
template<typename T>
void sharingManager(int numThreads, 
		    SharedChannel<T>* channelsOut[], 
		    SharedChannel<T>* channelsIn[]);

typedef expr::pickle::Pickle channelFormat;	/* Remove once we are using Pickle */

bool global_activity;		// to track activity on output channel
bool global_activity_true() { return global_activity; }
bool global_activity_false() { return not global_activity; }
boost::condition global_activitycond;

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
  string d_tag;
  SharedChannel<channelFormat> *d_sharedChannel;
public:
  PortfolioLemmaOutputChannel(string tag, SharedChannel<channelFormat> *c) :
    d_tag(tag), 
    d_sharedChannel(c) {
  }

  void notifyNewLemma(Expr lemma) {
    Debug("sharing") << d_tag << ": " << lemma << std::endl;
    expr::pickle::Pickler pklr(lemma.getExprManager());
    expr::pickle::Pickle pkl;
    pklr.toPickle(lemma, pkl);
    d_sharedChannel->push(pkl);
    
    global_activity = true;	// HACK
    global_activitycond.notify_one();
  }

};/* class PortfolioLemmaOutputChannel */

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

  /* Currently all code assumes two threads */
  assert(numThreads == 2);

  /* Duplication, Individualisation */
  ExprManager* exprMgr2 = new ExprManager();
  VariableTypeMap* vmap = new VariableTypeMap();
  Command *seq2 = seq->exportTo(exprMgr2, *vmap);
  Options options2 = options;
  options.pivotRule = Options::MINIMUM;
  options2.pivotRule = Options::MAXIMUM;

  /* Output to string stream  */
  if(options.verbosity == 0) {
    stringstream ss_out(stringstream::out);
    options.out = &ss_out;
    stringstream ss_out2(stringstream::out);
    options2.out = &ss_out2;
  }

  /* Sharing channels */
  SharedChannel<channelFormat> *channelsOut[2], *channelsIn[2];
  
  for(int i=0; i<numThreads; ++i)
    channelsOut[i] = new SynchronizedSharedChannel<channelFormat>(10);

  
  /* Lemma output channel */
  options.lemmaOutputChannel = 
    new PortfolioLemmaOutputChannel("thread #0", channelsOut[0]);
  options2.lemmaOutputChannel = 
    new PortfolioLemmaOutputChannel("thread #1", channelsOut[1]);

  /* Portfolio */
  function <Result()> fns[numThreads];

  fns[0] = boost::bind(doSmt, boost::ref(*exprMgr), seq, boost::ref(options));
  fns[1] = boost::bind(doSmt, boost::ref(*exprMgr2), seq2, boost::ref(options2));

  function <void()>
    smFn = boost::bind(sharingManager<channelFormat>, numThreads, channelsOut, channelsIn);
  
  pair<int, Result> portfolioReturn = runPortfolio(numThreads, smFn, fns);
  int winner = portfolioReturn.first;
  Result result = portfolioReturn.second;

  cout << result << endl;
  if(options.printWinner){
    cout << "The winner is #" << (winner == 0 ? 0 : 1) << endl;
  }

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

/* Code shared with driver.cpp */

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

/* End of code shared with driver.cpp */

/** Create the SMT engine and execute the commands */
Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options) {
  // Create the SmtEngine(s)
  SmtEngine smt(&exprMgr, options);
  doCommand(smt, cmd, options);

  return smt.getStatusOfLastCommand();
}

template<typename T>
void sharingManager(int numThreads, 
		    SharedChannel<T> *channelsOut[], // out and in with respect 
		    SharedChannel<T> *channelsIn[])  // to smt engines
{
  Debug("sharing") << "sharing: thread started " << std::endl;
  vector <int> cnt(numThreads);	// Debug("sharing")
  boost::mutex mutex_activity;
  while(not boost::this_thread::interruption_requested()) {
    global_activitycond.wait(mutex_activity, global_activity_true);
    global_activity = false;
    for(int t=0; t<numThreads; ++t) {
      if(channelsOut[t]->empty()) continue;      /* No activity on this channel */
      cnt[t] ++;		// Debug("sharing")
      T data = channelsOut[t]->pop();
      Debug("sharing") << "sharing: Got data. Thread #" << t
		       << ". Chunk " << cnt[t] << std :: endl;
      for(int u=0; u<numThreads; ++u) {
	if(u != t)
	  Debug("sharing") << "sharing: Sending to " << u << std::endl;
      }/* end of inner for: broadcast activity */
    } /* end of outer for: look for activity */
  } /* end of infinite while */
  Debug("sharing") << "sharing: Interuppted, exiting." << std::endl;
}
