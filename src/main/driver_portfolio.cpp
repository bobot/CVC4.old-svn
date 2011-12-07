#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <sys/time.h>           // for gettimeofday()

#include <queue>

#include <boost/thread.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>
#include <boost/lexical_cast.hpp>

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

#include "expr/pickler.h"
#include "util/channel.h"

#include "main/portfolio.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

/* Global variables */

namespace CVC4 {
  namespace main {

    StatisticsRegistry theStatisticsRegistry;

    /** A pointer to the StatisticsRegistry (the signal handlers need it) */
    CVC4::StatisticsRegistry* pStatistics;

  }/* CVC4::main namespace */
}/* CVC4 namespace */

/* Function declarations */

static bool doCommand(SmtEngine&, Command*, Options&);

Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options);

template<typename T>
void sharingManager(int numThreads,
                    SharedChannel<T>* channelsOut[],
                    SharedChannel<T>* channelsIn[]);


/* To monitor for activity on shared channels */
bool global_activity;
bool global_activity_true() { return global_activity; }
bool global_activity_false() { return not global_activity; }
boost::condition global_activity_cond;

typedef expr::pickle::Pickle channelFormat; /* Remove once we are using Pickle */

template <typename T>
class EmptySharedChannel: public SharedChannel<T> {
public:
  EmptySharedChannel(int) {}
  bool push(const T&) { return true; }
  T pop() { return T(); }
  bool empty() { return true; }
  bool full() { return false; }
};

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
private:
  string d_tag;
  SharedChannel<channelFormat>* d_sharedChannel;
  expr::pickle::MapPickler d_pickler;

public:
  int cnt;
  PortfolioLemmaOutputChannel(string tag,
                              SharedChannel<channelFormat> *c,
                              ExprManager* em,
                              VarMap& to,
                              VarMap& from) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em, to, from)
    ,cnt(0)
  {}

  void notifyNewLemma(Expr lemma) {
    if(Debug.isOn("disable-lemma-sharing")) return;
    const Options *options = Options::current();
    if(options->sharingFilterByLength >= 0) { // 0 would mean no-sharing effectively
      if( int(lemma.getNumChildren()) > options->sharingFilterByLength)
        return;
    }
    ++cnt;
    Trace("sharing") << d_tag << ": " << lemma << std::endl;
    expr::pickle::Pickle pkl;
    try{
      d_pickler.toPickle(lemma, pkl);
      d_sharedChannel->push(pkl);
      if(Trace.isOn("showSharing") and options->thread_id == 0) {
	*(Options::current()->out) << "thread #0: " << lemma << endl;
      }
    }catch(expr::pickle::PicklingException& p){
      Trace("sharing::blocked") << lemma << std::endl;
    }
  }

};

/* class PortfolioLemmaInputChannel */
class PortfolioLemmaInputChannel : public LemmaInputChannel {
private:
  string d_tag;
  SharedChannel<channelFormat>* d_sharedChannel;
  expr::pickle::Pickler d_pickler;

public:
  PortfolioLemmaInputChannel(string tag,
                             SharedChannel<channelFormat>* c,
                             ExprManager* em) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em){
  }

  bool hasNewLemma(){
    Debug("lemmaInputChannel") << d_tag << ": " << "hasNewLemma" << endl;
    return !d_sharedChannel->empty();
  }

  Expr getNewLemma() {
    Debug("lemmaInputChannel") << d_tag << ": " << "getNewLemma" << endl;
    expr::pickle::Pickle pkl = d_sharedChannel->pop();

    Expr e = d_pickler.fromPickle(pkl);
    if(Trace.isOn("showSharing") and Options::current()->thread_id == 0) {
      *(Options::current()->out) << "thread #1: " << e << endl;
    }
    return e;
  }

};/* class PortfolioLemmaInputChannel */



int runCvc4(int argc, char *argv[], Options& options) {

  // Timer statistic
  TimerStat s_totalTime("totalTime");
  TimerStat s_beforePortfolioTime("beforePortfolioTime");
  s_totalTime.start();
  s_beforePortfolioTime.start();

  // For the signal handlers' benefit
  pOptions = &options;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

  // Parse the options
  int firstArgIndex = options.parseOptions(argc, argv);

  progName = options.binary_name.c_str();

  if( options.help ) {
    printUsage(options, true);
    exit(1);
  } else if( options.languageHelp ) {
    Options::printLanguageHelp(*options.out);
    exit(1);
  } else if( options.version ) {
    *options.out << Configuration::about().c_str() << flush;
    exit(0);
  }

  int numThreads = options.threads;

  if(options.threadArgv.size() > size_t(numThreads)) {
    stringstream ss;
    ss << "--thread" << (options.threadArgv.size() - 1)
       << " configuration string seen but this portfolio will only contain "
       << numThreads << " thread(s)!";
    throw OptionException(ss.str());
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

  // Statistics init
  pStatistics = &theStatisticsRegistry;

  StatisticsRegistry driverStatisticsRegistry("driver");
  theStatisticsRegistry.registerStat_((&driverStatisticsRegistry));

  // Options
  //options.showSharing = true;

  /* Use satRandomSeed for generating random numbers, in particular satRandomSeed-s */
  srand((unsigned int)(-options.satRandomSeed));

  vector<Options> threadOptions;
  for(int i = 0; i < numThreads; ++i) {
    threadOptions.push_back(options);
    Options& opts = threadOptions.back();

    // Set thread identifier
    opts.thread_id = i;

    // If the random-seed is negative, pick a random seed randomly
    const double EPS = 1e-9;
    if(options.satRandomSeed < 0)
      opts.satRandomSeed = (double)rand();

    if(i < options.threadArgv.size() && !options.threadArgv[i].empty()) {
      // separate out the thread's individual configuration string
      stringstream optidss;
      optidss << "--thread" << i;
      string optid = optidss.str();
      int targc = 1;
      char* tbuf = strdup(options.threadArgv[i].c_str());
      char* p = tbuf;
      // string length is certainly an upper bound on size needed
      char** targv = new char*[options.threadArgv[i].size()];
      char** vp = targv;
      *vp++ = strdup(optid.c_str());
      p = strtok(p, " ");
      while(p != NULL) {
        *vp++ = p;
        ++targc;
        p = strtok(NULL, " ");
      }
      *vp++ = NULL;
      if(targc > 1) { // this is necessary in case you do e.g. --thread0="  "
        try {
          opts.parseOptions(targc, targv);
        } catch(OptionException& e) {
          stringstream ss;
          ss << optid << ": " << e.getMessage();
          throw OptionException(ss.str());
        }
        if(optind != targc) {
          stringstream ss;
          ss << "unused argument `" << targv[optind]
             << "' in thread configuration " << optid << " !";
          throw OptionException(ss.str());
        }
        if(opts.threads != numThreads || opts.threadArgv != options.threadArgv) {
          stringstream ss;
          ss << "not allowed to set thread options in " << optid << " !";
          throw OptionException(ss.str());
        }
      }
      free(targv[0]);
      delete targv;
      free(tbuf);
    }
  }

  // Create the expression manager
  ExprManager* exprMgrs[numThreads];
  exprMgrs[0] = new ExprManager(threadOptions[0]);
  ExprManager* exprMgr = exprMgrs[0]; // to avoid having to change code which uses that

  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic* statFilenameReg =
    new RegisterStatistic(&driverStatisticsRegistry, &s_statFilename);

  // Timer statistic
  RegisterStatistic* statTotatTime =
    new RegisterStatistic(&driverStatisticsRegistry, &s_totalTime);
  RegisterStatistic* statBeforePortfolioTime =
    new RegisterStatistic(&driverStatisticsRegistry, &s_beforePortfolioTime);
  // Ask: why doesn't this: driverStatisticsRegistry.registerStat(&s_totalTime) work?

  // Parse commands until we are done
  Command* cmd;
  bool status = true;
  CommandSequence* seq = new CommandSequence();
  if( options.interactive ) {
    InteractiveShell shell(*exprMgr, options);
    Message() << Configuration::getPackageName()
              << " " << Configuration::getVersionString();
    if(Configuration::isSubversionBuild()) {
      Message() << " [subversion " << Configuration::getSubversionBranchName()
                << " r" << Configuration::getSubversionRevision()
                << (Configuration::hasSubversionModifications() ?
                    " (with modifications)" : "")
                << "]";
    }
    Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
              << " assertions:"
              << (Configuration::isAssertionBuild() ? "on" : "off")
              << endl;
    while((cmd = shell.readCommand())) {
      seq->addCommand(cmd);
    }
  } else {
    ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename).
        withOptions(options);

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

  exprMgr = NULL;               // don't want to use that variable
                                // after this point

  /* Currently all code assumes a maximum of two threads */
  //assert(numThreads <= 2);

  assert(numThreads >= 1);      //do we need this?

  /* Output to string stream  */
  vector<stringstream*> ss_out(numThreads);
  if(options.verbosity == 0 or options.separateOutput) {
    for(int i=0;i <numThreads; ++i) {
      ss_out[i] = new stringstream;
      threadOptions[i].out = ss_out[i];
    }
  }

  /* Sharing channels */
  SharedChannel<channelFormat> *channelsOut[numThreads], *channelsIn[numThreads];

  for(int i=0; i<numThreads; ++i){
    if(Debug.isOn("channel-empty")) {
      channelsOut[i] = new EmptySharedChannel<channelFormat>(10000);
      channelsIn[i] = new EmptySharedChannel<channelFormat>(10000);
      continue;
    }
    channelsOut[i] = new SynchronizedSharedChannel<channelFormat>(10000);
    channelsIn[i] = new SynchronizedSharedChannel<channelFormat>(10000);
  }

  /* Duplication, Individualisation */
  ExprManagerMapCollection* vmaps;
  Command *seqs[numThreads];
  seqs[0] = seq;   seq = NULL;
  for(int i = 1; i < numThreads; ++i) {
    vmaps = new ExprManagerMapCollection();
    exprMgrs[i] = new ExprManager(threadOptions[i]);
    seqs[i] = seqs[0]->exportTo(exprMgrs[i], *vmaps);
  }

  /* Lemma output channel */
  if(numThreads == 2) {
    threadOptions[0].lemmaOutputChannel =
      new PortfolioLemmaOutputChannel("thread #0",
                                      channelsOut[0],
                                      exprMgrs[0],
                                      vmaps->d_to,
                                      vmaps->d_from);
    threadOptions[1].lemmaOutputChannel =
      new PortfolioLemmaOutputChannel("thread #1",
                                      channelsOut[1], exprMgrs[1],
                                      vmaps->d_from, vmaps->d_to);

    threadOptions[0].lemmaInputChannel =
      new PortfolioLemmaInputChannel("thread #0", channelsIn[0], exprMgrs[0]);
    threadOptions[1].lemmaInputChannel =
      new PortfolioLemmaInputChannel("thread #1", channelsIn[1], exprMgrs[1]);
  } else {
    // Disable sharing. We do not currently support it.
    for(int i=0; i<numThreads; ++i)
      threadOptions[i].sharingFilterByLength = 0;
  }

  /* Portfolio */
  function <Result()> fns[numThreads];

  for(int i = 0 ; i < numThreads ; ++i)
    fns[i] = boost::bind(doSmt, boost::ref(*exprMgrs[i]), seqs[i], boost::ref(threadOptions[i]));

  function <void()>
    smFn = boost::bind(sharingManager<channelFormat>, numThreads, channelsOut, channelsIn);

  s_beforePortfolioTime.stop();
  pair<int, Result> portfolioReturn = runPortfolio(numThreads, smFn, fns, false);
  int winner = portfolioReturn.first;
  Result result = portfolioReturn.second;

  cout << result << endl;
  if(options.printWinner){
    cout << "The winner is #" << winner << endl;
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
  // RegisterStatistic statSatResultReg(*exprMgr, &s_statSatResult);

  // Stop timers, enough work done
  s_totalTime.stop();

  if(options.statistics) {
    pStatistics->flushInformation(*options.err);
    *options.err << "Statistics printing complete " << endl;
  }

  if(options.separateOutput) {
    for(int i = 0; i < numThreads; ++i) {
      *options.out << "--- Output from thread #" << i << " ---" << endl;
      *options.out << ss_out[i]->str();
    }
  }

  /*if(options.statistics) {
    double totalTime = double(s_totalTime.getData().tv_sec) +
        double(s_totalTime.getData().tv_nsec)/1000000000.0;
    cout.precision(6);
    *options.err << "real time: " << totalTime << "s\n";
    int th0_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(options.lemmaOutputChannel)).cnt;
    int th1_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(threadOptions[1].lemmaOutputChannel)).cnt;
    *options.err << "lemmas shared by thread #0: " << th0_lemcnt << endl;
    *options.err << "lemmas shared by thread #1: " << th1_lemcnt << endl;
    *options.err << "sharing rate: " << double(th0_lemcnt+th1_lemcnt)/(totalTime)
                 << " lem/sec" << endl;
    *options.err << "winner: #" << (winner == 0 ? 0 : 1) << endl;
  }*/

  // destruction is causing segfaults, let us just exit
  exit(returnValue);

  delete vmaps;

  delete statFilenameReg;

  // delete seq;
  // delete exprMgr;

  // delete seq2;
  // delete exprMgr2;

  return returnValue;
}

/**** Code shared with driver.cpp ****/

namespace CVC4 {
  namespace main {/* Global options variable */
    CVC4_THREADLOCAL(Options*) pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;
  }
}

void printUsage(Options& options, bool full) {
  stringstream ss;
  ss << "usage: " << options.binary_name << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  if(full) {
    Options::printUsage( ss.str(), *options.out );
  } else {
    Options::printShortUsage( ss.str(), *options.out );
  }
}

/** Executes a command. Deletes the command after execution. */
static bool doCommand(SmtEngine& smt, Command* cmd, Options& options) {
  if( options.parseOnly ) {
    return true;
  }

  // assume no error
  bool status = true;

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      status = doCommand(smt, *subcmd, options) && status;
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
    status = status && cmd->ok();
  }

  return status;
}

/**** End of code shared with driver.cpp ****/

/** Create the SMT engine and execute the commands */
Result doSmt(ExprManager &exprMgr, Command *cmd, Options &options) {

  try {
    // For the signal handlers' benefit
    pOptions = &options;

    // Create the SmtEngine(s)
    SmtEngine smt(&exprMgr);

    // Register the statistics registry of the thread
    smt.getStatisticsRegistry()->setName("thread #" + boost::lexical_cast<string>(options.thread_id));
    theStatisticsRegistry.registerStat_( (Stat*)smt.getStatisticsRegistry() );

    // Execute the commands
    bool status = doCommand(smt, cmd, options);

    if(options.statistics) {
      smt.getStatisticsRegistry()->flushInformation(*options.err);
      *options.err << "Statistics printing of my thread complete " << endl;
    }

    return status ? smt.getStatusOfLastCommand() : Result::SAT_UNKNOWN;
  } catch(OptionException& e) {
    *pOptions->out << "unknown" << endl;
    cerr << "CVC4 Error:" << endl << e << endl;
    printUsage(*pOptions);
    return Result::SAT_UNKNOWN;
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 Error:" << endl << e << endl;
    if(pOptions->statistics) {
      pStatistics->flushInformation(*pOptions->err);
    }
    return Result::SAT_UNKNOWN;
  } catch(bad_alloc) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 ran out of memory." << endl;
    if(pOptions->statistics) {
      pStatistics->flushInformation(*pOptions->err);
    }
    return Result::SAT_UNKNOWN;
  } catch(...) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 threw an exception of unknown type." << endl;
    return Result::SAT_UNKNOWN;
  }
}

template<typename T>
void sharingManager(int numThreads,
                    SharedChannel<T> *channelsOut[], // out and in with respect
                    SharedChannel<T> *channelsIn[])  // to smt engines
{
  Debug("sharing") << "sharing: thread started " << std::endl;
  vector <int> cnt(numThreads); // Debug("sharing")

  vector< queue<T> > queues;
  for(int i=0; i < numThreads; ++i){
    queues.push_back(queue<T>());
  }

  boost::mutex mutex_activity;

  while(not boost::this_thread::interruption_requested()) {

    boost::this_thread::sleep(boost::posix_time::milliseconds(1));

    for(int t=0; t<numThreads; ++t) {

      if(channelsOut[t]->empty()) continue;      /* No activity on this channel */

      T data = channelsOut[t]->pop();

      if(Debug.isOn("sharing")) {
        ++cnt[t];
        Debug("sharing") << "sharing: Got data. Thread #" << t
                         << ". Chunk " << cnt[t] << std :: endl;
      }

      for(int u=0; u<numThreads; ++u) {
        if(u != t){
          Debug("sharing") << "sharing: adding to queue " << u << std::endl;
          queues[u].push(data);
        }
      }/* end of inner for: broadcast activity */

    } /* end of outer for: look for activity */

    for(int t=0; t<numThreads; ++t){
      while(!queues[t].empty() && !channelsIn[t]->full()){
        Debug("sharing") << "sharing: pushing on channel " << t << std::endl;
        T data = queues[t].front();
        channelsIn[t]->push(data);
        queues[t].pop();
      }
    }
  } /* end of infinite while */
  Debug("sharing") << "sharing: Interuppted, exiting." << std::endl;
}
