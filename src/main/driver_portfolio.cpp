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

void doCommand(SmtEngine&, Command*, Options&);

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
    if(options->sharingFilterByLength > 0) {
      if(lemma.getNumChildren() > options->sharingFilterByLength)
        return;
    }
    ++cnt;
    Debug("sharing") << d_tag << ": " << lemma << std::endl;
    expr::pickle::Pickle pkl;
    try{
      d_pickler.toPickle(lemma, pkl);
      d_sharedChannel->push(pkl);
      if(Trace.isOn("showSharing") and options->thread_id == 0) {
	*(Options::current()->out) << "thread #0: " << lemma << endl;
      }
    }catch(expr::pickle::PicklingException& p){
      Debug("sharing::blocked") << lemma << std::endl;
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
    Debug("lemmaInputChannel") << "hasNewLemma" << endl;
    return !d_sharedChannel->empty();
  }

  Expr getNewLemma() {
    Debug("lemmaInputChannel") << "getNewLemma" << endl;
    expr::pickle::Pickle pkl = d_sharedChannel->pop();

    Expr e = d_pickler.fromPickle(pkl);
    if(Trace.isOn("showSharing") and Options::current()->thread_id == 0) {
      *(Options::current()->out) << "thread #1: " << e << endl;
    }
    return e;
  }

};/* class PortfolioLemmaInputChannel */



int runCvc4(int argc, char *argv[], Options& options) {

  // Timer statistic till we have support in cluster
  timeval tim;
  gettimeofday(&tim, NULL);
  double t_start = tim.tv_sec+(tim.tv_usec/1000000.0);

  // For the signal handlers' benefit
  pOptions = &options;

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

  int numThreads = options.threads;

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

  StatisticsRegistry driverStatisticsRegistry;
  theStatisticsRegistry.registerStat_((&driverStatisticsRegistry));

  // Options
  //options.showSharing = true;

  Options options1 = options;
  Options options2 = options;
  options1.pivotRule = Options::MINIMUM;
  options2.pivotRule = Options::MAXIMUM;
  options1.thread_id = 0;
  options2.thread_id = 1;

  // Create the expression manager
  ExprManager* exprMgr = new ExprManager(options1);

  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic* statFilenameReg =
    new RegisterStatistic(&driverStatisticsRegistry, &s_statFilename);

  // Parse commands until we are done
  Command* cmd;
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

  /* Currently all code assumes a maximum of two threads */
  assert(numThreads <= 2);

  /* Output to string stream  */
  
  stringstream ss_out(stringstream::out);
  stringstream ss_out2(stringstream::out);
  if(options.verbosity == 0 or options.separateOutput) {
    options1.out = &ss_out;
    options2.out = &ss_out2;
  }

  /* Sharing channels */
  SharedChannel<channelFormat> *channelsOut[2], *channelsIn[2];

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
  ExprManager* exprMgr2 = new ExprManager(options2);

  ExprManagerMapCollection* vmaps = new ExprManagerMapCollection();

  Command *seq2 = seq->exportTo(exprMgr2, *vmaps);

  /* Add StatisticRegistries to GlobalRegistry */

  /* Lemma output channel */
  options1.lemmaOutputChannel =
    new PortfolioLemmaOutputChannel("thread #0",
                                    channelsOut[0],
                                    exprMgr,
                                    vmaps->d_to,
                                    vmaps->d_from);
  options2.lemmaOutputChannel =
    new PortfolioLemmaOutputChannel("thread #1",
                                    channelsOut[1], exprMgr2,
                                    vmaps->d_from, vmaps->d_to);

  options1.lemmaInputChannel =
    new PortfolioLemmaInputChannel("thread #0", channelsIn[0], exprMgr);
  options2.lemmaInputChannel =
    new PortfolioLemmaInputChannel("thread #1", channelsIn[1], exprMgr2);

  /* Portfolio */
  function <Result()> fns[2];

  fns[0] = boost::bind(doSmt, boost::ref(*exprMgr), seq, boost::ref(options1));
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
  // RegisterStatistic statSatResultReg(*exprMgr, &s_statSatResult);

  if(options.statistics) {
    theStatisticsRegistry.flushInformation(*options.err);
  }

  if(options.separateOutput) {
    *options.out << ss_out.str() ;
    *options.out << "--- Seperator ---" << endl;
    *options.out << ss_out2.str() ;
  }

  // destruction is causing segfaults, let us just exit
  exit(returnValue);

  delete vmaps;

  delete statFilenameReg;

  delete seq;
  delete exprMgr;

  delete seq2;
  delete exprMgr2;

  if(options.statistics) {
    gettimeofday(&tim, NULL);
    double t_end=tim.tv_sec+(tim.tv_usec/1000000.0);
    cout.precision(6);
    *options.err << "real time: " << t_end-t_start << "s\n";
    int th0_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(options.lemmaOutputChannel)).cnt;
    int th1_lemcnt = (*static_cast<PortfolioLemmaOutputChannel*>(options2.lemmaOutputChannel)).cnt;
    *options.err << "lemmas shared by thread #0: " << th0_lemcnt << endl;
    *options.err << "lemmas shared by thread #1: " << th1_lemcnt << endl;
    *options.err << "sharing rate: " << double(th0_lemcnt+th1_lemcnt)/(t_end-t_start)
                 << " lem/sec" << endl;
    *options.err << "winner: #" << (winner == 0 ? 0 : 1) << endl;
  }

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

void printUsage(Options& options) {
  stringstream ss;
  ss << "usage: " << options.binary_name << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  Options::printUsage( ss.str(), *options.out );
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
    doCommand(smt, cmd, options);

    return smt.getStatusOfLastCommand();
  } catch(OptionException& e) {
    *pOptions->out << "unknown" << endl;
    cerr << "CVC4 Error:" << endl << e << endl;
    printUsage(*pOptions);
    exit(1);
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 Error:" << endl << e << endl;
    if(pOptions->statistics) {
      pStatistics->flushInformation(*pOptions->err);
    }
    exit(1);
  } catch(bad_alloc) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 ran out of memory." << endl;
    if(pOptions->statistics) {
      pStatistics->flushInformation(*pOptions->err);
    }
    exit(1);
  } catch(...) {
#ifdef CVC4_COMPETITION_MODE
    *pOptions->out << "unknown" << endl;
#endif
    *pOptions->err << "CVC4 threw an exception of unknown type." << endl;
    exit(1);
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
