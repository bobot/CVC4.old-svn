/*********************                                                        */
/*! \file options.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT.
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS_H
#define __CVC4__OPTIONS_H

#include <iostream>
#include <fstream>
#include <string>

#include "util/exception.h"
#include "util/language.h"
#include "util/lemma_output_channel.h"
#include "util/lemma_input_channel.h"
#include "util/tls.h"

#include <vector>

namespace CVC4 {

class ExprStream;

/** Class representing an option-parsing exception. */
class CVC4_PUBLIC OptionException : public CVC4::Exception {
public:
    OptionException(const std::string& s) throw() :
      CVC4::Exception("Error in option parsing: " + s) {
    }
};/* class OptionException */

struct CVC4_PUBLIC Options {

  /** The current Options in effect */
  static CVC4_THREADLOCAL(const Options*) s_current;

  /** Get the current Options in effect */
  static inline const Options* current() {
    return s_current;
  }

  /** The name of the binary (e.g. "cvc4") */
  std::string binary_name;

  /** Whether to collect statistics during this run */
  bool statistics;

  std::istream* in; /*< The input stream to use */
  std::ostream* out; /*< The output stream to use */
  std::ostream* err; /*< The error stream to use */

  /* -1 means no output */
  /* 0 is normal (and default) -- warnings only */
  /* 1 is warnings + notices so the user doesn't get too bored */
  /* 2 is chatty, giving statistical things etc. */
  /* with 3, the solver is slowed down by all the scrolling */
  int verbosity;

  /** The input language */
  InputLanguage inputLanguage;

  /** The output language */
  OutputLanguage outputLanguage;

  /** Should we print the help message? */
  bool help;

  /** Should we print the release information? */
  bool version;

  /** Should we print the language help information? */
  bool languageHelp;

  /** Should we exit after parsing? */
  bool parseOnly;

  /** Should we exit after preprocessing? */
  bool preprocessOnly;

  /** Should the parser do semantic checks? */
  bool semanticChecks;

  /** Should the TheoryEngine do theory registration? */
  bool theoryRegistration;

  /** Should the parser memory-map file input? */
  bool memoryMap;

  /** Should we strictly enforce the language standard while parsing? */
  bool strictParsing;

  /** Should we expand function definitions lazily? */
  bool lazyDefinitionExpansion;

  /** Parallel Only: Whether the winner is printed at the end or not. */
  bool printWinner;

  /** Enumeration of simplification modes (when to simplify). */
  typedef enum {
    /** Simplify the assertions as they come in */
    SIMPLIFICATION_MODE_INCREMENTAL,
    /** Simplify the assertions all together once a check is requested */
    SIMPLIFICATION_MODE_BATCH,
    /** Don't do simplification */
    SIMPLIFICATION_MODE_NONE
  } SimplificationMode;

  /** When/whether to perform nonclausal simplifications. */
  SimplificationMode simplificationMode;
  /** Whether the user set the nonclausal simplification mode. */
  bool simplificationModeSetByUser;

  /** Enumeration of decision strategies */
  typedef enum {
    /**
     * Decision engine doesn't do anything. Use sat solver's internal
     * heuristics
     */
    DECISION_STRATEGY_INTERNAL,
    /**
     * Use the justification heuristic
     */
    DECISION_STRATEGY_JUSTIFICATION
  } DecisionMode;
  /** When/whether to use any decision strategies */
  DecisionMode decisionMode;
  /** Whether the user set the decision strategy */
  bool decisionModeSetByUser;

  /** Whether to perform the static learning pass. */
  bool doStaticLearning;

  /** Whether we're in interactive mode or not */
  bool interactive;

  /**
   * Whether we're in interactive mode (or not) due to explicit user
   * setting (if false, we inferred the proper default setting).
   */
  bool interactiveSetByUser;

  /** Per-query resource limit. */
  unsigned long perCallResourceLimit;
  /** Cumulative resource limit. */
  unsigned long cumulativeResourceLimit;

  /** Per-query time limit in milliseconds. */
  unsigned long perCallMillisecondLimit;
  /** Cumulative time limit in milliseconds. */
  unsigned long cumulativeMillisecondLimit;

  /** Whether we should "spin" on a SIG_SEGV. */
  bool segvNoSpin;

  /** Whether we support SmtEngine::getValue() for this run. */
  bool produceModels;

  /** Whether we produce proofs. */
  bool proof;

  /** Whether we support SmtEngine::getAssignment() for this run. */
  bool produceAssignments;

  /** Whether we do typechecking at all. */
  bool typeChecking;

  /** Whether we do typechecking at Expr creation time. */
  bool earlyTypeChecking;

  /** Whether incemental solving (push/pop) */
  bool incrementalSolving;

  /** Replay file to use (for decisions); empty if no replay file. */
  std::string replayFilename;

  /** Replay stream to use (for decisions); NULL if no replay file. */
  ExprStream* replayStream;

  /** Log to write replay instructions to; NULL if not logging. */
  std::ostream* replayLog;

  /** Turn on and of arithmetic propagation. */
  bool arithPropagation;

  /**
   * Frequency for the sat solver to make random decisions.
   * Should be between 0 and 1.
   */
  double satRandomFreq;

  /**
   * Seed for Minisat's random decision procedure.
   * If this is 0, no random decisions will occur.
   **/
  double satRandomSeed;

  /** Variable activity decay factor for Minisat */
  double satVarDecay;

  /** Clause activity decay factor for Minisat */
  double satClauseDecay;

  /** Base restart interval for Minisat */
  int satRestartFirst;

  /** Restart interval increase factor for Minisat */
  double satRestartInc;

  /** The pivot rule for arithmetic */
  typedef enum { MINIMUM, BREAK_TIES, MAXIMUM } ArithPivotRule;
  ArithPivotRule pivotRule;

  /**
   * The number of pivots before Bland's pivot rule is used on a basic
   * variable in arithmetic.
   */
  uint16_t arithPivotThreshold;

  /**
   * The maximum row length that arithmetic will use for propagation.
   */
  uint16_t arithPropagateMaxLength;

  /**
   * Whether to do the symmetry-breaking preprocessing in UF as
   * described by Deharbe et al. in CADE 2011 (on by default).
   */
  bool ufSymmetryBreaker;

  /**
   * Whether the user explicitly requested that the symmetry
   * breaker be enabled or disabled.
   */
  bool ufSymmetryBreakerSetByUser;

  /** 
   * Whether to mini-scope quantifiers.
   * For example, forall x. ( P( x ) ^ Q( x ) ) will be rewritten to 
   * ( forall x. P( x ) ) ^ ( forall x. Q( x ) )
   */
  bool miniscopeQuant;

  /** 
   * Whether to mini-scope quantifiers based on formulas with no free variables.
   * For example, forall x. ( P( x ) V Q ) will be rewritten to 
   * ( forall x. P( x ) ) V Q
   */
  bool miniscopeQuantFreeVar;

  /** 
   * Whether to prenex (nested universal) quantifiers
   */
  bool prenexQuant;

  /**
   * Whether to variable-eliminate quantifiers.
   * For example, forall x y. ( P( x, y ) V x != c ) will be rewritten to
   *   forall y. P( c, y )
   */
  bool varElimQuant;

  /** 
   * Whether to CNF quantifier bodies
   */
  bool cnfQuant;

  /**
   * Whether to pre-skolemize quantifier bodies.
   * For example, forall x. ( P( x ) => (exists y. f( y ) = x) ) will be rewritten to
   *   forall x. P( x ) => f( S( x ) ) = x 
   */
  bool preSkolemQuant;

  /** 
   * Whether to use smart triggers
   */
  bool smartTriggers;

  /**
   * Whether to use finite model find heuristic
   */
  bool finiteModelFind;

  /** 
   * Whether to use region-based SAT for finite model finding 
   */
  bool fmfRegionSat;

  /**
   * Whether to use model-based exhaustive instantiation for finite model finding
   */
  bool fmfModelBasedInst;

  /** casc file. */
  std::string cascFilename;

  /** 
   * Whether to use efficient E-matching 
   */
  bool efficientEMatching;

  /** Enumeration of literal matching modes. */
  typedef enum {
    /** Do not consider polarity of patterns */
    LITERAL_MATCH_NONE,
    /** Consider polarity of boolean predicates only */
    LITERAL_MATCH_PREDICATE,
    /** Consider polarity of boolean predicates, as well as equalities */
    LITERAL_MATCH_EQUALITY,
  } LiteralMatchMode;

  /** When/whether to perform nonclausal simplifications. */
  LiteralMatchMode literalMatchMode;

  /**
   * Whether to do counterexample-based quantifier instantiation
   */
  bool cbqi;

  /**
   * Whether the user explicitly requested that counterexample-based
   * quantifier instantiation be enabled or disabled.
   */
  bool cbqiSetByUser;

  /** 
   * Whether to use user patterns for pattern-based instantiation
   */
  bool userPatternsQuant;

  /** 
   * Whether to use flip decision (useful when cbqi=true)
   */
  bool flipDecision;

  /**
   * Whether to do the linear diophantine equation solver
   * in Arith as described by Griggio JSAT 2012 (on by default).
   */
  bool dioSolver;

  /**
   * Whether to split (= x y) into (and (<= x y) (>= x y)) in
   * arithmetic preprocessing.
   */
  bool arithRewriteEq;

  /** The output channel to receive notfication events for new lemmas */
  LemmaOutputChannel* lemmaOutputChannel;
  LemmaInputChannel* lemmaInputChannel;

  /** Total number of threads */
  int threads;

  /** Thread configuration (a string to be passed to parseOptions) */
  std::vector<std::string> threadArgv;

  /** Thread ID, for internal use in case of multi-threaded run */
  int thread_id;

  /**
   * In multi-threaded setting print output of each thread at the
   * end of run, separated by a divider ("----").
   **/
  bool separateOutput;

  /** Filter depending on length of lemma */
  int sharingFilterByLength;

  Options();

  /**
   * Get a description of the command-line flags accepted by
   * parseOptions.  The returned string will be escaped so that it is
   * suitable as an argument to printf. */
  std::string getDescription() const;

  /**
   * Print overall command-line option usage message, prefixed by
   * "msg"---which could be an error message causing the usage
   * output in the first place, e.g. "no such option --foo"
   */
  static void printUsage(const std::string msg, std::ostream& out);

  /**
   * Print command-line option usage message for only the most-commonly
   * used options.  The message is prefixed by "msg"---which could be
   * an error message causing the usage output in the first place, e.g.
   * "no such option --foo"
   */
  static void printShortUsage(const std::string msg, std::ostream& out);

  /** Print help for the --lang command line option */
  static void printLanguageHelp(std::ostream& out);

  /**
   * Initialize the options based on the given command-line arguments.
   */
  int parseOptions(int argc, char* argv[]) throw(OptionException);

  /**
   * Set the output language based on the given string.
   */
  void setOutputLanguage(const char* str) throw(OptionException);

  /**
   * Set the input language based on the given string.
   */
  void setInputLanguage(const char* str) throw(OptionException);

};/* struct Options */

inline std::ostream& operator<<(std::ostream& out,
                                Options::SimplificationMode mode) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out,
                                Options::SimplificationMode mode) {
  switch(mode) {
  case Options::SIMPLIFICATION_MODE_INCREMENTAL:
    out << "SIMPLIFICATION_MODE_INCREMENTAL";
    break;
  case Options::SIMPLIFICATION_MODE_BATCH:
    out << "SIMPLIFICATION_MODE_BATCH";
    break;
  case Options::SIMPLIFICATION_MODE_NONE:
    out << "SIMPLIFICATION_MODE_NONE";
    break;
  default:
    out << "SimplificationMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, Options::ArithPivotRule rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS_H */
