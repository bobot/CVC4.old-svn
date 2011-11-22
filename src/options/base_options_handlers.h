#ifndef __CVC4__BASE_OPTIONS_HANDLERS_H
#define __CVC4__BASE_OPTIONS_HANDLERS_H

#include <iostream>
#include <string>
#include <sstream>

namespace CVC4 {
namespace options {

inline void increaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() + 1);
}

inline void decreaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() - 1);
}

inline OutputLanguage stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "cvc4" || optarg == "pl") {
    return language::output::LANG_CVC4;
  } else if(optarg == "smtlib" || optarg == "smt") {
    return language::output::LANG_SMTLIB;
  } else if(optarg == "smtlib2" || optarg == "smt2") {
    return language::output::LANG_SMTLIB_V2;
  } else if(optarg == "ast") {
    return language::output::LANG_AST;
  } else if(optarg == "auto") {
    return language::output::LANG_AUTO;
  }

  if(optarg != "help") {
    throw OptionException(std::string("unknown language for --output-lang: `") +
                          optarg + "'.  Try --output-lang help.");
  }

  options::languageHelp.set(true);
  return language::output::LANG_AUTO;
}

inline InputLanguage stringToInputLanguage(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "cvc4" || optarg == "pl" || optarg == "presentation") {
    return language::input::LANG_CVC4;
  } else if(optarg == "smtlib" || optarg == "smt") {
    return language::input::LANG_SMTLIB;
  } else if(optarg == "smtlib2" || optarg == "smt2") {
    return language::input::LANG_SMTLIB_V2;
  } else if(optarg == "auto") {
    return language::input::LANG_AUTO;
  }

  if(optarg != "help") {
    throw OptionException(std::string("unknown language for --lang: `") +
                          optarg + "'.  Try --lang help.");
  }

  options::languageHelp.set(true);
  return language::input::LANG_AUTO;
}

inline void addTraceTag(std::string option, std::string optarg) {
  Trace.on(optarg);
}

inline void addDebugTag(std::string option, std::string optarg) {
  Debug.on(optarg);
  Trace.on(optarg);
}

template <template <class U> class Cmp>
class comparator {
  long d_lbound;
  double d_dbound;
  bool d_hasLbound;

public:
  comparator(long l) throw() : d_lbound(l), d_dbound(0.0), d_hasLbound(true) {}
  comparator(double d) throw() : d_lbound(0), d_dbound(d), d_hasLbound(false) {}

  template <class T>
  void operator()(std::string option, const T& value) {
    if((d_hasLbound && !(Cmp<T>()(value, T(d_lbound)))) ||
       (!d_hasLbound && !(Cmp<T>()(value, T(d_dbound))))) {
      std::stringstream ss;
      ss << option << ": " << value << " is not a legal setting";
      throw OptionException(ss.str());
    }
  }
};/* class comparator */

struct greater : public comparator<std::greater> {
  greater(long l) throw() : comparator<std::greater>(l) {}
  greater(double d) throw() : comparator<std::greater>(d) {}
};/* struct greater */

struct greater_equal : public comparator<std::greater_equal> {
  greater_equal(long l) throw() : comparator<std::greater_equal>(l) {}
  greater_equal(double d) throw() : comparator<std::greater_equal>(d) {}
};/* struct greater_equal */

struct less : public comparator<std::less> {
  less(long l) throw() : comparator<std::less>(l) {}
  less(double d) throw() : comparator<std::less>(d) {}
};/* struct less */

struct less_equal : public comparator<std::less_equal> {
  less_equal(long l) throw() : comparator<std::less_equal>(l) {}
  less_equal(double d) throw() : comparator<std::less_equal>(d) {}
};/* struct less_equal */

struct not_equal : public comparator<std::not_equal_to> {
  not_equal(long l) throw() : comparator<std::not_equal_to>(l) {}
  not_equal(double d) throw() : comparator<std::not_equal_to>(d) {}
};/* struct not_equal_to */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__BASE_OPTIONS_HANDLERS_H */

