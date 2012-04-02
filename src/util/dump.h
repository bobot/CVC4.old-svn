/*********************                                                        */
/*! \file dump.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Dump utility classes and functions
 **
 ** Dump utility classes and functions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__DUMP_H
#define __CVC4__DUMP_H

#include "util/output.h"
#include "expr/command.h"
#include "util/Assert.h"

namespace CVC4 {

class CVC4_PUBLIC CVC4dumpstream {

#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
  std::ostream* d_os;
#endif /* CVC4_DUMPING && !CVC4_MUZZLE */

#ifdef CVC4_PORTFOLIO
  CommandSequence* d_commands;
#endif /* CVC4_PORTFOLIO */

public:
  CVC4dumpstream() throw()
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE) && defined(CVC4_PORTFOLIO)
    : d_os(NULL), d_commands(NULL)
#elif defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    : d_os(NULL)
#elif defined(CVC4_PORTFOLIO)
    : d_commands(NULL)
#endif /* CVC4_PORTFOLIO */
  { }

  CVC4dumpstream(std::ostream& os, CommandSequence *commands) throw()
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE) && defined(CVC4_PORTFOLIO)
    : d_os(&os), d_commands(commands)
#elif defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    : d_os(&os)
#elif defined(CVC4_PORTFOLIO)
    : d_commands(commands)
#endif /* CVC4_PORTFOLIO */
  { }

  CVC4dumpstream& operator<<(const Command& c) {
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    if(d_os != NULL) {
      (*d_os) << c << std::endl;
    }
#endif
#if defined(CVC4_PORTFOLIO)
    if(d_commands != NULL) {
      d_commands->addCommand(c.clone());
    }
#endif
    return *this;
  }
};/* class CVC4dumpstream */

/** The dump class */
class CVC4_PUBLIC DumpC {
  std::set<std::string> d_tags;
  CommandSequence *d_commands;

public:
  CVC4dumpstream operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return CVC4dumpstream(getStream(), d_commands);
    } else {
      return CVC4dumpstream();
    }
  }
  CVC4dumpstream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4dumpstream(getStream(), d_commands);
    } else {
      return CVC4dumpstream();
    }
  }

  void clear() { if(d_commands != NULL) d_commands->clear(); }
  const CommandSequence& getCommands() const { return *d_commands; }
  void disableCommands() {
    if(d_commands != NULL) {
      delete d_commands;
    } else {
      // What should we do here? Crash, raise exception or just...
      // ...ignore for now
      Assert(false, "Should not call this function twice, or if command sequence not being used");     // or may be not
    }
  }
  DumpC() { d_commands = new CommandSequence(); }
  ~DumpC() { if(d_commands != NULL) delete d_commands; }

  void declareVar(Expr e, std::string comment) {
    if(isOn("declarations")) {
      std::stringstream ss;
      ss << Expr::setlanguage(Expr::setlanguage::getLanguage(getStream())) << e;
      std::string s = ss.str();
      CVC4dumpstream(getStream(), d_commands)
        << CommentCommand(s + " is " + comment)
        << DeclareFunctionCommand(s, e.getType());
    }
  }

  bool on (const char* tag) { d_tags.insert(std::string(tag)); return true; }
  bool on (std::string tag) { d_tags.insert(tag); return true; }
  bool off(const char* tag) { d_tags.erase (std::string(tag)); return false; }
  bool off(std::string tag) { d_tags.erase (tag); return false; }
  bool off()                { d_tags.clear(); return false; }

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  std::ostream& setStream(std::ostream& os) { DumpOut.setStream(os); return os; }
  std::ostream& getStream() { return DumpOut.getStream(); }
};/* class DumpC */

/** The dump singleton */
extern DumpC DumpChannel CVC4_PUBLIC;

#define Dump ::CVC4::DumpChannel

}/* CVC4 namespace */

#endif /* __CVC4__DUMP_H */
