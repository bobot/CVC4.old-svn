/*********************                                                        */
/*! \file theory_bv_rewrite_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once 

#include "cvc4_private.h"
#include "theory/theory.h"
#include "context/context.h"
#include "util/stats.h"
#include "theory/bv/theory_bv_utils.h"
#include <sstream>

namespace CVC4 {
namespace theory {
namespace bv {

enum RewriteRuleId {
  /// core rewrite rules
  EmptyRule,
  ConcatFlatten,
  ConcatExtractMerge,
  ConcatConstantMerge,
  ExtractExtract,
  ExtractWhole,
  ExtractConcat,
  ExtractConstant,
  FailEq,
  SimplifyEq,
  ReflexivityEq,
  /// operator elimination rules
  UgtToUlt,
  UgeToUle,
  SgeToSle,
  SgtToSlt,
  RepeatEliminate,
  RotateLeftEliminate,
  RotateRightEliminate,
  NandEliminate,
  NorEliminate,
  SdivEliminate,
  UdivEliminate,
  SmodEliminate,
  SremEliminate,
  ZeroExtendEliminate,
  // division by zero guards: rewrite a / b as b!=0 => a/b = ...
  DivZeroGuard
 };

inline std::ostream& operator << (std::ostream& out, RewriteRuleId ruleId) {
  switch (ruleId) {
  case EmptyRule:           out << "EmptyRule";           return out;
  case ConcatFlatten:       out << "ConcatFlatten";       return out;
  case ConcatExtractMerge:  out << "ConcatExtractMerge";  return out;
  case ConcatConstantMerge: out << "ConcatConstantMerge"; return out;
  case ExtractExtract:      out << "ExtractExtract";      return out;
  case ExtractWhole:        out << "ExtractWhole";        return out;
  case ExtractConcat:       out << "ExtractConcat";       return out;
  case ExtractConstant:     out << "ExtractConstant";     return out;
  case FailEq:              out << "FailEq";              return out;
  case SimplifyEq:          out << "SimplifyEq";          return out;
  case ReflexivityEq:       out << "ReflexivityEq";       return out;
  case UgtToUlt:            out << "UgtToUlt";            return out;
  case SgtToSlt:            out << "SgtToSlt";            return out;
  case UgeToUle:            out << "UgeToUle";            return out;
  case SgeToSle:            out << "SgeToSle";            return out;
  case RepeatEliminate:     out << "RepeatEliminate";     return out;
  case RotateLeftEliminate: out << "RotateLeftEliminate"; return out;
  case RotateRightEliminate:out << "RotateRightEliminate";return out;
  case NandEliminate:       out << "NandEliminate";       return out;
  case NorEliminate :       out << "NorEliminate";        return out;
  case SdivEliminate :      out << "SdivEliminate";       return out;
  case SremEliminate :      out << "SremEliminate";       return out;
  case SmodEliminate :      out << "SmodEliminate";       return out;
  case ZeroExtendEliminate :out << "ZeroExtendEliminate";       return out;
  case DivZeroGuard :       out << "DivZeroGuard";        return out;
  default:
    Unreachable();
  }
};

template <RewriteRuleId rule>
class RewriteRule {

  class RuleStatistics {

    /** The name of the rule prefixed with the prefix */
    static std::string getStatName(const char* prefix) {
      std::stringstream statName;
      statName << prefix << rule;
      return statName.str();
    }

  public:

    /** Number of applications of this rule */
    IntStat d_ruleApplications;

    /** Constructor */
    RuleStatistics()
    : d_ruleApplications(getStatName("theory::bv::RewriteRules::count"), 0) {
      StatisticsRegistry::registerStat(&d_ruleApplications);
    }

    /** Destructor */
    ~RuleStatistics() {
      StatisticsRegistry::unregisterStat(&d_ruleApplications);
    }
  };

  /* Statistics about the rule */
  // NOTE: Cannot have static fields like this, or else you can't have
  // two SmtEngines in the process (the second-to-be-destroyed will
  // have a dangling pointer and segfault).  If this statistic is needed,
  // fix the rewriter by making it an instance per-SmtEngine (instead of
  // static).
  //static RuleStatistics* s_statistics;

  /** Actually apply the rewrite rule */
  static inline Node apply(Node node) {
    Unreachable();
  }

public:

  RewriteRule() {
    /*
    if (s_statistics == NULL) {
      s_statistics = new RuleStatistics();
    }
    */
  }

  ~RewriteRule() {
    /*
    delete s_statistics;
    s_statistics = NULL;
    */
  }

  static inline bool applies(Node node) {
    Unreachable();
  }

  template<bool checkApplies>
  static inline Node run(Node node) {
    if (!checkApplies || applies(node)) {
      BVDebug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ")" << std::endl;
      Assert(checkApplies || applies(node));
      //++ s_statistics->d_ruleApplications;
      Node result = apply(node);
      BVDebug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ") => " << result << std::endl;
      return result;
    } else {
      return node;
    }
  }
};

/*
template<RewriteRuleId rule>
typename RewriteRule<rule>::RuleStatistics* RewriteRule<rule>::s_statistics = NULL;
*/

/** Have to list all the rewrite rules to get the statistics out */
struct AllRewriteRules {
  
  RewriteRule<EmptyRule>            rule00;
  RewriteRule<ConcatFlatten>        rule01;
  RewriteRule<ConcatExtractMerge>   rule02;
  RewriteRule<ConcatConstantMerge>  rule03;
  RewriteRule<ExtractExtract>       rule04;
  RewriteRule<ExtractWhole>         rule05;
  RewriteRule<ExtractConcat>        rule06;
  RewriteRule<ExtractConstant>      rule07;
  RewriteRule<FailEq>               rule08;
  RewriteRule<SimplifyEq>           rule09;
  RewriteRule<ReflexivityEq>        rule10;
  RewriteRule<UgtToUlt>             rule11;
  RewriteRule<SgtToSlt>             rule12;
  RewriteRule<UgeToUle>             rule13;
  RewriteRule<SgeToSle>             rule14;
  RewriteRule<RepeatEliminate>      rule17;
  RewriteRule<RotateLeftEliminate>  rule18;
  RewriteRule<RotateRightEliminate> rule19;
  RewriteRule<NandEliminate>        rule20;
  RewriteRule<NorEliminate>         rule21;
  RewriteRule<SdivEliminate>        rule22;
  RewriteRule<SremEliminate>        rule23;
  RewriteRule<SmodEliminate>        rule24;
  RewriteRule<DivZeroGuard>         rule25;

};

template<>
bool RewriteRule<EmptyRule>::applies(Node node) {
  return false;
}

template<>
Node RewriteRule<EmptyRule>::apply(Node node) {
  Unreachable();
  return node;
}

template<Kind kind, RewriteRuleId rule>
struct ApplyRuleToChildren {

  static Node apply(Node node) {
    if (node.getKind() != kind) {
      return RewriteRule<rule>::template run<true>(node);
    }
    NodeBuilder<> result(kind);
    for (unsigned i = 0, end = node.getNumChildren(); i < end; ++ i) {
      result << RewriteRule<rule>::template run<true>(node[i]);
    }
    return result;
  }

  static bool applies(Node node) {
    if (node.getKind() == kind) return true;
    return RewriteRule<rule>::applies(node);
  }

  template <bool checkApplies>
  static Node run(Node node) {
    if (!checkApplies || applies(node)) {
      return apply(node);
    } else {
      return node;
    }
  }
};

template <
  typename R1,
  typename R2 = RewriteRule<EmptyRule>,
  typename R3 = RewriteRule<EmptyRule>,
  typename R4 = RewriteRule<EmptyRule>,
  typename R5 = RewriteRule<EmptyRule>,
  typename R6 = RewriteRule<EmptyRule>,
  typename R7 = RewriteRule<EmptyRule>,
  typename R8 = RewriteRule<EmptyRule>
  >
struct LinearRewriteStrategy {
  static Node apply(Node node) {
    Node current = node;
    if (R1::applies(current)) current = R1::template run<false>(current);
    if (R2::applies(current)) current = R2::template run<false>(current);
    if (R3::applies(current)) current = R3::template run<false>(current);
    if (R4::applies(current)) current = R4::template run<false>(current);
    if (R5::applies(current)) current = R5::template run<false>(current);
    if (R6::applies(current)) current = R6::template run<false>(current);
    if (R7::applies(current)) current = R7::template run<false>(current);
    if (R8::applies(current)) current = R8::template run<false>(current);
    return current;
  }
};

} // End namespace bv
} // End namespace theory
} // End namespace CVC4