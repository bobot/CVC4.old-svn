/*********************                                                        */
/*! \file theory_bv_rewrite_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: lianah
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

  /// core normalization rules
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
  UgtEliminate,
  UgeEliminate,
  SgeEliminate,
  SgtEliminate,
  SubEliminate,
  SltEliminate,
  SleEliminate,
  CompEliminate,
  RepeatEliminate,
  RotateLeftEliminate,
  RotateRightEliminate,
  NandEliminate,
  NorEliminate,
  XnorEliminate,
  SdivEliminate,
  UdivEliminate,
  SmodEliminate,
  SremEliminate,
  ZeroExtendEliminate,
  SignExtendEliminate,
  
  /// ground term evaluation
  EvalEquals,
  EvalConcat, // to remove
  EvalAnd,
  EvalOr,
  EvalXor,
  EvalNot,
  EvalMult,
  EvalPlus,
  EvalUdiv,
  EvalUrem,
  EvalShl,
  EvalLshr,
  EvalAshr,
  EvalUlt,
  EvalUle,
  EvalExtract, // to remove
  EvalSignExtend,
  EvalRotateLeft,
  EvalRotateRight,
  EvalNeg,
  
  /// simplification rules
  /// all of these rules decrease formula size
  ShlByConst,
  LshrByConst,
  AshrByConst,
  BitwiseIdemp,
  AndZero,
  AndOne,
  OrZero,
  OrOne,
  XorDuplicate,
  XorOne,
  XorZero,
  BitwiseNotAnd,
  BitwiseNotOr,
  XorNot,
  NotIdemp,
  LtSelf,
  LteSelf,
  UltZero,
  UltSelf,
  UleZero,
  UleSelf,
  ZeroUle,
  UleMax,
  NotUlt,
  NotUle,
  MultOne,
  MultZero,
  MultPow2,
  PlusZero,
  PlusSelf,
  PlusNegSelf,
  NegIdemp,
  UdivPow2,
  UdivOne,
  UdivSelf,
  UremPow2,
  UremOne,
  UremSelf,
  ShiftZero,
  
  /// normalization rules
  ExtractBitwise,
  ExtractNot,
  ExtractArith,
  ExtractArith2,
  DoubleNeg,
  NegConcat,
  NegAnd, // not sure why this would help (not done)
  NegOr,  // not sure why this would help (not done)
  NotXor // not sure why this would help (not done)
 };

// inline std::ostream& operator << (std::ostream& out, RewriteRuleId ruleId) {
//   switch (ruleId) {
//   case EmptyRule:           out << "EmptyRule";           return out;
//   case ConcatFlatten:       out << "ConcatFlatten";       return out;
//   case ConcatExtractMerge:  out << "ConcatExtractMerge";  return out;
//   case ConcatConstantMerge: out << "ConcatConstantMerge"; return out;
//   case ExtractExtract:      out << "ExtractExtract";      return out;
//   case ExtractWhole:        out << "ExtractWhole";        return out;
//   case ExtractConcat:       out << "ExtractConcat";       return out;
//   case ExtractConstant:     out << "ExtractConstant";     return out;
//   case FailEq:              out << "FailEq";              return out;
//   case SimplifyEq:          out << "SimplifyEq";          return out;
//   case ReflexivityEq:       out << "ReflexivityEq";       return out;
//   case UgtToUlt:            out << "UgtToUlt";            return out;
//   case SgtToSlt:            out << "SgtToSlt";            return out;
//   case UgeToUle:            out << "UgeToUle";            return out;
//   case SgeToSle:            out << "SgeToSle";            return out;
//   case RepeatEliminate:     out << "RepeatEliminate";     return out;
//   case RotateLeftEliminate: out << "RotateLeftEliminate"; return out;
//   case RotateRightEliminate:out << "RotateRightEliminate";return out;
//   case NandEliminate:       out << "NandEliminate";       return out;
//   case NorEliminate :       out << "NorEliminate";        return out;
//   case SdivEliminate :      out << "SdivEliminate";       return out;
//   case SremEliminate :      out << "SremEliminate";       return out;
//   case SmodEliminate :      out << "SmodEliminate";       return out;
//   case ZeroExtendEliminate :out << "ZeroExtendEliminate"; return out;
//   case EvalEquals :         out << "EvalEquals";          return out;
//   case EvalConcat :         out << "EvalConcat";          return out;
//   case EvalAnd :            out << "EvalAnd";             return out;
//   case EvalOr :             out << "EvalOr";              return out;
//   case EvalXor :            out << "EvalXor";             return out;
//   case EvalNot :            out << "EvalNot";             return out;
//   case EvalMult :           out << "EvalMult";            return out;
//   case EvalPlus :           out << "EvalPlus";            return out;
//   case EvalUdiv :           out << "EvalUdiv";            return out;
//   case EvalUrem :           out << "EvalUrem";            return out;
//   case EvalShl :            out << "EvalShl";             return out;
//   case EvalLshr :           out << "EvalLshr";            return out;
//   case EvalAshr :           out << "EvalAshr";            return out;
//   case EvalUlt :            out << "EvalUlt";             return out;
//   case EvalSlt :            out << "EvalSlt";             return out;
//   case EvalUle :            out << "EvalUle";             return out;
//   case EvalSle :            out << "EvalSle";             return out;
//   case EvalExtract :        out << "EvalExtract";         return out;
//   case EvalSignExtend :     out << "EvalSignExtend";      return out;
//   case EvalRotateLeft :     out << "EvalRotateLeft";      return out;
//   case EvalRotateRight :    out << "EvalRotateRight";     return out;
//   case EvalNeg :            out << "EvalNeg";             return out;
//   case ShlByConst :         out << "ShlByConst";          return out;
//   case LshrByConst :        out << "LshrByConst";         return out;
//   case AshrByConst :        out << "AshrByConst";         return out;
//   case ExtractBitwise :     out << "ExtractBitwise";      return out;
//   case ExtractNot :         out << "ExtractNot";          return out;
//   case ExtractArith :       out << "ExtractArith";        return out;
//   case DoubleNeg :          out << "DoubleNeg";           return out;
//   case NegConcat :          out << "NegConcat";           return out;
//   case NegAnd :             out << "NegAnd";              return out;
//   case NegOr :              out << "NegOr";               return out;
//   case NegXor :             out << "NegXor";              return out;
//   case BitwiseIdemp :       out << "BitwiseIdemp";        return out;
//   case XorDuplicate :       out << "XorDuplicate";        return out;
//   case BitwiseNegAnd :      out << "BitwiseNegAnd";       return out;
//   case BitwiseNegOr :       out << "BitwiseNegOr";        return out;
//   case XorNeg :             out << "XorNeg";              return out;
//   case LtSelf :             out << "LtSelf";              return out;
//   case LteSelf :            out << "LteSelf";              return out;
//   case UltZero :            out << "UltZero";             return out;
//   case UleZero :            out << "UleZero";             return out;
//   case ZeroUle :            out << "ZeroUle";             return out;
//   case NotUlt :             out << "NotUlt";              return out;
//   case NotUle :             out << "NotUle";              return out;
//   case UleMax :             out << "UleMax";              return out;
//   case SltEliminate :       out << "SltEliminate";        return out;
//   case SleEliminate :       out << "SleEliminate";        return out;
//   default:
//     Unreachable();
//   }
// };

template <RewriteRuleId rule>
class RewriteRule {

  // class RuleStatistics {

  //   /** The name of the rule prefixed with the prefix */
  //   static std::string getStatName(const char* prefix) {
  //     std::stringstream statName;
  //     statName << prefix << rule;
  //     return statName.str();
  //   }

  // public:

  //   /** Number of applications of this rule */
  //   IntStat d_ruleApplications;

  //   /** Constructor */
  //   RuleStatistics()
  //   : d_ruleApplications(getStatName("theory::bv::RewriteRules::count"), 0) {
  //     StatisticsRegistry::registerStat(&d_ruleApplications);
  //   }

  //   /** Destructor */
  //   ~RuleStatistics() {
  //     StatisticsRegistry::unregisterStat(&d_ruleApplications);
  //   }
  // };

  // /* Statistics about the rule */
  // // NOTE: Cannot have static fields like this, or else you can't have
  // // two SmtEngines in the process (the second-to-be-destroyed will
  // // have a dangling pointer and segfault).  If this statistic is needed,
  // // fix the rewriter by making it an instance per-SmtEngine (instead of
  // // static).
  // static RuleStatistics* s_statistics;

  /** Actually apply the rewrite rule */
  static inline Node apply(Node node) {
    Unreachable();
  }

public:

  RewriteRule() {
    
    // if (s_statistics == NULL) {
    //   s_statistics = new RuleStatistics();
    // }
    
  }

  ~RewriteRule() {
    
    // delete s_statistics;
    // s_statistics = NULL;
    
  }

  static inline bool applies(Node node) {
    Unreachable();
  }

  template<bool checkApplies>
  static inline Node run(Node node) {
    if (!checkApplies || applies(node)) {
      BVDebug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ")" << std::endl;
      Assert(checkApplies || applies(node));
      // ++ s_statistics->d_ruleApplications;
      Node result = apply(node);
      BVDebug("theory::bv::rewrite") << "RewriteRule<" << rule << ">(" << node << ") => " << result << std::endl;
      return result;
    } else {
      return node;
    }
  }
};


// template<RewriteRuleId rule>
// typename RewriteRule<rule>::RuleStatistics* RewriteRule<rule>::s_statistics = NULL;


/** Have to list all the rewrite rules to get the statistics out */
// struct AllRewriteRules {
//   RewriteRule<EmptyRule>            rule00;
//   RewriteRule<ConcatFlatten>        rule01;
//   RewriteRule<ConcatExtractMerge>   rule02;
//   RewriteRule<ConcatConstantMerge>  rule03;
//   RewriteRule<ExtractExtract>       rule04;
//   RewriteRule<ExtractWhole>         rule05;
//   RewriteRule<ExtractConcat>        rule06;
//   RewriteRule<ExtractConstant>      rule07;
//   RewriteRule<FailEq>               rule08;
//   RewriteRule<SimplifyEq>           rule09;
//   RewriteRule<ReflexivityEq>        rule10;
//   RewriteRule<UgtToUlt>             rule11;
//   RewriteRule<SgtToSlt>             rule12;
//   RewriteRule<UgeToUle>             rule13;
//   RewriteRule<SgeToSle>             rule14;
//   RewriteRule<RepeatEliminate>      rule17;
//   RewriteRule<RotateLeftEliminate>  rule18;
//   RewriteRule<RotateRightEliminate> rule19;
//   RewriteRule<NandEliminate>        rule20;
//   RewriteRule<NorEliminate>         rule21;
//   RewriteRule<SdivEliminate>        rule22;
//   RewriteRule<SremEliminate>        rule23;
//   RewriteRule<SmodEliminate>        rule24;
//   RewriteRule<EvalConcat>           rule25;
//   RewriteRule<EvalAnd>              rule26;
//   RewriteRule<EvalOr>               rule27;
//   RewriteRule<EvalXor>              rule28;
//   RewriteRule<EvalNot>              rule29;
//   RewriteRule<EvalComp>             rule30;
//   RewriteRule<EvalMult>             rule31;
//   RewriteRule<EvalPlus>             rule32;
//   RewriteRule<EvalSub>              rule33;
//   RewriteRule<EvalUdiv>             rule34;
//   RewriteRule<EvalUrem>             rule35;
//   RewriteRule<EvalShl>              rule36;
//   RewriteRule<EvalLshr>             rule37;
//   RewriteRule<EvalAshr>             rule38;
//   RewriteRule<EvalUlt>              rule39;
//   RewriteRule<EvalUle>              rule40;
//   RewriteRule<EvalSlt>              rule41;
//   RewriteRule<EvalSle>              rule42;
//   RewriteRule<EvalExtract>          rule43;
//   RewriteRule<EvalSignExtend>       rule44;
//   RewriteRule<EvalRotateLeft>       rule45;
//   RewriteRule<EvalRotateRight>      rule46;
//   RewriteRule<EvalEquals>           rule47;
//   RewriteRule<EvalNeg>              rule48;
//   RewriteRule<EvalXnor>             rule49;
//   RewriteRule<ShlByConst>             rule50;
//   RewriteRule<LshrByConst>             rule51;
//   RewriteRule<AshrByConst>             rule52;
//   RewriteRule<ExtractBitwise>             rule53;
//   RewriteRule<ExtractNot>             rule54;
//   RewriteRule<ExtractArith>             rule55;
//   RewriteRule<DoubleNeg>             rule56;
//   RewriteRule<NegConcat>             rule57;
//   RewriteRule<NegAnd>             rule58;
//   RewriteRule<NegOr>             rule59;
//   RewriteRule<NegXor>             rule60;
//   RewriteRule<BitwiseIdemp>             rule61;
//   RewriteRule<XorDuplicate>             rule62;
//   RewriteRule<BitwiseNegAnd>             rule63;
//   RewriteRule<BitwiseNegOr>             rule64;
//   RewriteRule<XorNeg>             rule65;
//   RewriteRule<LtSelf>             rule66;
//   RewriteRule<LtSelf>             rule67;
//   RewriteRule<UltZero>             rule68;
//   RewriteRule<UleZero>             rule69;
//   RewriteRule<ZeroUle>             rule70;
//   RewriteRule<NotUlt>             rule71;
//   RewriteRule<NotUle>             rule72;
//   RewriteRule<ZeroExtendEliminate> rule73;
//   RewriteRule<UleMax> rule74;
//   RewriteRule<LteSelf> rule75;
//   RewriteRule<SltEliminate> rule76;
//   RewriteRule<SleEliminate> rule77; 
// };

template<>
bool RewriteRule<EmptyRule>::applies(Node node) {
  return false;
}

template<>
Node RewriteRule<EmptyRule>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EmptyRule> for " << node.getKind() <<"\n"; 
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
  typename R2  = RewriteRule<EmptyRule>,
  typename R3  = RewriteRule<EmptyRule>,
  typename R4  = RewriteRule<EmptyRule>,
  typename R5  = RewriteRule<EmptyRule>,
  typename R6  = RewriteRule<EmptyRule>,
  typename R7  = RewriteRule<EmptyRule>,
  typename R8  = RewriteRule<EmptyRule>,
  typename R9  = RewriteRule<EmptyRule>,
  typename R10 = RewriteRule<EmptyRule>,
  typename R11 = RewriteRule<EmptyRule>,
  typename R12 = RewriteRule<EmptyRule>,
  typename R13 = RewriteRule<EmptyRule>,
  typename R14 = RewriteRule<EmptyRule>,
  typename R15 = RewriteRule<EmptyRule>,
  typename R16 = RewriteRule<EmptyRule>,
  typename R17 = RewriteRule<EmptyRule>,
  typename R18 = RewriteRule<EmptyRule>,
  typename R19 = RewriteRule<EmptyRule>,
  typename R20 = RewriteRule<EmptyRule>
  >
struct LinearRewriteStrategy {
  static Node apply(Node node) {
    Node current = node;
    if (R1::applies(current)) current  = R1::template run<false>(current);
    if (R2::applies(current)) current  = R2::template run<false>(current);
    if (R3::applies(current)) current  = R3::template run<false>(current);
    if (R4::applies(current)) current  = R4::template run<false>(current);
    if (R5::applies(current)) current  = R5::template run<false>(current);
    if (R6::applies(current)) current  = R6::template run<false>(current);
    if (R7::applies(current)) current  = R7::template run<false>(current);
    if (R8::applies(current)) current  = R8::template run<false>(current);
    if (R9::applies(current)) current  = R9::template run<false>(current);
    if (R10::applies(current)) current = R10::template run<false>(current);
    if (R11::applies(current)) current = R11::template run<false>(current);
    if (R12::applies(current)) current = R12::template run<false>(current);
    if (R13::applies(current)) current = R13::template run<false>(current);
    if (R14::applies(current)) current = R14::template run<false>(current);
    if (R15::applies(current)) current = R15::template run<false>(current);
    if (R16::applies(current)) current = R16::template run<false>(current);
    if (R17::applies(current)) current = R17::template run<false>(current);
    if (R18::applies(current)) current = R18::template run<false>(current);
    if (R19::applies(current)) current = R19::template run<false>(current);
    if (R20::applies(current)) current = R20::template run<false>(current);
    return current;
  }
};

template <
  typename R1,
  typename R2  = RewriteRule<EmptyRule>,
  typename R3  = RewriteRule<EmptyRule>,
  typename R4  = RewriteRule<EmptyRule>,
  typename R5  = RewriteRule<EmptyRule>,
  typename R6  = RewriteRule<EmptyRule>,
  typename R7  = RewriteRule<EmptyRule>,
  typename R8  = RewriteRule<EmptyRule>,
  typename R9  = RewriteRule<EmptyRule>,
  typename R10 = RewriteRule<EmptyRule>,
  typename R11 = RewriteRule<EmptyRule>,
  typename R12 = RewriteRule<EmptyRule>,
  typename R13 = RewriteRule<EmptyRule>,
  typename R14 = RewriteRule<EmptyRule>,
  typename R15 = RewriteRule<EmptyRule>,
  typename R16 = RewriteRule<EmptyRule>,
  typename R17 = RewriteRule<EmptyRule>,
  typename R18 = RewriteRule<EmptyRule>,
  typename R19 = RewriteRule<EmptyRule>,
  typename R20 = RewriteRule<EmptyRule>
  >
struct FixpointRewriteStrategy {
  static Node apply(Node node) {
    Node previous = node; 
    Node current = node;
    do {
      previous = current;
      if (R1::applies(current)) current  = R1::template run<false>(current);
      if (R2::applies(current)) current  = R2::template run<false>(current);
      if (R3::applies(current)) current  = R3::template run<false>(current);
      if (R4::applies(current)) current  = R4::template run<false>(current);
      if (R5::applies(current)) current  = R5::template run<false>(current);
      if (R6::applies(current)) current  = R6::template run<false>(current);
      if (R7::applies(current)) current  = R7::template run<false>(current);
      if (R8::applies(current)) current  = R8::template run<false>(current);
      if (R9::applies(current)) current  = R9::template run<false>(current);
      if (R10::applies(current)) current = R10::template run<false>(current);
      if (R11::applies(current)) current = R11::template run<false>(current);
      if (R12::applies(current)) current = R12::template run<false>(current);
      if (R13::applies(current)) current = R13::template run<false>(current);
      if (R14::applies(current)) current = R14::template run<false>(current);
      if (R15::applies(current)) current = R15::template run<false>(current);
      if (R16::applies(current)) current = R16::template run<false>(current);
      if (R17::applies(current)) current = R17::template run<false>(current);
      if (R18::applies(current)) current = R18::template run<false>(current);
      if (R19::applies(current)) current = R19::template run<false>(current);
      if (R20::applies(current)) current = R20::template run<false>(current);
    } while (previous != current);
    
    return current;
  }
};


} // End namespace bv
} // End namespace theory
} // End namespace CVC4
