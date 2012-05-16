/*********************                                                        */
/*! \file relevancy.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. See
 ** [insert reference] for more details. This code is, or not, based
 ** on the CVC3 implementation of the same heuristic -- note below.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/
/*****************************************************************************/

#include "relevancy.h"

#include "expr/node_manager.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "util/ite_removal.h"

// Relevancy stuff

void Relevancy::setJustified(TNode n)
{
  d_justified.insert(n);
}

bool Relevancy::checkJustified(TNode n)
{
  return d_justified.find(n) != d_justified.end();
}

SatValue Relevancy::tryGetSatValue(Node n)
{
  Debug("decision") << "   "  << n << " has sat value " << " ";
  if(d_decisionEngine->hasSatLiteral(n) ) {
    Debug("decision") << d_decisionEngine->getSatValue(n) << std::endl;
    return d_decisionEngine->getSatValue(n);
  } else {
    Debug("decision") << "NO SAT LITERAL" << std::endl;
    return SAT_VALUE_UNKNOWN;
  }//end of else
}

void Relevancy::computeITEs(TNode n, IteList &l)
{
  Debug("jh-ite") << " computeITEs( " << n << ", &l)\n";
  for(unsigned i=0; i<n.getNumChildren(); ++i) {
    SkolemMap::iterator it2 = d_iteAssertions.find(n[i]);
    if(it2 != d_iteAssertions.end())
      l.push_back(it2->second);
    computeITEs(n[i], l);
  }
}

const IteList& Relevancy::getITEs(TNode n)
{
  IteCache::iterator it = d_iteCache.find(n);
  if(it != d_iteCache.end()) {
    return it->second;
  } else {
    // Compute the list of ITEs
    // TODO: optimize by avoiding multiple lookup for d_iteCache[n]
    d_iteCache[n] = vector<TNode>();
    computeITEs(n, d_iteCache[n]);
    return d_iteCache[n];
  }
}

bool Relevancy::findSplitterRec(TNode node, 
                                SatValue desiredVal)
{
  Trace("decision") 
    << "findSplitterRec(" << node << ", " 
    << desiredVal << ", .. )" << std::endl; 

  /* Handle NOT as a special case */
  while (node.getKind() == kind::NOT) {
    desiredVal = invertValue(desiredVal);
    node = node[0];
  }

  /* Base case */
  if (checkJustified(node) || d_visited.find(node) != d_visited.end())
    return false;

#if defined CVC4_ASSERTIONS || defined CVC4_TRACING
  // We don't always have a sat literal, so remember that. Will need
  // it for some assertions we make.
  bool litPresent = d_decisionEngine->hasSatLiteral(node);
  if(Trace.isOn("decision")) {
    if(!litPresent) {
      Trace("decision") << "no sat literal for this node" << std::endl;
    }
  }
  //Assert(litPresent); -- fails
#endif

  // Get value of sat literal for the node, if there is one
  SatValue litVal = tryGetSatValue(node);

  /* You'd better know what you want */
  Assert(desiredVal != SAT_VALUE_UNKNOWN, "expected known value");

  /* Good luck, hope you can get what you want */
  Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN, 
         "invariant voilated");

  /* What type of node is this */
  Kind k = node.getKind();	
  theory::TheoryId tId = theory::kindToTheoryId(k);

  /* Some debugging stuff */
  Trace("jh-findSplitterRec") << "kind = " << k << std::endl;
  Trace("jh-findSplitterRec") << "theoryId = " << tId << std::endl;
  Trace("jh-findSplitterRec") << "node = " << node << std::endl;
  Trace("jh-findSplitterRec") << "litVal = " << litVal << std::endl;

  /**
   * If not in theory of booleans, and not a "boolean" EQUAL (IFF),
   * then check if this is something to split-on.
   */
  if(tId != theory::THEORY_BOOL
     //      && !(k == kind::EQUAL && node[0].getType().isBoolean()) 
     ) {

    // if node has embedded ites -- which currently happens iff it got
    // replaced during ite removal -- then try to resolve that first
    const IteList& l = getITEs(node);
    Debug("jh-ite") << " ite size = " << l.size() << std::endl;
    d_visited.insert(node);
    for(unsigned i = 0; i < l.size(); ++i) {
      Assert(l[i].getKind() == kind::ITE, "Expected ITE");
      Debug("jh-ite") << " i = " << i 
                      << " l[i] = " << l[i] << std::endl;
      if (checkJustified(l[i])) continue;

      SatValue desiredVal = SAT_VALUE_TRUE; //NOTE: Reusing variable
#ifdef CVC4_ASSERTIONS
      bool litPresent = d_decisionEngine->hasSatLiteral(l[i]);
#endif

      // Handle the ITE to catch the case when a variable is its own
      // fanin
      SatValue ifVal = tryGetSatValue(l[i][0]);
      if (ifVal == SAT_VALUE_UNKNOWN) {
        // are we better off trying false? if not, try true
        SatValue ifDesiredVal = 
          (tryGetSatValue(l[i][2]) == desiredVal ||
           tryGetSatValue(l[i][1]) == invertValue(desiredVal))
          ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;

        if(findSplitterRec(l[i][0], ifDesiredVal)) {
          return true;
        }
        Assert(false, "No controlling input found (1)");
      } else {

        // Try to justify 'if'
        if (findSplitterRec(l[i][0], ifVal)) {
          return true;
        }

        // If that was successful, we need to go into only one of 'then'
        // or 'else'
        int ch = (ifVal == SAT_VALUE_TRUE) ? 1 : 2;
        int chVal = tryGetSatValue(l[i][ch]);
        if( d_visited.find(l[i]) == d_visited.end()
            && (chVal == SAT_VALUE_UNKNOWN || chVal == desiredVal)
            && findSplitterRec(l[i][ch], desiredVal) ) {
          return true;
        }
      }
      Assert(litPresent == false || litVal == desiredVal,
             "Output should be justified");
      setJustified(l[i]);
    }
    d_visited.erase(node);

    if(litVal != SAT_VALUE_UNKNOWN) {
      setJustified(node);
      return false;
    } else {
      /* if(not d_decisionEngine->hasSatLiteral(node))
         throw GiveUpException(); */
      Assert(d_decisionEngine->hasSatLiteral(node));
      SatVariable v = d_decisionEngine->getSatLiteral(node).getSatVariable();
      *d_curDecision = SatLiteral(v, desiredVal != SAT_VALUE_TRUE );
      Trace("decision") << "decision " << *d_curDecision << std::endl;
      Trace("decision") << "Found something to split. Glad to be able to serve you." << std::endl;
      return true;
    }
  }

  bool ret = false;
  SatValue flipCaseVal = SAT_VALUE_FALSE;
  switch (k) {

  case kind::CONST_BOOLEAN:
    Assert(node.getConst<bool>() == false || desiredVal == SAT_VALUE_TRUE);
    Assert(node.getConst<bool>() == true  || desiredVal == SAT_VALUE_FALSE);
    break;

  case kind::AND:
    if (desiredVal == SAT_VALUE_FALSE) ret = handleOrTrue(node, SAT_VALUE_FALSE);
    else                               ret = handleOrFalse(node, SAT_VALUE_TRUE);
    break;

  case kind::OR:
    if (desiredVal == SAT_VALUE_FALSE) ret = handleOrFalse(node, SAT_VALUE_FALSE);
    else                               ret = handleOrTrue(node, SAT_VALUE_TRUE);
    break;

  case kind::IMPLIES:
    Assert(node.getNumChildren() == 2, "Expected 2 fanins");
    if (desiredVal == SAT_VALUE_FALSE) {
      ret = findSplitterRec(node[0], SAT_VALUE_TRUE);
      if(ret) break;
      ret = findSplitterRec(node[1], SAT_VALUE_FALSE);
      break;
    }
    else {
      if (tryGetSatValue(node[0]) != SAT_VALUE_TRUE) {
        ret = findSplitterRec(node[0], SAT_VALUE_FALSE);
        break;
      }
      if (tryGetSatValue(node[1]) != SAT_VALUE_FALSE) {
        ret = findSplitterRec(node[1], SAT_VALUE_TRUE);
        break;
      }
      Assert(false, "No controlling input found (3)");
    }
    break;

  case kind::XOR:
    flipCaseVal = SAT_VALUE_TRUE;
  case kind::IFF:
    //throw GiveUpException();
    {
      // flipCaseVal = SAT_VALUE_FALSE  --- done at initialization
    SatValue val = tryGetSatValue(node[0]);
    if (val != SAT_VALUE_UNKNOWN) {
      ret = findSplitterRec(node[0], val);
      if (ret) break;
      if (desiredVal == flipCaseVal) val = invertValue(val);
      ret = findSplitterRec(node[1], val);
    }
    else {
      val = tryGetSatValue(node[1]);
      if (val == SAT_VALUE_UNKNOWN) val = SAT_VALUE_FALSE;
      if (desiredVal == flipCaseVal) val = invertValue(val);
      ret = findSplitterRec(node[0], val);
      if(ret) break;
      Assert(false, "Unable to find controlling input (4)");
    }
    break;
  }

  case kind::ITE: {
    //[0]: if, [1]: then, [2]: else
    SatValue ifVal = tryGetSatValue(node[0]);
    if (ifVal == SAT_VALUE_UNKNOWN) {
      
      // are we better off trying false? if not, try true
      SatValue ifDesiredVal = 
        (tryGetSatValue(node[2]) == desiredVal ||
	 tryGetSatValue(node[1]) == invertValue(desiredVal))
	? SAT_VALUE_FALSE : SAT_VALUE_TRUE;

      if(findSplitterRec(node[0], ifDesiredVal)) {
	return true;
      }
      Assert(false, "No controlling input found (6)");
    } else {

      // Try to justify 'if'
      if (findSplitterRec(node[0], ifVal)) {
	return true;
      }

      // If that was successful, we need to go into only one of 'then'
      // or 'else'
      int ch = (ifVal == SAT_VALUE_TRUE) ? 1 : 2;
      int chVal = tryGetSatValue(node[ch]);
      if( (chVal == SAT_VALUE_UNKNOWN || chVal == desiredVal)
	  && findSplitterRec(node[ch], desiredVal) ) {
	return true;
      }
    }
    Assert(litPresent == false || litVal == desiredVal,
	   "Output should be justified");
    setJustified(node);
    return false;
  }

  default:
    Assert(false, "Unexpected Boolean operator");
    break;
  }//end of switch(k)

  if(ret == false) {
    Assert(litPresent == false || litVal ==  desiredVal,
           "Output should be justified");
    setJustified(node);
  }
  return ret;

  Unreachable();
}/* findRecSplit method */

bool Relevancy::handleOrFalse(Node node, SatValue desiredVal) {
  Debug("jh-findSplitterRec") << " handleOrFalse (" << node << ", "
                              << desiredVal << std::endl;

  Assert( (node.getKind() == kind::AND and desiredVal == SAT_VALUE_TRUE) or 
          (node.getKind() == kind::OR  and desiredVal == SAT_VALUE_FALSE) );

  int n = node.getNumChildren();
  for(int i = 0; i < n; ++i) {
    if (findSplitterRec(node[i], desiredVal)) {
      return true;
    }
  }
  return false;      
}

bool Relevancy::handleOrTrue(Node node, SatValue desiredVal) {
  Debug("jh-findSplitterRec") << " handleOrTrue (" << node << ", "
                              << desiredVal << std::endl;

  Assert( (node.getKind() == kind::AND and desiredVal == SAT_VALUE_FALSE) or 
          (node.getKind() == kind::OR  and desiredVal == SAT_VALUE_TRUE) );

  int n = node.getNumChildren();
  SatValue desiredValInverted = invertValue(desiredVal);
  for(int i = 0; i < n; ++i) {
    if ( tryGetSatValue(node[i]) != desiredValInverted ) {
      return findSplitterRec(node[i], desiredVal);
    }
  }
  if(Debug.isOn("jh-findSplitterRec")) {
    Debug("jh-findSplitterRec") << " * ** " << std::endl;
    Debug("jh-findSplitterRec") << node.getKind() << " "
                                << node << std::endl;
    for(unsigned i = 0; i < node.getNumChildren(); ++i) 
      Debug("jh-findSplitterRec") << "child: " << tryGetSatValue(node[i]) 
                                  << std::endl;
    Debug("jh-findSplitterRec") << "node: " << tryGetSatValue(node)
                                << std::endl;
  }
  Assert(false, "No controlling input found");
  return false;
}
