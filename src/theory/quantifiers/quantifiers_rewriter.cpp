/*********************                                                        */
/*! \file theory_quantifiers_rewriter.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of QuantifiersRewriter class
 **/

#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//#define QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS

bool QuantifiersRewriter::isClause( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isCube( n[0] );
  }else if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isClause( n[i] ) ){
        return false;
      }
    }
    return true;
  }else if( n.getKind()==IMPLIES ){
    return isCube( n[0] ) && isClause( n[1] );
  }else{
    return false;
  }
}

bool QuantifiersRewriter::isLiteral( Node n ){
  switch( n.getKind() ){
  case NOT:
    return isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
  case IFF:
    return false;
    break;
  case EQUAL:
    return n[0].getType()!=NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}

bool QuantifiersRewriter::isCube( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isClause( n[0] );
  }else if( n.getKind()==AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isCube( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void QuantifiersRewriter::computeArgs( std::map< Node, bool >& active, Node n ){
  if( active.find( n )!=active.end() ){
    active[n] = true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgs( active, n[i] );
    }
  }
}

void QuantifiersRewriter::computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ){
  std::map< Node, bool > active;
  for( int i=0; i<(int)args.size(); i++ ){
    active[ args[i] ] = false;
  }
  computeArgs( active, n );
  activeArgs.clear();
  for( std::map< Node, bool >::iterator it = active.begin(); it != active.end(); ++it ){
    if( it->second ){ //only add bound variables that occur in body
      activeArgs.push_back( it->first );
    }
  }
}

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& exArgs, bool pol ){
  if( body.getKind()==FORALL ){
    //must rename each variable that already exists
    std::vector< Node > old_vars;
    std::vector< Node > vars;
    bool varChanged = false;
    for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
      if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ||
          std::find( exArgs.begin(), exArgs.end(), body[0][i] )!=exArgs.end() ){
        vars.push_back( NodeManager::currentNM()->mkVar( body[0][i].getType() ) );
        varChanged = true;
      }else{
        vars.push_back( body[0][i] );
      }
      old_vars.push_back( body[0][i] );
    }
    Node newBody = body[1];
    if( varChanged ){
      newBody = newBody.substitute( old_vars.begin(), old_vars.end(), vars.begin(), vars.end() );
    }
    if( pol ){
      args.insert( args.end(), vars.begin(), vars.end() );
    }else{
      exArgs.insert( exArgs.end(), vars.begin(), vars.end() );
    }
    return newBody;
  }else if( body.getKind()==ITE || body.getKind()==XOR || body.getKind()==IFF ){
    return Node::null();
  }else{
    Assert( body.getKind()!=EXISTS );
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      bool newPol = ( body.getKind()==NOT || ( body.getKind()==IMPLIES && i==0 ) ) ? !pol : pol;
      Node n = computePrenex( body[i], args, exArgs, newPol );
      if( n.isNull() ){
        return Node::null();
      }else{
        newChildren.push_back( n );
        if( n!=body[i] ){
          childrenChanged = true;
        }
      }
    }
    if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
    }else{
      return body;
    }
  }
}

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args ){
  std::vector< Node > exArgs;
  Node newBody = computePrenex( body, args, exArgs, true );
  if( !newBody.isNull() ){
    if( !exArgs.empty() ){
      std::vector< Node > args;
      args.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, exArgs ) );
      args.push_back( newBody.getKind()==NOT ? newBody[0] : newBody.notNode() );
      newBody = NodeManager::currentNM()->mkNode(kind::FORALL, args );
      newBody = newBody.notNode();
    }
    return newBody;
  }else{
    return body;
  }
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node body, Node ipl ){
  if( doPrenex() ){
    //compute the new body
    body = computePrenex( body, args );
  }
  std::vector< Node > children;
  computeArgs( args, children, body );
  if( children.empty() ){
    return body;
  }else{
    std::vector< Node > args;
    args.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, children ) );
    args.push_back( body );
    if( !ipl.isNull() ){ 
      args.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode(kind::FORALL, args );
  }
}

bool QuantifiersRewriter::hasArg( std::vector< Node >& args, Node n ){
  if( std::find( args.begin(), args.end(), n )!=args.end() ){
    return true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( hasArg( args, n[i] ) ){
        return true;
      }
    }
    return false;
  }
}

void QuantifiersRewriter::setNestedQuantifiers( Node n, Node q ){
  if( n.getKind()==FORALL || n.getKind()==EXISTS ){
    NestedQuantAttribute nqai;
    n.setAttribute(nqai,q);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setNestedQuantifiers( n[i], q );
  }
}

Node QuantifiersRewriter::rewriteQuant( std::vector< Node >& args, Node body, NodeBuilder<>& defs, Node ipl, 
                                        bool isNested, bool isExists ){
  //std::cout << "rewrite quant " << body << std::endl;
  if( isExists ){
    Node retVal = rewriteQuant( args, body.notNode(), defs, ipl, isNested );
    return retVal.notNode();
  }else{
    if( body.getKind()==FORALL ){
      //combine arguments
      std::vector< Node > newArgs;
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        newArgs.push_back( body[0][i] );
      }
      newArgs.insert( newArgs.end(), args.begin(), args.end() );
      return mkForAll( newArgs, body[ 1 ], ipl );   //Note that we may lose instantiation patterns on nested quantifiers FIXME?
    }else if( !isNested && !isClause( body ) ){
      NodeBuilder<> body_split(kind::OR);
      Node newBody = body;
      if( body.getKind()==NOT ){
        //push not downwards
        if( body[0].getKind()==NOT ){
          return rewriteQuant( args, body[0][0], defs, ipl );
        }else if( body[0].getKind()==AND ){
          if( doMiniscopingNoFreeVar() ){
            NodeBuilder<> t(kind::OR);
            for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
              t <<  body[0][i].notNode();
            }
            Node quant = t;
            return rewriteQuant( args, quant, defs, ipl );
          }
        }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
          if( doMiniscopingAnd() ){
            NodeBuilder<> t(kind::AND);
            for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
              Node trm = ( body[0].getKind()==IMPLIES && i==0 ) ? body[0][i] : body[0][i].notNode();
              t << rewriteQuant( args, trm, defs, ipl );
            }
            Node retVal = t;
            return retVal;
          }
        }else{
          if( doMiniscopingAndExt() ){
            if( body[0].getKind()==IFF || body[0].getKind()==EQUAL ){
              Assert( body[0][0].getType()==NodeManager::currentNM()->booleanType() );
              return rewriteQuant( args, 
                NodeManager::currentNM()->mkNode( body[0].getKind(), body[0][0], body[0][1].notNode() ), defs, ipl );
            }else if( body[0].getKind()==XOR ){
              return rewriteQuant( args, 
                NodeManager::currentNM()->mkNode( XOR, body[0][0], body[0][1].notNode() ), defs, ipl );
            }else if( body[0].getKind()==ITE ){
              return rewriteQuant( args, 
                NodeManager::currentNM()->mkNode( ITE, body[0][0], body[0][1].notNode(), body[0][2].notNode() ), defs, ipl );
            }
          }
        }
      }else if( body.getKind()==AND ){
        if( !isNested && doMiniscopingAnd() ){
          //break apart
          NodeBuilder<> t(kind::AND);
          for( int i=0; i<(int)body.getNumChildren(); i++ ){
            t << rewriteQuant( args, body[i], defs, ipl );
          }
          Node retVal = t;
          return retVal;
        }
      }else if( body.getKind()==OR || body.getKind()==IMPLIES ){
        if( !isNested && doMiniscopingNoFreeVar() ){
          NodeBuilder<> tb(kind::OR);
          for( int i=0; i<(int)body.getNumChildren(); i++ ){
            Node trm = ( body.getKind()==IMPLIES && i==0 ) ? body[i].notNode() : body[i];
            if( hasArg( args, body[i] ) ){
              tb << trm;
            }else{
              body_split << trm;
            }
          }
          newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
        }
      }else{
        if( !isNested && doMiniscopingAndExt() ){
          if( body.getKind()==IFF ){
            Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( IMPLIES, body[0], body[1] ), defs, ipl );
            Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( IMPLIES, body[1], body[0] ), defs, ipl );
            return NodeManager::currentNM()->mkNode( AND, n1, n2 );
          }else if( body.getKind()==XOR ){
            Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0], body[1] ), defs, ipl, isNested );
            Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0].notNode(), body[1].notNode() ), defs, ipl );
            return NodeManager::currentNM()->mkNode( AND, n1, n2 );
          }else if( body.getKind()==ITE ){
            Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0], body[1] ), defs, ipl, isNested );
            Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0].notNode(), body[2] ), defs, ipl );
            return NodeManager::currentNM()->mkNode( AND, n1, n2 );
          }
        }
      }
      body_split << mkForAll( args, newBody, ipl );
      Node retVal = body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
      return retVal;
    }
    return mkForAll( args, body, ipl );
  }
}

bool QuantifiersRewriter::doMiniscopingNoFreeVar(){
  return Options::current()->miniscopeQuantFreeVar;
}

bool QuantifiersRewriter::doMiniscopingAnd(){
  if( Options::current()->miniscopeQuant ){
    return true;
  }else{
    if( Options::current()->cbqi ){
      return true;  
    }else{
      return false;
    }
  }
}

bool QuantifiersRewriter::doMiniscopingAndExt(){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
  return true;
#else
  return false;
#endif
}

bool QuantifiersRewriter::doPrenex(){
  return Options::current()->prenexQuant;
}