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

void QuantifiersRewriter::addNodeToOrBuilder( Node n, NodeBuilder<>& t ){
  if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
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
  //std::cout << "For " << n << " : " << std::endl;
  computeArgs( active, n );
  activeArgs.clear();
  for( std::map< Node, bool >::iterator it = active.begin(); it != active.end(); ++it ){
    Node n = it->first;
    //std::cout << "   " << it->first << " is " << it->second << std::endl;
    if( it->second ){ //only add bound variables that occur in body
      activeArgs.push_back( it->first );
    }
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
    Debug("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
    NestedQuantAttribute nqai;
    n.setAttribute(nqai,q);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setNestedQuantifiers( n[i], q );
  }
}

RewriteResponse QuantifiersRewriter::preRewrite(TNode in) {
  Debug("quantifiers-rewrite-debug") << "pre-rewriting " << in << " " << in.hasAttribute(NestedQuantAttribute()) << std::endl;
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    if( !in.hasAttribute(NestedQuantAttribute()) ){
      setNestedQuantifiers( in[ 1 ], in );
    }
    std::vector< Node > args;
    for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
      args.push_back( in[0][i] );
    }
    Node body = in[1];
    bool doRewrite = false;
    while( body.getNumChildren()>=2 && body.getKind()==in.getKind() ){
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
      body = body[1];
      doRewrite = true;
    }
    if( doRewrite ){
      std::vector< Node > children;
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,args) );
      children.push_back( body );
      if( in.getNumChildren()==3 ){
        children.push_back( in[2] );
      }
      Node n = NodeManager::currentNM()->mkNode( in.getKind(), children );
      if( in!=n ){
        Debug("quantifiers-pre-rewrite") << "*** pre-rewrite " << in << std::endl;
        Debug("quantifiers-pre-rewrite") << " to " << std::endl;
        Debug("quantifiers-pre-rewrite") << n << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, n);
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse QuantifiersRewriter::postRewrite(TNode in) {
  Debug("quantifiers-rewrite-debug") << "post-rewriting " << in << " " << in.hasAttribute(NestedQuantAttribute()) << std::endl;
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    //get the arguments
    std::vector< Node > args;
    for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
      args.push_back( in[0][i] );
    }
    //get the body
    Node body = in[1];
    if( in.getKind()==EXISTS ){
      body = body.getKind()==NOT ? body[0] : body.notNode();
    }
    //get the instantiation pattern list
    Node ipl;
    if( in.getNumChildren()==3 ){
      ipl = in[2];
    }
    bool isNested = in.hasAttribute(NestedQuantAttribute());
    //compute miniscoping first
    Node n = computeMiniscoping( args, body, ipl, isNested );
    if( in.getKind()==kind::EXISTS ){
      n = n.getKind()==NOT ? n[0] : n.notNode();
    }
    //compute other rewrite options for each produced quantifier
    n = rewriteQuants( n, isNested );
    //print if changed
    if( in!=n ){
      Debug("quantifiers-rewrite") << "*** rewrite " << in << std::endl;
      Debug("quantifiers-rewrite") << " to " << std::endl;
      Debug("quantifiers-rewrite") << n << std::endl;
      if( in.hasAttribute(InstConstantAttribute()) ){
        InstConstantAttribute ica;
        n.setAttribute(ica,in.getAttribute(InstConstantAttribute()) );
      }
    }
    return RewriteResponse(REWRITE_DONE, n );
  }
  return RewriteResponse(REWRITE_DONE, in);
}

Node QuantifiersRewriter::computeVarElimination( Node f ){
  //std::cout << "Compute var elimination for " << f << std::endl;
  std::map< Node, bool > args;
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    args[ f[0][i] ] = true;
  }
  Node body = f[1];
  std::map< Node, bool > litPhaseReq;
  QuantifiersEngine::computePhaseReqs( body, false, litPhaseReq );
  std::vector< Node > vars;
  std::vector< Node > subs;
  for( std::map< Node, bool >::iterator it = litPhaseReq.begin(); it != litPhaseReq.end(); ++it ){
    //std::cout << "   " << it->first << " -> " << ( it->second ? "true" : "false" ) << std::endl;
    if( it->first.getKind()==EQUAL ){
      if( it->second ){
        if( args.find( it->first[0] )!=args.end() && args[ it->first[0] ] ){
          std::vector< Node > temp;
          temp.push_back( it->first[0] );
          if( !hasArg( temp, it->first[1] ) ){
            args[ it->first[0] ] = false;
            vars.push_back( it->first[0] );
            subs.push_back( it->first[1] );
            break;
          }
        }else if( args.find( it->first[1] )!=args.end() && args[ it->first[1] ] ){
          std::vector< Node > temp;
          temp.push_back( it->first[1] );
          if( !hasArg( temp, it->first[0] ) ){
            args[ it->first[1] ] = false;
            vars.push_back( it->first[1] );
            subs.push_back( it->first[0] );
            break;
          }
        }
      }
    }
  }
  if( !vars.empty() ){
    //std::cout << "VE " << vars.size() << "/" << n[0].getNumChildren() << std::endl;
    //remake with eliminated nodes
    std::vector< Node > argsVec;
    for( std::map< Node, bool >::iterator it = args.begin(); it != args.end(); ++it ){
      if( it->second ){
        argsVec.push_back( it->first );
      }
    }
    body = body.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    //std::cout << "substitute body = " << body << std::endl;
    if( argsVec.empty() ){
      return body;
    }else{
      body = Rewriter::rewrite( body );
      //make the forall node
      std::vector< Node > childrenVec;
      childrenVec.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, argsVec ) );
      childrenVec.push_back( body );
      if( f.getNumChildren()==3 ){ 
        Node ipl = f[2].substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
        childrenVec.push_back( ipl );
      }
      return NodeManager::currentNM()->mkNode(kind::FORALL, childrenVec );
    }
  }else{
    return f;
  }
}

Node QuantifiersRewriter::computeClause( Node n ){
  Assert( isClause( n ) );
  if( isLiteral( n ) ){
    return n;
  }else{
    NodeBuilder<> t(OR);
    if( n.getKind()==NOT ){
      if( n[0].getKind()==NOT ){
        return computeClause( n[0][0] );
      }else{
        //De-Morgan's law
        Assert( n[0].getKind()==AND );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          Node nn = computeClause( n[0][i].notNode() );
          addNodeToOrBuilder( nn, t );
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        Node nc = ( ( i==0 && n.getKind()==IMPLIES ) ? n[i].notNode() : n[i] );
        Node nn = computeClause( nc );
        addNodeToOrBuilder( nn, t );
      }
    }
    return t.constructNode();
  }
}

Node QuantifiersRewriter::computeCNF2( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred ){ 
  if( isLiteral( n ) ){
    return n;
  }else if( !forcePred && isClause( n ) ){
    return computeClause( n );
  }else{
    Kind k = ( n.getKind()==IMPLIES ? OR : ( n.getKind()==XOR ? IFF : n.getKind() ) );
    NodeBuilder<> t(k);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nc = ( i==0 && ( n.getKind()==IMPLIES || n.getKind()==XOR ) ) ? n[i].notNode() : n[i];
      Node ncnf = computeCNF2( nc, args, defs, k!=OR );
      if( k==OR ){
        addNodeToOrBuilder( ncnf, t );
      }else{
        t << ncnf;
      }
    }
    if( !forcePred && k==OR ){
      return t.constructNode();
    }else{
      //compute the free variables 
      Node nt = t;
      std::vector< Node > activeArgs;
      computeArgs( args, activeArgs, nt );
      std::vector< TypeNode > argTypes;
      for( int i=0; i<(int)activeArgs.size(); i++ ){
        argTypes.push_back( activeArgs[i].getType() );
      }
      //create the predicate
      TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
      Node op = NodeManager::currentNM()->mkVar( typ );
      std::vector< Node > predArgs;
      predArgs.push_back( op );
      predArgs.insert( predArgs.end(), activeArgs.begin(), activeArgs.end() );
      Node pred = NodeManager::currentNM()->mkNode( APPLY_UF, predArgs );
      Debug("quantifiers-rewrite-cnf-debug") << "Made predicate " << pred << " for " << nt << std::endl;
      //create the bound var list
      Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, activeArgs );
      //now, look at the structure of nt
      if( nt.getKind()==NOT ){
        //case for NOT
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[0].notNode() : nt[0] );
          tt << ( i==0 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==OR ){
        //case for OR
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i].notNode() << pred;
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i];
        }
        tt << pred.notNode();
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==AND ){
        //case for AND
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i] << pred.notNode();
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i].notNode();
        }
        tt << pred;
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==IFF ){
        //case for IFF
        for( int i=0; i<4; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( ( i==0 || i==3 ) ? nt[0].notNode() : nt[0] );
          tt << ( ( i==1 || i==3 ) ? nt[1].notNode() : nt[1] );
          tt << ( ( i==0 || i==1 ) ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==ITE ){
        //case for ITE
        for( int j=1; j<=2; j++ ){
          for( int i=0; i<2; i++ ){
            NodeBuilder<> tt(OR);
            tt << ( ( j==1 ) ? nt[0].notNode() : nt[0] );
            tt << ( ( i==1 ) ? nt[j].notNode() : nt[j] );
            tt << ( ( i==0 ) ? pred.notNode() : pred );
            defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
          }
        }
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[1].notNode() : nt[1] );
          tt << ( i==0 ? nt[2].notNode() : nt[2] );
          tt << ( i==1 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else{
        std::cout << "Unhandled Quantifiers CNF: " << nt << std::endl;
      }
      return pred;
    }
  }
}

Node QuantifiersRewriter::computeCNF( Node f ){
  std::vector< Node > args;
  std::vector< TypeNode > argTypes;
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    args.push_back( f[0][i] );
    argTypes.push_back( f[0][i].getType() );
  }
  NodeBuilder<> defs(kind::AND);
  Node nn = computeCNF2( f[1], args, defs, false );
  std::vector< Node > children;
  children.push_back( f[0] );
  children.push_back( nn );
  //carry the instantiation pattern
  if( defs.getNumChildren()==0 && f.getNumChildren()==3 ){
    children.push_back( f[2] );
  }
  nn = NodeManager::currentNM()->mkNode(kind::FORALL, children );
  defs << nn;
  return defs.getNumChildren()==1 ? defs.getChild( 0 ) : defs.constructNode();
}

Node QuantifiersRewriter::computePrenex2( Node body, std::vector< Node >& args, bool pol ){
  if( body.getKind()==FORALL ){
    if( pol ){
      //must rename each variable that already exists
      std::vector< Node > old_vars;
      std::vector< Node > vars;
      bool varChanged = false;
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
          vars.push_back( NodeManager::currentNM()->mkVar( body[0][i].getType() ) );
          varChanged = true;
        //}else{
        //  vars.push_back( body[0][i] );
        //}
        old_vars.push_back( body[0][i] );
      }
      Node newBody = body[1];
      if( varChanged ){
        newBody = newBody.substitute( old_vars.begin(), old_vars.end(), vars.begin(), vars.end() );
      }
      args.insert( args.end(), vars.begin(), vars.end() );
      //if( body[0].getKind()==NOT && body[0][0].getKind()==FORALL ){
      //  return computePrenex( body[0], args, exArgs, pol );
      //}else{
        return newBody;
      //}
    }else{
      return body;
    }
  }else if( body.getKind()==ITE || body.getKind()==XOR || body.getKind()==IFF ){
    return body;
  }else{
    Assert( body.getKind()!=EXISTS );
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      bool newPol = ( body.getKind()==NOT || ( body.getKind()==IMPLIES && i==0 ) ) ? !pol : pol;
      Node n = computePrenex2( body[i], args, newPol );
      newChildren.push_back( n );
      if( n!=body[i] ){
        childrenChanged = true;
      }
    }
    if( childrenChanged ){
      if( body.getKind()==NOT && newChildren[0].getKind()==NOT ){
        return newChildren[0][0];
      }else{
        return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
      }
    }else{
      return body;
    }
  }
}

Node QuantifiersRewriter::computePrenex( Node f ){
  std::vector< Node > args;
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    args.push_back( f[0][i] );
  }
  Node n = computePrenex2( f[1], args, true );
  std::vector< Node > children;
  children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
  children.push_back( n );
  if( f.getNumChildren()==3 ){
    children.push_back( f[2] );
  }
  return NodeManager::currentNM()->mkNode(kind::FORALL, children );
}

Node QuantifiersRewriter::computePreSkolem2( Node body, std::vector< Node >& args, bool pol ){
  return body;
}

Node QuantifiersRewriter::computePreSkolem( Node f ){
  return f;
#if 0
  std::vector< Node > args;
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    args.push_back( f[0][i] );
  }
  Node n = computePreSkolem2( f[1], args, true );
  std::vector< Node > children;
  children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
  children.push_back( n );
  if( f.getNumChildren()==3 ){
    children.push_back( f[2] );
  }
  return NodeManager::currentNM()->mkNode(kind::FORALL, children );
#endif
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node body, Node ipl ){
  std::vector< Node > activeArgs;
  computeArgs( args, activeArgs, body );
  if( activeArgs.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, activeArgs ) );
    children.push_back( body );
    if( !ipl.isNull() ){ 
      children.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}

Node QuantifiersRewriter::computeMiniscoping( std::vector< Node >& args, Node body, Node ipl, bool isNested ){
  //std::cout << "rewrite quant " << body << std::endl;
  if( body.getKind()==FORALL ){
    //combine arguments
    std::vector< Node > newArgs;
    for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
      newArgs.push_back( body[0][i] );
    }
    newArgs.insert( newArgs.end(), args.begin(), args.end() );
    return mkForAll( newArgs, body[ 1 ], ipl );
  }else if( !isNested ){
    if( body.getKind()==NOT ){
      //push not downwards
      if( body[0].getKind()==NOT ){
        return computeMiniscoping( args, body[0][0], ipl );
      }else if( body[0].getKind()==AND ){
        if( doMiniscopingNoFreeVar() ){
          NodeBuilder<> t(kind::OR);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            t <<  ( body[0][i].getKind()==NOT ? body[0][i][0] : body[0][i].notNode() );
          }
          return computeMiniscoping( args, t.constructNode(), ipl );
        }
      }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
        if( doMiniscopingAnd() ){
          NodeBuilder<> t(kind::AND);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            Node trm = ( body[0].getKind()==IMPLIES && i==0 ) ? body[0][i] : ( body[0][i].getKind()==NOT  ? body[0][i][0] : body[0][i].notNode() );
            t << computeMiniscoping( args, trm, ipl );
          }
          return t.constructNode();
        }
      }
    }else if( body.getKind()==AND ){
      if( doMiniscopingAnd() ){
        //break apart
        NodeBuilder<> t(kind::AND);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          t << computeMiniscoping( args, body[i], ipl );
        }
        Node retVal = t;
        return retVal;
      }
    }else if( body.getKind()==OR || body.getKind()==IMPLIES ){
      if( doMiniscopingNoFreeVar() ){
        Node newBody = body;
        NodeBuilder<> body_split(kind::OR);
        NodeBuilder<> tb(kind::OR);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          Node trm = ( body.getKind()==IMPLIES && i==0 ) ? ( body[i].getKind()==NOT ? body[i][0] : body[i].notNode() ) : body[i];
          if( hasArg( args, body[i] ) ){
            tb << trm;
          }else{
            body_split << trm;
          }
        }
        if( tb.getNumChildren()==0 ){
          return body_split;
        }else if( body_split.getNumChildren()>0 ){
          newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
          body_split << mkForAll( args, newBody, ipl );
          return body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
        }
      }
    }
  }
  return mkForAll( args, body, ipl );
}

Node QuantifiersRewriter::rewriteQuants( Node n, bool isNested ){
  if( n.getKind()==FORALL ){
    if( !isNested ){
      //do pre-skolemization
      if( doPreSkolem( n ) ){
        Node prev = n;
        n = computePreSkolem( n );
        if( prev!=n ){
          Debug("quantifiers-rewrite-pre-skolem") << "pre-skolem: rewrite " << prev << std::endl;
          Debug("quantifiers-rewrite-pre-skolem") << " to " << std::endl;
          Debug("quantifiers-rewrite-pre-skolem") << n << std::endl;
        }
      }
    }
    //do prenexing
    if( doPrenex( n ) ){
      Node prev = n;
      n = computePrenex( n );
      if( prev!=n ){
        Debug("quantifiers-rewrite-prenex") << "prenex: rewrite " << prev << std::endl;
        Debug("quantifiers-rewrite-prenex") << " to " << std::endl;
        Debug("quantifiers-rewrite-prenex") << n << std::endl;
      }
    }
    //do variable elimination
    if( doVarElimination( n ) ){
      Node prev = n;
      //check if any variable can be eliminated
      bool success;
      do{
        Node prev2 = n;
        n = computeVarElimination( n );
        success = n!=prev2;
      }while( success );
      if( prev!=n ){
        Debug("quantifiers-rewrite-var-elim") << "var elimination: rewrite " << prev << std::endl;
        Debug("quantifiers-rewrite-var-elim") << " to " << std::endl;
        Debug("quantifiers-rewrite-var-elim") << n << std::endl;
      }
    }
    //do CNFication
    if( doCNF( n ) ){
      Node prev = n;
      n = computeCNF( n );
      if( prev!=n ){
        Debug("quantifiers-rewrite-cnf") << "CNF: rewrite " << prev << std::endl;
        Debug("quantifiers-rewrite-cnf") << " to " << std::endl;
        Debug("quantifiers-rewrite-cnf") << n << std::endl;
      }
    }
    return n;
  }else if( isLiteral( n ) ){
    return n;
  }else{
    NodeBuilder<> tt(n.getKind());
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      tt << rewriteQuants( n[i], isNested );
    }
    return tt.constructNode();
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

bool QuantifiersRewriter::doPreSkolem( Node f ){
  return Options::current()->preSkolemQuant;
}

bool QuantifiersRewriter::doPrenex( Node f ){
  return Options::current()->prenexQuant;
}

bool QuantifiersRewriter::doVarElimination( Node f ){
  return Options::current()->varElimQuant;
}

bool QuantifiersRewriter::doCNF( Node f ){
  return Options::current()->cnfQuant;
}
