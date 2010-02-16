
#include "theory/uf/theory_uf.h"
#include "theory/uf/ecdata.h"
#include "expr/kind.h"

using namespace CVC4;
using namespace theory;
using namespace context;


enum TmpEnum {EC};

void setAttribute(Node n, TmpEnum te, ECData * ec){}

ECData* getAttribute(Node n, TmpEnum te) { return NULL; }

void TheoryUF::setup(const Node& n){
  ECData * ecN = new ECData(n);

  //TODO Make sure attribute manager owns the pointer
  setAttribute(n, EC, ecN);

  if(n.getKind() == APPLY){
    for(Node::iterator cIter = n.begin(); cIter != n.end(); ++cIter){
      Node child = *cIter;
      
      ECData * ecChild = getAttribute(child, EC);
      ecChild = ccFind(ecChild);

      ecChild->addPredecessor(n, d_context);
    }
  }
}

bool TheoryUF::equiv(Node x, Node y){
  if(x.getNumChildren() != y.getNumChildren())
    return false;

  if(x.getOperator() != y.getOperator())
    return false;

  Node::iterator xIter = x.begin();
  Node::iterator yIter = y.begin();

  while(xIter != x.end()){
    
    if(ccFind(getAttribute(*xIter, EC)) !=
       ccFind(getAttribute(*yIter, EC)))
      return false;

    ++xIter;
    ++yIter;
  }
  return true;
}

ECData* TheoryUF::ccFind(ECData * x){
  if( x->getFind() == x)
    return x;
  else{
    return ccFind(x->getFind());
  }
}

void TheoryUF::ccUnion(ECData* ecX, ECData* ecY){
  ECData* nslave;
  ECData* nmaster;

  if(ecX->getClassSize() <= ecY->getClassSize()){
    nslave = ecX;
    nmaster = ecY;
  }else{
    nslave = ecY;
    nmaster = ecX;
  }

  for(List* Px = nmaster->getFirst(); Px != NULL; Px = Px->next ){
    for(List * Py = nslave->getFirst(); Py != NULL; Py = Py->next ){
      if(equiv(Px->data,Py->data)){
        d_pending.push_back((Px->data).eqExpr(Py->data));
      }
    }
  }

  ECData::takeOverClass(nslave, nmaster);
}

//TODO make parameters soft references
void TheoryUF::merge(){
  do{
    Node assertion = d_pending.back();
    d_pending.pop_back();
    
    Node x = assertion[0];
    Node y = assertion[1];
    
    ECData* ecX = getAttribute(xRep, EC);
    ECData* ecY = getAttribute(yRep, EC);
    
    ecX = ccFind(ecX);
    ecY = ccFind(ecY);
    
    if(ecX == ecY)
      continue;
    
    ccUnion(ecX, ecY);
  }while(! d_pending.empty() );
}

void TheoryUF::check(OutputChannel& out, Effort level){
  while(!done()){
    Node assertion = get();
    
    switch(assertion.getKind()){
    case EQUAL:
      d_pending.push_back(assertion);
      merge();
      break;
    case NOT:
      d_disequality.push_back(assertion[0]);
      break;
    default:
      Unreachable();
    }
  }
  if(fullEffort(level)){
    for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter){
      
      if(ccFind(getAttribute((*diseqIter)[0], EC)) ==
         ccFind(getAttribute((*diseqIter)[1], EC))){
        out.conflict(*diseqIter, true);
      }
    }
  }
}
