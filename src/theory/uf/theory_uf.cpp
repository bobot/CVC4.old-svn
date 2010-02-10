
#include "theory/uf/theory_uf.h"

struct ECData{
  unsigned classSize;
  ECData * find;

  Node rep;
  
  Link * first;
  Link ** last;

  ECData(const Node & n) :
    classSize(1), find(this), rep(n), first(NULL), last(&(first))
  {}
};

struct Link {
  Link * next;
  Node data;
  
  Link(Node n, Link * l = NULL) : next(l), data(n) {}
};


void TheoryUF::setup(const Node& n){
  ECData * ecN = new ECData(n);

  setAttribute(n, EC, 1);

  if(n.getKind() == APPLY){
    for(Node::iterator cIter = n.begin(); cIter != n.end(); ++cIter){
      Node child = *cIter;
      
      ECData* ecChild = getAttribute(child, EC);
      ecChild = ccFind(ecChild);
      

      *(ecChild->last) = new Link(n);
      ecChild->last = &(*(ecChild->last)->next);
      
    }
  }
}

bool equiv(Node x, Node y){
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

inline void takeOverClass(ECData * nslave, ECData * nmaster){
  nmaster->classSize += nslave->classSize;
  
  nslave->find = nmaster;

  for(List * Px = nmaster->first; Px != NULL; Px = Px->next ){
    for(List * Py = nslave->first; Py != NULL; Py = Py->next ){
      if(equiv(Px->data,Py->data)){
        d_pending.push_back(mkNode(Equality(Px->data, Py->data)));
      }
    }

  }

  *(nmaster->last) = nslave->first;
  nmaster->last = nslave->last;
}

ECData* TheoryUF::ccFind(ECData * x){
  if( x->find == x)
    return x;
  else{
    return ccFind(x->find);
  }
}

void TheoryUF::ccUnion(ECData* ecX, ECData* ecY){

  if(exX->classSize <= ecY->classSize){
    takeOverClass(ecX, ecY);
  }else{
    takeOverClass(ecY, ecX);
  }
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
    
    ccUnion(x,y);
  }while(! d_pending.empty() );
}

void TheoryUF::check(OutputChannel& out, Effort level){
  while(!done){
    Node assertion = get();
    
    switch(assertion.getKind()){
    case EQUALITY:
      d_pending.push_back(assertion);
      merge();
      break;
    case NOT:
      d_disequality.push_back(assertion[0]);
      break;
    }
  }
  if(fullEffort(level)){
    for(vector<Node>::iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter){
      
      if(ccFind(getAttribute((*diseqIter)[0], EC)) ==
         ccFind(getAttribute((*diseqIter)[1], EC))){
        out.conflict(*diseqIter, true);
      }
    }
  }
}
