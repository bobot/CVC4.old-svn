
#include "theory/uf/theory_uf.h"

class ECData : public ContextObj {
private:
  unsigned classSize;
  ECData * find;

  Node rep;
  
  Link * first;
  Link * last;


  ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) ECData(*this);
  }

  
  void restore(ContextObj* pContextObj) {
    *this = *((ECData*)pContextObj);
  }


public:
  ECData(Context * context, const Node & n) :
    ContextObj(context),
    classSize(1), 
    find(this), 
    rep(n), 
    first(NULL), 
    last(NULL)
  {}
  
  unsigned getClassSize(){
    return classSize;
  }

  void setClassSize(unsigned newSize){
    makeCurrent();
    classSize = newSize;
  }

  void updateFind(ECData * ec){
    makeCurrent();
    find = ec;
  }
  ECData * getFind(){
    return find;
  }
  
  Node getRep(){
    return rep;
  }

  Link* getFirst(){
    return first;
  }

  Link* getLast(){
    return last;
  }

  void setFirst(Link * nfirst){
    makeCurrent();
    first = nfirst;
  }

  void setLast(Link * nlast){
    makeCurrent();
    last = nlast;
  }
  
};

struct Link {
  CDO<Link *> next;
  Node data;
  
  Link(Context * context, Node n, Link * l = NULL):
    next(context, l), data(n)
  {}

  static void* operator new(size_t size, ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }
};



void TheoryUF::setup(const Node& n){
  ECData * ecN = new ECData(n);

  //TODO Make sure attribute manager owns the pointer
  setAttribute(n, EC, ecN);

  if(n.getKind() == APPLY){
    for(Node::iterator cIter = n.begin(); cIter != n.end(); ++cIter){
      Node child = *cIter;
      
      ECData * ecChild = getAttribute(child, EC);
      ecChild = ccFind(ecChild);

      Link * npred = new (d_context->getCMM())  Link(d_context, n);      
      if(ecChild->getFirst() == NULL){
        ecChild->setFirst(npred);
        ecChild->setLast(npred);
      }else{
        Link* currLast = ecChild->getLast();
        currLast->next = npred;
        ecChild->setLast(npred);
      }
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
  nmaster->setClassSize(nmaster->getClassSize() + nslave->getClassSize());
  
  nslave->setFind( nmaster );

  for(List * Px = nmaster->getFirst(); Px != NULL; Px = Px->next ){
    for(List * Py = nslave->getFirst(); Py != NULL; Py = Py->next ){
      if(equiv(Px->data,Py->data)){
        d_pending.push_back(mkNode(Equality,Px->data, Py->data));
      }
    }

  }

  if(nmaster->getFirst() == NULL){
    nmaster->setFirst(nslave->getFirst());
    nmaster->setLast(nslave->getLast());
  }else{
    Link * currLast = nmaster->getLast();
    currLast->next = nslave->getFirst();
    nmaster->setLast(nslave->getLast());
  }
}

ECData* TheoryUF::ccFind(ECData * x){
  if( x->getFind() == x)
    return x;
  else{
    return ccFind(x->getFind());
  }
}

void TheoryUF::ccUnion(ECData* ecX, ECData* ecY){

  if(exX->getClassSize() <= ecY->getClassSize()){
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
    
    ccUnion(ecX, ecY);
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
