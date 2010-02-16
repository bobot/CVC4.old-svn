#include "theory/uf/ecdata.h"

using namespace CVC4;
using namespace context;
using namespace theory;


ECData::ECData(Context * context, const Node & n) :
  ContextObj(context),
  classSize(1), 
  find(this), 
  rep(n), 
  first(NULL), 
  last(NULL)
{}


bool ECData::isClassRep(){
  return this == this->find;
}

void ECData::addPredecessor(Node n, Scope* scope){
  Assert(isClassRep());


  Link * newPred = new (scope->getCMM())  Link(scope->getContext(), n, first);
  setFirst(newPred);
  if(last == NULL){
    setLast(newPred);
  }
}

ContextObj* ECData::save(ContextMemoryManager* pCMM) {
  return new(pCMM) ECData(*this);
}

void ECData::restore(ContextObj* pContextObj) {
  *this = *((ECData*)pContextObj);
}

Node ECData::getRep(){
  return rep;
}
  
unsigned ECData::getClassSize(){
  return classSize;
}

void ECData::setClassSize(unsigned newSize){
  Assert(isClassRep());

  makeCurrent();
  classSize = newSize;
}

void ECData::setFind(ECData * ec){
  makeCurrent();
  find = ec;
}

ECData * ECData::getFind(){
  return find;
}


Link* ECData::getFirst(){
  return first;
}


Link* ECData::getLast(){
  return last;
}

void ECData::setFirst(Link * nfirst){
  makeCurrent();
  first = nfirst;
}

void ECData::setLast(Link * nlast){
  makeCurrent();
  last = nlast;
}
  


void ECData::takeOverClass(ECData * nslave, ECData * nmaster){
  nmaster->setClassSize(nmaster->getClassSize() + nslave->getClassSize());
  
  nslave->setFind( nmaster );


  if(nmaster->getFirst() == NULL){
    nmaster->setFirst(nslave->getFirst());
    nmaster->setLast(nslave->getLast());
  }else if(nslave->getLast() != NULL){
    Link * currLast = nmaster->getLast();
    currLast->next = nslave->getFirst();
    nmaster->setLast(nslave->getLast());
  }
}
