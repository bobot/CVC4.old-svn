#include "lfsc_proof.h"



LFSCProof* LFSCProof::hole = NULL;

void LFSCProof::init(){
  hole = LFSCProofSym::make( "_" );
}

void LFSCProofC::print( std::ostream& os ){
  os << "(";
  switch( id ){
  case rule_R: os << "R";break;
  case rule_Q: os << "Q";break;
  case rule_satlem: os << "satlem";break;
  }
  int counter = 0;
  while( kids[counter] ){
    os << " ";
    kids[counter]->print( os );
  }
  os << ")";
}

void LFSCProofLam::print( std::ostream& os ){
  os << "(";
  if( typ ){
    os << "% ";
  }else{
    os << "\\ ";
  }
  var->print( os );
  os << " ";
  if( typ ){
    typ->print( os );
    os << std::endl;
  }
  body->print( os );
  os << ")";
}

LFSCProof* LFSCProof::make_R( LFSCProof* u1, LFSCProof* u2, LFSCProof* n ){
  LFSCProof **kids = new LFSCProof *[5];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = u1;
  kids[3] = u2;
  kids[4] = n;
  return new LFSCProofC( rule_R, kids );
}

LFSCProof* LFSCProof::make_Q( LFSCProof* u1, LFSCProof* u2, LFSCProof* n ){
  LFSCProof **kids = new LFSCProof *[5];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = u1;
  kids[3] = u2;
  kids[4] = n;
  return new LFSCProofC( rule_Q, kids );
}

LFSCProof* LFSCProof::make_satlem( LFSCProof* u1, LFSCProof* u2 ){
  LFSCProof **kids = new LFSCProof *[5];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = hole;
  kids[3] = u1;
  kids[4] = u2;
  return new LFSCProofC( rule_satlem, kids );
}


