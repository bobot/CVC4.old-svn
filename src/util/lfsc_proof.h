#ifndef LFSC_PROOF_LIB_H
#define LFSC_PROOF_LIB_H

#include <string>

namespace CVC4{

namespace prop{

class LFSCProof{
protected:
  enum{
    rule_R,
    rule_Q,
    rule_satlem,
  };
  static LFSCProof* hole;
  LFSCProof(){}
public:
  virtual ~LFSCProof(){}
  static void init();

  //functions to build LFSC proofs
  static LFSCProof* make_R( LFSCProof* u1, LFSCProof* u2, LFSCProof* n );
  static LFSCProof* make_Q( LFSCProof* u1, LFSCProof* u2, LFSCProof* n );
  static LFSCProof* make_satlem( LFSCProof* u1, LFSCProof* u2 );

  virtual void set_child( int i, LFSCProof* e ) {}
  virtual void print( std::ostream& os ){}
};

class LFSCProofC : public LFSCProof{
  short id;
  LFSCProof **kids;
public:
  LFSCProofC( short d_id, LFSCProof **d_kids ) : id( d_id ), kids( d_kids ){}
  void set_child( int i, LFSCProof* e ) { kids[i] = e; }
  void print( std::ostream& os );
};

class LFSCProofSym : public LFSCProof{
private:
  std::string s;
  LFSCProofSym( std::string ss ) : s( ss ){}
public:
  static LFSCProofSym* make( std::string ss ) { return new LFSCProofSym( ss ); }
  static LFSCProofSym* make( const char* ss ) { return new LFSCProofSym( std::string( ss ) ); }
  ~LFSCProofSym(){}
  void print( std::ostream& os ) { os << s.c_str(); }
};

class LFSCProofLam : public LFSCProof{
  LFSCProofSym* var;
  LFSCProof* body;
  LFSCProof* typ;
  LFSCProofLam( LFSCProofSym* d_var, LFSCProof* d_body, LFSCProof* d_typ ) : var( d_var ), body( d_body ), typ( d_typ ){}
public:
  static LFSCProof* make( LFSCProofSym* d_var, LFSCProof* d_body, LFSCProof* d_typ = NULL ) {
    return new LFSCProofLam( d_var, d_body, d_typ );
  }
  ~LFSCProofLam(){}

  void print( std::ostream& os );
};


LFSCProof* LFSCProof::hole = NULL;

void LFSCProof::init(){
  hole = LFSCProofSym::make( "_" );
}

void LFSCProofC::print( std::ostream& os ){
  os << "(";
  switch( id ){
  case rule_R: os << "R";break;
  case rule_Q: os << "Q";break;
  case rule_satlem: os << "\n satlem";break;
  }
  int counter = 0;
  while( kids[counter]!= NULL ){
    os << " ";
    kids[counter]->print( os );
    counter++;
  }
  os << ")";
}

void LFSCProofLam::print( std::ostream& os ){
  os << "(";
  if( typ ){
    os << "% ";
  }else{
    os << "\n \\ ";
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
  LFSCProof **kids = new LFSCProof *[6];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = u1;
  kids[3] = u2;
  kids[4] = n;
  kids[5] = 0;
  return new LFSCProofC( rule_R, kids );
}

LFSCProof* LFSCProof::make_Q( LFSCProof* u1, LFSCProof* u2, LFSCProof* n ){
  LFSCProof **kids = new LFSCProof *[6];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = u1;
  kids[3] = u2;
  kids[4] = n;
  kids[5] = 0;
  return new LFSCProofC( rule_Q, kids );
}

LFSCProof* LFSCProof::make_satlem( LFSCProof* u1, LFSCProof* u2 ){
  LFSCProof **kids = new LFSCProof *[6];
  kids[0] = hole;
  kids[1] = hole;
  kids[2] = hole;
  kids[3] = u1;
  kids[4] = u2;
  kids[5] = 0;
  return new LFSCProofC( rule_satlem, kids );
}


} // namespace prop
} // namespace CVC4


#endif
