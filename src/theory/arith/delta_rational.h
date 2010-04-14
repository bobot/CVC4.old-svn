
/**
 * A DeltaRational is a pair of rationals (c,k) that represent the number
 *   c + kd
 * where d is an implicit system wide symbolic infinitesimal.
 */
class DeltaRational {
private:
  Rational c;
  Rational k;

public:
  DeltaRational() : c(0), k(0) {}
  DeltaRational(Rational& base, Rational& coeff) : c(base), k(coeff) {}
  DeltaRational(Rational& r, int i = 0) : c(k), k(i) {}

  DeltaRational operator+(DeltaRational& other){
    return DeltaRational(c+other.c, k + other.k);
  }

  DeltaRational operator*(Rational& a){
    return DeltaRational(a*c,a*k);
  }

  bool operator==(DeltaRational& other){
    return (k == other.k) && (c == other.c);
  }

  bool operator<=(DeltaRational& other){
    int cmp = c.cmp(other.c);
    return (cmp < 0) || ((cmp==0)&&(k <= other.k));
  }
  bool operator<(DeltaRational& other){
    return (other  > *this);
  }
  bool operator>=(DeltaRational& other){
    return (other <= *this);
  }
  bool operator>(DeltaRational& other){
    return !(*this <= other);
  }

  DeltaRational& operator=(DeltaRational& r){
    c = other.c;
    k = other.k;
  }

  DeltaRational& operator*=(Rational& a){
    c *= a;
    k *= a;

    return *(this);
  }

  DeltaRational& operator+=(DeltaRational& other){
    c+=other.c;
    k+=other.k;
  }
};
