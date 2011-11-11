#pragma once

namespace CVC4 {
  struct options_holder;

  class Options {
    options_holder* d_holder;
    static Options d_current;
  public:
    Options();
    static Options& current() { return d_current; }
    template <class T>
    typename T::type& operator[](T);
  };
}

