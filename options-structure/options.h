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
    void set(T, const typename T::type&) {
      T::you_are_trying_to_assign_to_a_read_only_option;
    }

    template <class T>
    const typename T::type& operator[](T) const;
  };
}

