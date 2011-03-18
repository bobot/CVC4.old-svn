#include <boost/function.hpp>
#include <utility>

template<typename T, typename S>
std::pair<int,S> runPortfolio(int numThreads, 
			 boost::function<T()> driverFn,
			 boost::function<S()> threadFns[]);
// as we have defined things, S=void would give compile errors
// do we want to fix this? yes, no, maybe?

#include "portfolio.cpp"	/* bah! */
