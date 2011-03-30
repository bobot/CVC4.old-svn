
#ifndef __CVC4__CHANNEL_H
#define __CVC4__CHANNEL_H

#include <boost/circular_buffer.hpp>
#include <boost/thread/mutex.hpp>
#include <boost/thread/condition.hpp>
#include <boost/thread/thread.hpp>
#include <boost/call_traits.hpp>
#include <boost/progress.hpp>
#include <boost/bind.hpp>


namespace CVC4 {

template <typename T>
class SharedChannel {
private:
  int d_maxsize;                // just call it size?
public:
  SharedChannel() {}
  SharedChannel(int maxsize) : d_maxsize(maxsize) {}

  /* Tries to add element and returns true if successful */
  virtual bool push(const T&) = 0;

  /* Removes an element from the channel */
  virtual T pop() = 0;
  
  /* */
  virtual bool empty() = 0; 
  
  /* */
  virtual bool full() = 0;
};

/* 
This code is from

http://live.boost.org/doc/libs/1_46_1/libs/circular_buffer/doc/circular_buffer.html#boundedbuffer 

Overkill, it would probably have been better to have written one myself.
*/
template <typename T>
class SynchronizedSharedChannel: public SharedChannel<T> {
public:
  typedef boost::circular_buffer<T> container_type;
  typedef typename container_type::size_type size_type;
  typedef typename container_type::value_type value_type;
  typedef typename boost::call_traits<value_type>::param_type param_type;

  explicit SynchronizedSharedChannel(size_type capacity) : m_unread(0), m_container(capacity) {}

  bool push(param_type item){
  // param_type represents the "best" way to pass a parameter of type value_type to a method
  
    boost::mutex::scoped_lock lock(m_mutex);
    m_not_full.wait(lock, boost::bind(&SynchronizedSharedChannel<value_type>::is_not_full, this));
    m_container.push_front(item);
    ++m_unread;
    lock.unlock();
    m_not_empty.notify_one();
    return true;
  }//function definitions need to be moved to cpp

  value_type pop(){
    value_type ret;
    boost::mutex::scoped_lock lock(m_mutex);
    m_not_empty.wait(lock, boost::bind(&SynchronizedSharedChannel<value_type>::is_not_empty, this));
    ret = m_container[--m_unread];
    lock.unlock();
    m_not_full.notify_one();
    return ret;
  }


  bool empty() { return not is_not_empty(); }
  bool full() { return not is_not_full(); }

private:
  SynchronizedSharedChannel(const SynchronizedSharedChannel&);              // Disabled copy constructor
  SynchronizedSharedChannel& operator = (const SynchronizedSharedChannel&); // Disabled assign operator

  bool is_not_empty() const { return m_unread > 0; }
  bool is_not_full() const { return m_unread < m_container.capacity(); }

  size_type m_unread;
  container_type m_container;
  boost::mutex m_mutex;
  boost::condition m_not_empty;
  boost::condition m_not_full;
};



// template <typename T>
// class SynchronizedSharedChannel : SharedChannel {
// private:
//   std::vector <T> d_buffer;
//   int d_readPtr;
//   int d_writePtr;
//   boost::mutex m_buffer;
//   boost::condition m_notempty; 
//   boost::condition m_notfull;
// public:
//   SharedChannel(int) : d_readPtr(0), d_writePtr(0) { d_buffer.resize(d_maxsize); }

//   bool push(const T&);
//   T pop();
// };



}

#endif /* __CVC4__CHANNEL_H */


