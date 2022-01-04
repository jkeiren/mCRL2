// Author(s): Maurice Laveaux
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#ifndef MCRL2_UTILITIES_INDEXED_SET_H
#define MCRL2_UTILITIES_INDEXED_SET_H

#include <deque>
#include <mutex>

#include "mcrl2/utilities/unordered_map.h"

namespace mcrl2
{
namespace utilities
{
namespace detail
{

struct alignas (64) thread_control
{
  std::atomic<bool> busy_flag;
  std::atomic<bool> forbidden_flag;
  // For this thread the keys at positions reserved_numbers_begin until
  // reserved_numbers_end have been reserved for this thread. 
  std::size_t reserved_numbers_begin=0, reserved_numbers_end=0;

  thread_control() = default;

  thread_control(const thread_control& other)
  {
    // Do not copy the busy and forbidden flags. 
    reserved_numbers_begin=other.reserved_numbers_begin;
    reserved_numbers_end=other.reserved_numbers_end;
  }

  thread_control(thread_control&& other)
  {
    // Do not copy the busy and forbidden flags. 
    reserved_numbers_begin=other.reserved_numbers_begin;
    reserved_numbers_end=other.reserved_numbers_end;
  }

  thread_control& operator=(const thread_control& other)
  {
    // Do not copy the busy and forbidden flags. 
    reserved_numbers_begin=other.reserved_numbers_begin;
    reserved_numbers_end=other.reserved_numbers_end;
    return *this;
  }

  thread_control& operator=(thread_control&& other)
  {
    // Do not copy the busy and forbidden flags. 
    reserved_numbers_begin=other.reserved_numbers_begin;
    reserved_numbers_end=other.reserved_numbers_end;
    return *this;
  }

  
};

} // namespace detail

/// \brief A set that assigns each element an unique index.
template<typename Key,
         typename Hash = std::hash<Key>,
         typename Equals = std::equal_to<Key>,
         typename Allocator = std::allocator<Key>,
         bool ThreadSafe = false,
         typename KeyTable = std::deque< Key, Allocator > > 
class indexed_set
{
private:
  // std::vector<std::atomic<std::size_t> > m_hashtable;
  std::vector<std::size_t> m_hashtable;
  KeyTable m_keys;

  /// \brief Mutex for the m_hashtable and m_keys data structures.
  mutable std::shared_ptr<std::mutex> m_mutex;
  mutable std::vector<detail::thread_control> m_thread_control;

  Hash m_hasher;
  Equals m_equals;

  void lock_shared(std::size_t thread_index) const;
  void unlock_shared(std::size_t thread_index) const;
  void lock_exclusive(std::size_t thread_index) const;
  void unlock_exclusive(std::size_t thread_index) const;

  /// \brief Check whether this index is refers to a valid object,
  //         or to a reserved, non used spot. In the latter case false is returned.
  bool check_index_validity(std::size_t index);
  
  /// \brief Reserve indices that this thread can use. Doing this 
  ///        infrequently prevents obtaining an exclusive lock for the
  ///        indexed set too often. 
  void reserve_indices_for_this_thread(std::size_t thread_index);
  /// \brief Inserts the given (key, n) pair into the indexed set.
  std::size_t put_in_hashtable(const Key& key, std::size_t value);

  /// \brief Resizes the hash table to twice its current size.
  inline void resize_hashtable();

public:
  typedef Key key_type;
  typedef std::size_t size_type;
  typedef std::pair<const key_type, size_type> value_type;
  typedef Equals key_equal;
  typedef Hash hasher;

  typedef value_type& reference;
  typedef const value_type& const_reference;
  typedef value_type* pointer;
  typedef const value_type* const_pointer;

  typedef typename KeyTable::iterator iterator;
  typedef typename KeyTable::const_iterator const_iterator;

  typedef typename KeyTable::reverse_iterator reverse_iterator;
  typedef typename KeyTable::const_reverse_iterator const_reverse_iterator;

  typedef std::ptrdiff_t difference_type;
  
  /// \brief Value returned when an element does not exist in the set.
  /// \return Value indicating non existing element, equal to std::numeric_limits<std::size_t>::max(). 
  static constexpr size_type npos = std::numeric_limits<std::size_t>::max();

  /// \brief Constructor of an empty indexed set. Starts with a hashtable of size 128 and assumes one single thread.
  indexed_set()
    : indexed_set(1)
  {}

  /// \brief Constructor of an empty indexed set. 
  /// \detail With a single thread it delivers contiguous values for states.
  ///         With multiple threads some indices may be skipped. Each thread
  ///         reserves numbers, which it hands out. If a thread does not have
  ///         the opportunity to hand out all numbers, holes in the contiguous
  ///         numbering can occur. The holes are always of limited size. 
  /// \param The number of threads that use this index set. 
  indexed_set(std::size_t number_of_threads);

  /// \brief Constructor of an empty index set. Starts with a hashtable of the indicated size. 
  /// \details With one thread the numbering is contiguous. With multiple threads limited size holes
  ///          can occur in the numbering. 
  /// \param The number of threads that use this index set. 
  /// \param initial_hashtable_size The initial size of the hashtable.
  /// \param hash The hash function.
  /// \param equals The comparison function for its elements.
  indexed_set(std::size_t number_of_threads,
    std::size_t initial_hashtable_size,
    const hasher& hash = hasher(),
    const key_equal& equals = key_equal());

  /// \brief Returns a reference to the mapped value.
  /// \details Returns an invalid value, larger or equal than the size of the indexed set, if there is no element with the given key.
  size_type index(const key_type& key, std::size_t thread_index=0) const;

  /// \brief Returns a reference to the mapped value.
  /// \details Returns an out_of_range exception if there is no element with the given key.
  /// \param index The position in the indexed set.
  /// \return The value at position index.
  const key_type& at(const size_type index) const;

  /// \brief Operator that provides a const reference at the position indicated by index.
  /// \param index The position in the indexed set.
  /// \return The value at position index.
  /// \threadsafe
  const key_type& operator[](const size_type index) const;

  /// \brief Forward iterator which runs through the elements from the lowest to the largest number.
  /// \details Complexity is constant per operation.
  iterator begin() 
  { 
    return m_keys.begin(); 
  }

  /// \brief End of the forward iterator.
  iterator end()
  { 
    return m_keys.end(); 
  }

  /// \brief Forward iterator which runs through the elements from the lowest to the largest number.
  /// \details Complexity is constant per operation.
  const_iterator begin() const
  {
    return m_keys.begin();
  }

  /// \brief End of the forward iterator.
  const_iterator end() const
  {
    return m_keys.end();
  }

  /// \brief const_iterator going through the elements in the set numbered from zero upwards. 
  const_iterator cbegin() const
  { 
    return m_keys.cbegin(); 
  }

  /// \brief End of the forward const_iterator. 
  const_iterator cend() const 
  { 
    return m_keys.cend(); 
  }

  /// \brief Reverse iterator going through the elements in the set from the largest to the smallest index. 
  iterator rbegin() 
  { 
    return m_keys.rbegin(); 
  }

  /// \brief End of the reverse iterator. 
  iterator rend()
  { 
    return m_keys.rend(); 
  }

  /// \brief Reverse const_iterator going through the elements from the highest to the lowest numbered element. 
  const_iterator crbegin() const
  { 
    return m_keys.crbegin(); 
  }

  /// \brief End of the reverse const_iterator. 
  const_iterator crend() const 
  { 
    return m_keys.crend(); 
  }

  /// \brief Clears the indexed set by removing all its elements. It is not guaranteed that the memory is released too. 
  void clear(std::size_t thread_index=0);

  /// \brief Insert a key in the indexed set and return its index. 
  /// \details If the element was already in the set, the resulting bool is true, and the existing index is returned.
  ///         Otherwise, the key is inserted in the set, and the next available index is assigned to it. 
  /// \param  key The key to be inserted in the set.
  /// \return The index of the key and a boolean indicating whether the element was actually inserted.
  /// \threadsafe
  std::pair<size_type, bool> insert(const key_type& key, std::size_t thread_index=0);

  /// \brief Provides an iterator to the stored key in the indexed set.
  /// \param key The key that is sought.
  /// \return An iterator to the key, otherwise end().
  const_iterator find(const key_type& key, std::size_t thread_index=0) const;

  /// \brief The number of elements in the indexed set.
  /// \return The number of elements in the indexed set. 
  /// \threadsafe
  size_type size() const
  { 
    std::size_t correction=0;
    for(detail::thread_control& c: m_thread_control)
    {
      correction=correction + c.reserved_numbers_end-c.reserved_numbers_begin;
    }
    return m_keys.size()-correction;
  }
};

} // end namespace utilities
} // end namespace mcrl2

#include "mcrl2/utilities/detail/indexed_set.h"


#endif // MCRL2_UTILITIES_INDEXED_SET_H
