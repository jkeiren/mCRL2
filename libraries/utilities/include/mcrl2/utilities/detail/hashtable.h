// Author(s): Maurice Laveaux
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#ifndef MCRL2_UTILITIES_DETAIL_HASHTABLE_H
#define MCRL2_UTILITIES_DETAIL_HASHTABLE_H
#pragma once

#ifdef PRINT_LINEAR_PROBING_STEPS
#include <iomanip>
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#endif

#include "mcrl2/utilities/power_of_two.h" 
#include "mcrl2/utilities/hashtable.h"    // necessary for header test.
#include "mcrl2/utilities/indexed_set.h"    // necessary for header test.

namespace mcrl2
{
namespace utilities
{

#ifdef PRINT_LINEAR_PROBING_STEPS
template <class Key, typename Hash, typename Equals, typename Allocator>
inline std::ostream& hashtable<Key, Hash, Equals, Allocator>::print_linear_probing_steps(std::ostream& os)
{
  boost::multiprecision::int128_t n_inserts = 0;
  boost::multiprecision::int128_t sum_steps = 0;
  for (auto [steps, count]: m_linear_probe_step_count) {
    os << steps << ":  " << count << std::endl;
    n_inserts += count;
    sum_steps += count*steps;
  }
  boost::multiprecision::cpp_bin_float_quad avg = boost::multiprecision::cpp_bin_float_quad(sum_steps)/boost::multiprecision::cpp_bin_float_quad(n_inserts);
  os << "Total number of steps:              " << sum_steps << std::endl;
  os << "Number of inserts:                  " << n_inserts << std::endl;
  os << "Average number of steps per insert: " << std::setprecision(2) << avg << std::endl;
  return os;
}
#endif

template <class Key, typename Hash, typename Equals, typename Allocator>
inline void hashtable<Key, Hash, Equals, Allocator>::rehash(std::size_t size)
{
#ifdef PRINT_LINEAR_PROBING_STEPS
  std::cerr << "Resizing hash table with old size " << size << ". Linear probing statistics for old table: " << std::endl;
  print_linear_probing_steps(std::cerr);
  m_linear_probe_step_count.clear();
#endif //PRINT_LINEAR_PROBING_STEPS

  // Copy the old hashtable.
  std::vector<Key> old = std::move(m_hashtable);

  m_hashtable = std::vector<Key>(size, nullptr);
  m_buckets_mask = m_hashtable.size() - 1;

  for (const Key& key : old)
  {
#ifdef PRINT_LINEAR_PROBING_STEPS
    std::size_t step_count = 0;
#endif //PRINT_LINEAR_PROBING_STEPS

    const std::size_t key_index = get_index(key);
    auto it = begin() + key_index;
    // Find the first empty position.
    while (*it != nullptr)
    {
      ++it;
#ifdef PRINT_LINEAR_PROBING_STEPS
      ++step_count;
#endif //PRINT_LINEAR_PROBING_STEPS
      if (it == end())
      {
        it = begin();
      }

      assert(it != begin() + key_index);
    }

#ifdef PRINT_LINEAR_PROBING_STEPS
    auto probe_it = m_linear_probe_step_count.find(step_count);
    if(probe_it == m_linear_probe_step_count.end())
    {
      probe_it = m_linear_probe_step_count.insert({step_count, 0}).first;
    }
    ++(probe_it->second);
#endif //PRINT_LINEAR_PROBING_STEPS

    // Found an empty spot, insert a new index belonging to key,
    *it = key;
  }
}

template <class Key, typename Hash, typename Equals, typename Allocator>
inline hashtable<Key,Hash,Equals,Allocator>::hashtable()
  : hashtable(128)
{
} 

template <class Key, typename Hash, typename Equals, typename Allocator>
inline hashtable<Key,Hash,Equals,Allocator>::hashtable(std::size_t initial_size,
  const hasher& hasher,
  const key_equal& equals)
      : m_hashtable(std::max(initial_size, detail::minimal_hashtable_size), nullptr),
        m_hasher(hasher),
        m_equals(equals)
{
  assert(utilities::is_power_of_two(initial_size));
  m_buckets_mask = m_hashtable.size() - 1;
}

template <class Key, typename Hash, typename Equals, typename Allocator>
inline void hashtable<Key,Hash,Equals,Allocator>::clear()
{
  m_hashtable.clear();
}

template <class Key, typename Hash, typename Equals, typename Allocator>
bool hashtable<Key,Hash,Equals,Allocator>::must_resize()
{
  return (2 * m_number_of_elements >= m_hashtable.size());
}

template <class Key, typename Hash, typename Equals, typename Allocator>
void hashtable<Key,Hash,Equals,Allocator>::resize()
{
  rehash(2 * m_hashtable.size());
}

template <class Key, typename Hash, typename Equals, typename Allocator>
inline std::pair<typename hashtable<Key,Hash,Equals,Allocator>::iterator, bool> hashtable<Key,Hash,Equals,Allocator>::insert(const Key& key)
{
  // Resize hashtable must be done explicitly.
  assert(!must_resize());
  ++m_number_of_elements;

  const std::size_t key_index = get_index(key);
  auto it = begin() + key_index;

#ifdef PRINT_LINEAR_PROBING_STEPS
  std::size_t step_count = 0;
#endif //PRINT_LINEAR_PROBING_STEPS

  // Find the first empty position.
  while (*it != nullptr)
  {
    ++it;
#ifdef PRINT_LINEAR_PROBING_STEPS
    ++step_count;
#endif //PRINT_LINEAR_PROBING_STEPS

    if (it == end())
    {
      it = begin();
    }

    assert(it != begin() + key_index);
  }

  // Found an empty spot, insert a new index belonging to key,
  *it = key;

#ifdef PRINT_LINEAR_PROBING_STEPS
  auto probe_it = m_linear_probe_step_count.find(step_count);
  if(probe_it == m_linear_probe_step_count.end())
  {
    probe_it = m_linear_probe_step_count.insert({step_count, 0}).first;
  }
  ++(probe_it->second);
#endif //PRINT_LINEAR_PROBING_STEPS

  return std::make_pair(it, true);
}


template <class Key, typename Hash, typename Equals, typename Allocator>
inline typename hashtable<Key,Hash,Equals,Allocator>::iterator hashtable<Key,Hash,Equals,Allocator>::erase(const Key& key)
{
  const std::size_t key_index = get_index(key);
  auto it = begin() + key_index;

  // Find the key.
  while (!m_equals(*it, key))
  {
    ++it;
    if (it == end())
    {
      it = begin();
    }

    if (it == begin() + key_index)
    {
      // An element not in the hashset is begin removed.
      // When optimizing, the gcc compiler tends to generate
      // destructions of non generated aterms. If this is
      // repaired, this safety escape can be removed. 
      return it; 
    }
    assert(it != begin() + key_index);
  }

  *it = nullptr;
  --m_number_of_elements;
  return it;
}

// TODO: This find is O(n), this should be made more efficient!
template <class Key, typename Hash, typename Equals, typename Allocator>
inline typename hashtable<Key,Hash,Equals,Allocator>::iterator hashtable<Key,Hash,Equals,Allocator>::find(const Key& key)
{
  for (auto it = begin(); it != end(); ++it)
  {
    if (*it == key)
    {
      return it;
    }
  }

  return end();
}

// PRIVATE FUNCTIONS

template <class Key, typename Hash, typename Equals, typename Allocator>
inline std::size_t hashtable<Key,Hash,Equals,Allocator>::get_index(const Key& key)
{
  return m_hasher(key) & m_buckets_mask;
}


} // namespace utilities

} // namespace mcrl2

#endif // MCRL2_UTILITIES_DETAIL_INDEXED_SET_H
