// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/split_ranges.h
/// \brief Splits summands whose condition bounds a numeric parameter to a small range.
///
/// A summand with a condition such as `0 < a && a < 3` and an update such as `a := a + 1` is
/// replaced by one summand per value in the range, with the extra conjunct `a == k`. In each of
/// these summands the value of `a` before and after the step is a constant, which makes `a` a
/// control flow parameter in the sense of `lpsstategraph`. The conditions of the new summands
/// partition the original condition, so the LTS is unchanged.

#ifndef MCRL2_LPS_SPLIT_RANGES_H
#define MCRL2_LPS_SPLIT_RANGES_H

#include "mcrl2/data/join.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/standard_numbers_utility.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
#include "mcrl2/lps/specification.h"

#include <algorithm>
#include <map>
#include <optional>
#include <utility>
#include <vector>

namespace mcrl2::lps
{

struct split_ranges_options
{
  /// \brief The maximal number of values in a range that is split into separate summands.
  std::size_t max_range = 16;
};

namespace detail
{

class split_ranges_algorithm
{
protected:
  using bounds = std::pair<long long, long long>;

  specification& m_spec;
  data::rewriter m_rewr;
  split_ranges_options m_options;

  bool is_parameter(const data::data_expression& x) const
  {
    if (!data::is_variable(x))
    {
      return false;
    }
    const data::variable_list& parameters = m_spec.process().process_parameters();
    return std::find(parameters.begin(), parameters.end(), atermpp::down_cast<data::variable>(x)) != parameters.end();
  }

  // Returns the value of a numeral, if x is one.
  static std::optional<long long> numeral_value(const data::data_expression& x)
  {
    if (data::sort_pos::is_positive_constant(x))
    {
      return std::stoll(data::sort_pos::positive_constant_as_string(x));
    }
    if (data::sort_nat::is_natural_constant(x))
    {
      return std::stoll(data::sort_nat::natural_constant_as_string(x));
    }
    if (data::sort_int::is_integer_constant(x))
    {
      return std::stoll(data::sort_int::integer_constant_as_string(x));
    }
    return std::nullopt;
  }

  // Returns the numeral of sort s with the given value, if it exists.
  static std::optional<data::data_expression> numeral(const data::sort_expression& s, long long value)
  {
    if (data::sort_pos::is_pos(s) && value > 0)
    {
      return data::sort_pos::pos(std::to_string(value));
    }
    if (data::sort_nat::is_nat(s) && value >= 0)
    {
      return data::sort_nat::nat(std::to_string(value));
    }
    if (data::sort_int::is_int(s))
    {
      return data::sort_int::int_(std::to_string(value));
    }
    return std::nullopt;
  }

  // Computes the bounds [lo, hi] of the parameters constrained by comparisons with numerals in the
  // conjuncts of a condition. Only ranges of at most max_range values are returned.
  std::map<data::variable, bounds> range_bounds(const data::data_expression& condition)
  {
    std::map<data::variable, long long> lower;
    std::map<data::variable, long long> upper;
    auto add = [](std::map<data::variable, long long>& m, const data::variable& p, long long v, bool is_lower)
    {
      auto i = m.find(p);
      if (i == m.end())
      {
        m[p] = v;
      }
      else
      {
        i->second = is_lower ? std::max(i->second, v) : std::min(i->second, v);
      }
    };
    for (const data::data_expression& c: data::split_and(condition))
    {
      const bool strict = data::is_less_application(c) || data::is_greater_application(c);
      const bool non_strict = data::is_less_equal_application(c) || data::is_greater_equal_application(c);
      if (!strict && !non_strict)
      {
        continue;
      }
      // Normalise to left < right or left <= right.
      const bool greater = data::is_greater_application(c) || data::is_greater_equal_application(c);
      const data::data_expression left = greater ? data::binary_right1(c) : data::binary_left1(c);
      const data::data_expression right = greater ? data::binary_left1(c) : data::binary_right1(c);
      const long long offset = strict ? 1 : 0;
      if (is_parameter(right))
      {
        if (std::optional<long long> v = numeral_value(m_rewr(left)))
        {
          add(lower, atermpp::down_cast<data::variable>(right), *v + offset, true);
        }
      }
      else if (is_parameter(left))
      {
        if (std::optional<long long> v = numeral_value(m_rewr(right)))
        {
          add(upper, atermpp::down_cast<data::variable>(left), *v - offset, false);
        }
      }
    }
    std::map<data::variable, bounds> result;
    for (const auto& [p, lo]: lower)
    {
      auto i = upper.find(p);
      if (i != upper.end() && lo <= i->second && static_cast<std::size_t>(i->second - lo) < m_options.max_range)
      {
        result[p] = {lo, i->second};
      }
    }
    return result;
  }

  static data::data_expression next_state_value(const action_summand& s, const data::variable& p)
  {
    for (const data::assignment& a: s.assignments())
    {
      if (a.lhs() == p)
      {
        return a.rhs();
      }
    }
    return p;
  }

  // Splits s on the values of p in [lo, hi], provided that the update of p is not constant, but
  // becomes constant for every value in the range. Returns std::nullopt if s is not split.
  std::optional<std::vector<action_summand>> split(const action_summand& s, const data::variable& p, const bounds& b)
  {
    const data::data_expression update = next_state_value(s, p);
    if (update == p || data::is_constant(m_rewr(update)))
    {
      return std::nullopt;
    }
    std::vector<action_summand> result;
    for (long long k = b.first; k <= b.second; ++k)
    {
      std::optional<data::data_expression> value = numeral(p.sort(), k);
      if (!value)
      {
        return std::nullopt;
      }
      data::mutable_map_substitution<> sigma;
      sigma[p] = *value;
      if (!data::is_constant(m_rewr(update, sigma)))
      {
        return std::nullopt;
      }
      action_summand part = s;
      part.condition() = data::sort_bool::and_(data::equal_to(p, *value), s.condition());
      result.push_back(part);
    }
    return result;
  }

public:
  split_ranges_algorithm(specification& spec, const data::rewriter& rewr, const split_ranges_options& options)
    : m_spec(spec),
      m_rewr(rewr),
      m_options(options)
  {}

  /// \brief Applies the transformation and returns the number of summands that were split.
  std::size_t run()
  {
    std::size_t splits = 0;
    action_summand_vector result;
    for (const action_summand& summand: m_spec.process().action_summands())
    {
      std::vector<action_summand> todo = {summand};
      for (const auto& [p, b]: range_bounds(summand.condition()))
      {
        std::vector<action_summand> next;
        for (const action_summand& s: todo)
        {
          std::optional<std::vector<action_summand>> parts = split(s, p, b);
          if (parts)
          {
            next.insert(next.end(), parts->begin(), parts->end());
            ++splits;
          }
          else
          {
            next.push_back(s);
          }
        }
        todo = next;
      }
      result.insert(result.end(), todo.begin(), todo.end());
    }
    mCRL2log(log::log_level_t::verbose) << "split ranges: " << splits << " summands split, "
                                        << m_spec.process().action_summands().size() << " -> " << result.size()
                                        << " action summands" << std::endl;
    m_spec.process().action_summands() = result;
    return splits;
  }
};

} // namespace detail

/// \brief Splits every action summand whose condition bounds a numeric parameter to a range of at
/// most options.max_range values, and whose update of that parameter is constant for each value
/// in the range but not in general, into one summand per value. The LTS is unchanged.
/// \return The number of summands that were split.
inline std::size_t split_ranges(specification& spec,
  const data::rewriter& rewr,
  const split_ranges_options& options = split_ranges_options())
{
  return detail::split_ranges_algorithm(spec, rewr, options).run();
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_SPLIT_RANGES_H
