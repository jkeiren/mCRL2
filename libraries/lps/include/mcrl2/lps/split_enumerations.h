// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/split_enumerations.h
/// \brief Splits summands on the values of a parameter of an enumerated sort.
///
/// A summand with an update such as `active := next(active)`, where `active` has a sort whose
/// constructors are all constants, is replaced by one summand per value `c` of that sort for
/// which the condition is not false, with the extra conjunct `active == c` and the update
/// `active := next(c)` rewritten to a constant. Afterwards the value of `active` before and after
/// each step is a constant, which makes it a control flow parameter. The conditions of the new
/// summands partition the original condition, so the LTS is unchanged.
///
/// Splitting multiplies the number of summands, and only pays off if the parameter becomes a
/// control flow parameter. A parameter is therefore only split if its initial value is a constant
/// and every summand leaves it unchanged, assigns it a constant, or assigns it an expression in
/// which it is the only free variable.

#ifndef MCRL2_LPS_SPLIT_ENUMERATIONS_H
#define MCRL2_LPS_SPLIT_ENUMERATIONS_H

#include "mcrl2/data/find.h"
#include "mcrl2/data/join.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
#include "mcrl2/lps/detail/instantiate_global_variables.h"
#include "mcrl2/lps/specification.h"

#include <algorithm>
#include <optional>
#include <set>
#include <vector>

namespace mcrl2::lps
{

struct split_enumerations_options
{
  /// \brief The maximal number of values of a sort whose parameters are split.
  std::size_t max_values = 32;
};

namespace detail
{

class split_enumerations_algorithm
{
protected:
  specification& m_spec;
  data::rewriter m_rewr;
  split_enumerations_options m_options;

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

  // Returns the values of sort s if all its constructors are constants and there are at most
  // max_values of them.
  std::optional<std::vector<data::data_expression>> enumeration_values(const data::sort_expression& s) const
  {
    const data::function_symbol_vector& constructors = m_spec.data().constructors(s);
    if (constructors.empty() || constructors.size() > m_options.max_values)
    {
      return std::nullopt;
    }
    if (!std::all_of(constructors.begin(),
          constructors.end(),
          [](const data::function_symbol& f) { return !data::is_function_sort(f.sort()); }))
    {
      return std::nullopt;
    }
    return std::vector<data::data_expression>(constructors.begin(), constructors.end());
  }

  // Returns true if the update of p in s is not constant, but its only free variable is p.
  bool needs_split(const action_summand& s, const data::variable& p) const
  {
    const data::data_expression update = m_rewr(next_state_value(s, p));
    if (update == p || data::is_constant(update))
    {
      return false;
    }
    const std::set<data::variable> free = data::find_free_variables(update);
    return free.size() == 1 && free.contains(p);
  }

  // Returns true if every summand leaves p unchanged, assigns it a constant, or assigns it an
  // expression whose only free variable is p, and at least one summand does the latter.
  bool is_splittable(const data::variable& p, const data::data_expression& init) const
  {
    if (!data::is_constant(m_rewr(init)))
    {
      return false;
    }
    bool split_some = false;
    for (const action_summand& s: m_spec.process().action_summands())
    {
      const data::data_expression update = m_rewr(next_state_value(s, p));
      if (update == p || data::is_constant(update))
      {
        continue;
      }
      if (!needs_split(s, p))
      {
        return false;
      }
      split_some = true;
    }
    return split_some;
  }

  // Splits s on the values of p. Values for which the condition is false are left out.
  std::vector<action_summand>
  split(const action_summand& s, const data::variable& p, const std::vector<data::data_expression>& values) const
  {
    std::vector<action_summand> result;
    for (const data::data_expression& value: values)
    {
      data::mutable_map_substitution<> sigma;
      sigma[p] = value;
      const data::data_expression condition = m_rewr(s.condition(), sigma);
      if (condition == data::sort_bool::false_())
      {
        continue;
      }
      action_summand part = s;
      part.condition() = data::lazy::and_(data::equal_to(p, value), condition);
      data::assignment_vector assignments;
      for (const data::assignment& a: s.assignments())
      {
        assignments.push_back(a.lhs() == p ? data::assignment(p, m_rewr(a.rhs(), sigma)) : a);
      }
      part.assignments() = data::assignment_list(assignments.begin(), assignments.end());
      result.push_back(part);
    }
    return result;
  }

public:
  split_enumerations_algorithm(specification& spec,
    const data::rewriter& rewr,
    const split_enumerations_options& options)
    : m_spec(spec),
      m_rewr(rewr),
      m_options(options)
  {}

  /// \brief Applies the transformation and returns the number of parameters that were split.
  std::size_t run()
  {
    // A global variable assigned to a parameter would make its update non-constant.
    lps::detail::instantiate_global_variables(m_spec);
    const std::size_t original_size = m_spec.process().action_summands().size();
    std::size_t split_parameters = 0;
    const data::variable_list& parameters = m_spec.process().process_parameters();
    const data::data_expression_list& init = m_spec.initial_process().expressions();
    auto init_i = init.begin();
    for (const data::variable& p: parameters)
    {
      const data::data_expression& init_p = *init_i++;
      const std::optional<std::vector<data::data_expression>> values = enumeration_values(p.sort());
      if (!values || !is_splittable(p, init_p))
      {
        continue;
      }
      action_summand_vector result;
      for (const action_summand& s: m_spec.process().action_summands())
      {
        if (needs_split(s, p))
        {
          const std::vector<action_summand> parts = split(s, p, *values);
          result.insert(result.end(), parts.begin(), parts.end());
        }
        else
        {
          result.push_back(s);
        }
      }
      mCRL2log(log::log_level_t::verbose)
        << "split enumerations: parameter " << p << " split, " << m_spec.process().action_summands().size() << " -> "
        << result.size() << " action summands" << std::endl;
      m_spec.process().action_summands() = result;
      ++split_parameters;
    }
    mCRL2log(log::log_level_t::verbose) << "split enumerations: " << split_parameters << " parameters split, "
                                        << original_size << " -> " << m_spec.process().action_summands().size()
                                        << " action summands" << std::endl;
    return split_parameters;
  }
};

} // namespace detail

/// \brief Splits every action summand on the values of each parameter of an enumerated sort (at
/// most options.max_values constants) that becomes a control flow parameter by doing so: its
/// initial value is a constant and each summand leaves it unchanged, assigns it a constant or
/// assigns it an expression in which it is the only free variable. The LTS is unchanged.
/// \return The number of parameters that were split.
inline std::size_t split_enumerations(specification& spec,
  const data::rewriter& rewr,
  const split_enumerations_options& options = split_enumerations_options())
{
  return detail::split_enumerations_algorithm(spec, rewr, options).run();
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_SPLIT_ENUMERATIONS_H
