// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/control_invariant.h
/// \brief Strengthens the conditions of an LPS with a pairwise invariant over its control parameters.
///
/// A parameter is *trackable* if every summand either leaves it unchanged or assigns it a value that
/// is constant once the parameter values fixed by the condition (the *sources*) are substituted.
/// For pairs of trackable parameters that are both fixed by the condition of some summand, the set
/// of reachable value pairs is over-approximated by a joint least fixpoint, in which the guard of a
/// summand on parameters outside the pair is checked against the other pairs. The resulting
/// invariant is used to derive additional sources, which are conjoined to the conditions, and to
/// remove summands that are never enabled in a reachable state. The result is strongly bisimilar to
/// the input (strengthening with an inductive invariant that holds initially).
///
/// Summands whose condition bounds a numeric parameter to a small range, and whose update of that
/// parameter is constant for every value in the range, are split into one summand per value first.

#ifndef MCRL2_LPS_CONTROL_INVARIANT_H
#define MCRL2_LPS_CONTROL_INVARIANT_H

#include "mcrl2/data/join.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/standard_numbers_utility.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
#include "mcrl2/lps/detail/instantiate_global_variables.h"
#include "mcrl2/lps/specification.h"

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <utility>
#include <vector>

namespace mcrl2::lps
{

struct control_invariant_options
{
  /// \brief The maximal number of values in a range that is split into separate summands.
  std::size_t max_range = 16;
};

namespace detail
{

class control_invariant_algorithm
{
protected:
  using value_pair = std::pair<data::data_expression, data::data_expression>;
  using scope = std::pair<std::size_t, std::size_t>;
  using valuation = std::map<std::size_t, data::data_expression>;

  specification& m_spec;
  data::rewriter m_rewr;
  control_invariant_options m_options;
  std::vector<data::variable> m_parameters;

  // Per summand (action summands first, then deadlock summands).
  std::vector<valuation> m_sources;
  std::vector<valuation> m_targets;
  std::vector<std::set<std::size_t>> m_assigned;
  std::vector<bool> m_dead;
  std::vector<valuation> m_derived;

  std::vector<bool> m_trackable;
  std::vector<std::set<data::data_expression>> m_values;
  std::vector<scope> m_scopes;
  std::map<scope, std::set<value_pair>> m_reachable;
  std::map<std::size_t, std::vector<scope>> m_scopes_of;

  std::size_t action_summand_count() const
  {
    return m_spec.process().action_summands().size();
  }
  std::size_t summand_count() const
  {
    return action_summand_count() + m_spec.process().deadlock_summands().size();
  }

  const data::data_expression& condition(std::size_t j) const
  {
    if (j < action_summand_count())
    {
      return m_spec.process().action_summands()[j].condition();
    }
    return m_spec.process().deadlock_summands()[j - action_summand_count()].condition();
  }

  std::optional<std::size_t> parameter_index(const data::data_expression& x) const
  {
    if (!data::is_variable(x))
    {
      return std::nullopt;
    }
    auto i = std::find(m_parameters.begin(), m_parameters.end(), atermpp::down_cast<data::variable>(x));
    if (i == m_parameters.end())
    {
      return std::nullopt;
    }
    return static_cast<std::size_t>(i - m_parameters.begin());
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

  // Computes the bounds [lo, hi] of the numeric parameters constrained by the conjuncts of a condition.
  std::map<std::size_t, std::pair<long long, long long>> range_bounds(const data::data_expression& cond)
  {
    std::map<std::size_t, long long> lower;
    std::map<std::size_t, long long> upper;
    auto add = [&](std::map<std::size_t, long long>& m, std::size_t i, long long v, bool is_lower)
    {
      auto j = m.find(i);
      if (j == m.end())
      {
        m[i] = v;
      }
      else
      {
        j->second = is_lower ? std::max(j->second, v) : std::min(j->second, v);
      }
    };
    for (const data::data_expression& c: data::split_and(cond))
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
      std::optional<std::size_t> p = parameter_index(right);
      std::optional<long long> v = numeral_value(m_rewr(left));
      if (p && v) // v < p, v <= p
      {
        add(lower, *p, *v + offset, true);
        continue;
      }
      p = parameter_index(left);
      v = numeral_value(m_rewr(right));
      if (p && v) // p < v, p <= v
      {
        add(upper, *p, *v - offset, false);
      }
    }
    std::map<std::size_t, std::pair<long long, long long>> result;
    for (const auto& [i, lo]: lower)
    {
      auto j = upper.find(i);
      if (j != upper.end() && lo <= j->second && static_cast<std::size_t>(j->second - lo) < m_options.max_range)
      {
        result[i] = {lo, j->second};
      }
    }
    return result;
  }

  // Splits summands whose condition bounds a parameter to a small range, provided that the update
  // of that parameter is not constant, but becomes constant for every value in the range.
  std::size_t split_ranges()
  {
    std::size_t splits = 0;
    action_summand_vector result;
    for (const action_summand& summand: m_spec.process().action_summands())
    {
      std::vector<action_summand> todo = {summand};
      for (const auto& [i, bounds]: range_bounds(summand.condition()))
      {
        const data::variable& p = m_parameters[i];
        std::vector<action_summand> next;
        for (const action_summand& s: todo)
        {
          const data::data_expression update = next_state_value(s, i);
          if (update == p || data::is_constant(m_rewr(update)))
          {
            next.push_back(s);
            continue;
          }
          std::vector<action_summand> parts;
          bool constant_targets = true;
          for (long long k = bounds.first; k <= bounds.second && constant_targets; ++k)
          {
            std::optional<data::data_expression> value = numeral(p.sort(), k);
            if (!value)
            {
              constant_targets = false;
              break;
            }
            data::mutable_map_substitution<> sigma;
            sigma[p] = *value;
            constant_targets = data::is_constant(m_rewr(update, sigma));
            action_summand part = s;
            part.condition() = data::sort_bool::and_(data::equal_to(p, *value), s.condition());
            parts.push_back(part);
          }
          if (constant_targets)
          {
            next.insert(next.end(), parts.begin(), parts.end());
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
    m_spec.process().action_summands() = result;
    return splits;
  }

  data::data_expression next_state_value(const action_summand& s, std::size_t i) const
  {
    for (const data::assignment& a: s.assignments())
    {
      if (a.lhs() == m_parameters[i])
      {
        return a.rhs();
      }
    }
    return m_parameters[i];
  }

  // Sources from conjuncts p == c, c == p, b and !b, with c a closed term.
  valuation compute_sources(const data::data_expression& cond)
  {
    valuation result;
    for (const data::data_expression& c: data::split_and(cond))
    {
      if (data::is_equal_to_application(c))
      {
        const data::data_expression& left = data::binary_left1(c);
        const data::data_expression& right = data::binary_right1(c);
        std::optional<std::size_t> p = parameter_index(left);
        if (p && data::is_constant(right))
        {
          result[*p] = m_rewr(right);
          continue;
        }
        p = parameter_index(right);
        if (p && data::is_constant(left))
        {
          result[*p] = m_rewr(left);
        }
      }
      else if (std::optional<std::size_t> p = parameter_index(c); p && data::sort_bool::is_bool(c.sort()))
      {
        result[*p] = data::sort_bool::true_();
      }
      else if (data::sort_bool::is_not_application(c))
      {
        std::optional<std::size_t> q = parameter_index(data::sort_bool::arg(c));
        if (q)
        {
          result[*q] = data::sort_bool::false_();
        }
      }
    }
    return result;
  }

  void compute_sources_and_targets()
  {
    const std::size_t n = summand_count();
    m_sources.assign(n, valuation());
    m_targets.assign(n, valuation());
    m_assigned.assign(n, std::set<std::size_t>());
    for (std::size_t j = 0; j < n; ++j)
    {
      m_sources[j] = compute_sources(condition(j));
      if (j >= action_summand_count())
      {
        continue;
      }
      data::mutable_map_substitution<> sigma;
      for (const auto& [i, v]: m_sources[j])
      {
        sigma[m_parameters[i]] = v;
      }
      for (const data::assignment& a: m_spec.process().action_summands()[j].assignments())
      {
        std::optional<std::size_t> i = parameter_index(a.lhs());
        if (!i || a.rhs() == a.lhs())
        {
          continue;
        }
        m_assigned[j].insert(*i);
        const data::data_expression value = m_rewr(a.rhs(), sigma);
        if (data::is_constant(value))
        {
          m_targets[j][*i] = value;
        }
      }
    }
  }

  void compute_trackable_parameters()
  {
    const data::data_expression_list& init = m_spec.initial_process().expressions();
    std::vector<data::data_expression> init_values;
    for (const data::data_expression& e: init)
    {
      init_values.push_back(m_rewr(e));
    }
    m_trackable.assign(m_parameters.size(), false);
    m_values.assign(m_parameters.size(), std::set<data::data_expression>());
    for (std::size_t i = 0; i < m_parameters.size(); ++i)
    {
      bool assigned_somewhere = false;
      bool trackable = data::is_constant(init_values[i]);
      for (std::size_t j = 0; j < summand_count() && trackable; ++j)
      {
        if (m_assigned[j].find(i) != m_assigned[j].end())
        {
          assigned_somewhere = true;
          trackable = m_targets[j].find(i) != m_targets[j].end();
        }
      }
      m_trackable[i] = trackable && assigned_somewhere;
      if (m_trackable[i])
      {
        m_values[i].insert(init_values[i]);
        for (std::size_t j = 0; j < summand_count(); ++j)
        {
          for (const valuation* m: {&m_sources[j], &m_targets[j]})
          {
            auto k = m->find(i);
            if (k != m->end())
            {
              m_values[i].insert(k->second);
            }
          }
        }
      }
    }
  }

  void compute_scopes()
  {
    std::set<scope> scopes;
    for (std::size_t j = 0; j < summand_count(); ++j)
    {
      std::vector<std::size_t> tracked;
      for (const auto& [i, v]: m_sources[j])
      {
        if (m_trackable[i])
        {
          tracked.push_back(i);
        }
      }
      for (std::size_t a = 0; a < tracked.size(); ++a)
      {
        for (std::size_t b = a + 1; b < tracked.size(); ++b)
        {
          scopes.insert({std::min(tracked[a], tracked[b]), std::max(tracked[a], tracked[b])});
        }
      }
    }
    m_scopes.assign(scopes.begin(), scopes.end());
    const data::data_expression_list& init = m_spec.initial_process().expressions();
    std::vector<data::data_expression> init_values(init.begin(), init.end());
    for (const scope& S: m_scopes)
    {
      m_reachable[S] = {{m_rewr(init_values[S.first]), m_rewr(init_values[S.second])}};
      m_scopes_of[S.first].push_back(S);
      m_scopes_of[S.second].push_back(S);
    }
  }

  // A partial valuation is consistent if its restriction to every fully determined scope is reachable.
  bool consistent(const valuation& q) const
  {
    for (const auto& [c, v]: q)
    {
      auto i = m_scopes_of.find(c);
      if (i == m_scopes_of.end())
      {
        continue;
      }
      for (const scope& S: i->second)
      {
        if (S.first != c)
        {
          continue;
        }
        auto w = q.find(S.second);
        if (w != q.end() && !m_reachable.at(S).contains({v, w->second}))
        {
          return false;
        }
      }
    }
    return true;
  }

  valuation tracked_sources(std::size_t j) const
  {
    valuation result;
    for (const auto& [i, v]: m_sources[j])
    {
      if (m_trackable[i])
      {
        result[i] = v;
      }
    }
    return result;
  }

  // The joint least fixpoint over the pair scopes.
  void compute_reachable_pairs()
  {
    bool changed = true;
    while (changed)
    {
      changed = false;
      for (std::size_t j = 0; j < action_summand_count(); ++j)
      {
        const valuation sj = tracked_sources(j);
        if (!consistent(sj))
        {
          continue;
        }
        std::set<scope> touched;
        for (std::size_t i: m_assigned[j])
        {
          auto k = m_scopes_of.find(i);
          if (k != m_scopes_of.end())
          {
            touched.insert(k->second.begin(), k->second.end());
          }
        }
        for (const scope& S: touched)
        {
          const std::vector<value_pair> current(m_reachable[S].begin(), m_reachable[S].end());
          for (const value_pair& p: current)
          {
            valuation q = sj;
            auto agrees = [&](std::size_t c, const data::data_expression& v)
            {
              auto k = q.find(c);
              return k == q.end() || k->second == v;
            };
            if (!agrees(S.first, p.first) || !agrees(S.second, p.second))
            {
              continue;
            }
            q[S.first] = p.first;
            q[S.second] = p.second;
            if (!consistent(q))
            {
              continue;
            }
            auto target = [&](std::size_t c, const data::data_expression& v)
            {
              auto k = m_targets[j].find(c);
              return k == m_targets[j].end() ? v : k->second;
            };
            if (m_reachable[S].insert({target(S.first, p.first), target(S.second, p.second)}).second)
            {
              changed = true;
            }
          }
        }
      }
    }
  }

  // Derives sources from the invariant and marks summands that are never enabled.
  void derive()
  {
    m_dead.assign(summand_count(), false);
    m_derived.assign(summand_count(), valuation());
    bool changed = true;
    while (changed)
    {
      changed = false;
      for (std::size_t j = 0; j < summand_count(); ++j)
      {
        if (m_dead[j])
        {
          continue;
        }
        valuation sj = tracked_sources(j);
        sj.insert(m_derived[j].begin(), m_derived[j].end());
        if (!consistent(sj))
        {
          m_dead[j] = true;
          changed = true;
          continue;
        }
        for (const auto& [c, scopes]: m_scopes_of)
        {
          if (sj.find(c) != sj.end())
          {
            continue;
          }
          std::vector<data::data_expression> allowed;
          for (const data::data_expression& x: m_values[c])
          {
            valuation q = sj;
            q[c] = x;
            if (consistent(q))
            {
              allowed.push_back(x);
            }
          }
          if (allowed.empty())
          {
            m_dead[j] = true;
            changed = true;
            break;
          }
          if (allowed.size() == 1)
          {
            m_derived[j][c] = allowed.front();
            sj[c] = allowed.front();
            changed = true;
          }
        }
      }
    }
  }

  data::data_expression strengthen(std::size_t j, const data::data_expression& cond) const
  {
    data::data_expression result = cond;
    for (const auto& [i, v]: m_derived[j])
    {
      result = data::sort_bool::and_(data::equal_to(m_parameters[i], v), result);
    }
    return result;
  }

  void write_result()
  {
    action_summand_vector action_summands;
    for (std::size_t j = 0; j < action_summand_count(); ++j)
    {
      if (!m_dead[j])
      {
        action_summand s = m_spec.process().action_summands()[j];
        s.condition() = strengthen(j, s.condition());
        action_summands.push_back(s);
      }
    }
    deadlock_summand_vector deadlock_summands;
    for (std::size_t j = action_summand_count(); j < summand_count(); ++j)
    {
      if (!m_dead[j])
      {
        deadlock_summand s = m_spec.process().deadlock_summands()[j - action_summand_count()];
        s.condition() = strengthen(j, s.condition());
        deadlock_summands.push_back(s);
      }
    }
    m_spec.process().action_summands() = action_summands;
    m_spec.process().deadlock_summands() = deadlock_summands;
  }

public:
  control_invariant_algorithm(specification& spec, const data::rewriter& rewr, const control_invariant_options& options)
    : m_spec(spec),
      m_rewr(rewr),
      m_options(options)
  {}

  void run()
  {
    lps::detail::instantiate_global_variables(m_spec);
    const data::variable_list& parameters = m_spec.process().process_parameters();
    m_parameters.assign(parameters.begin(), parameters.end());

    const std::size_t splits = split_ranges();
    compute_sources_and_targets();
    compute_trackable_parameters();
    compute_scopes();
    compute_reachable_pairs();
    derive();

    std::size_t reachable_pairs = 0;
    for (const auto& [S, pairs]: m_reachable)
    {
      reachable_pairs += pairs.size();
    }
    const std::size_t trackable = std::count(m_trackable.begin(), m_trackable.end(), true);
    const std::size_t dead = std::count(m_dead.begin(), m_dead.end(), true);
    std::size_t derived = 0;
    for (std::size_t j = 0; j < summand_count(); ++j)
    {
      if (!m_dead[j])
      {
        derived += m_derived[j].size();
      }
    }
    mCRL2log(log::log_level_t::verbose) << "control invariant: " << splits << " summands split, " << summand_count()
                                        << " summands, " << trackable << " trackable parameters, " << m_scopes.size()
                                        << " pair scopes with " << reachable_pairs << " reachable pairs, " << derived
                                        << " derived sources, " << dead << " summands removed" << std::endl;
    write_result();
  }
};

} // namespace detail

/// \brief Strengthens the conditions of an LPS with a pairwise invariant over its trackable parameters,
/// and removes summands that are never enabled in a reachable state. Global variables are instantiated.
/// The result is strongly bisimilar to the input.
inline void control_invariant(specification& spec,
  const data::rewriter& rewr,
  const control_invariant_options& options = control_invariant_options())
{
  detail::control_invariant_algorithm(spec, rewr, options).run();
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_CONTROL_INVARIANT_H
