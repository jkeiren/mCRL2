// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/detail/control_invariant_analysis.h
/// \brief Computes a pairwise invariant over the trackable parameters of an LPS.
///
/// A parameter is *trackable* if every summand either leaves it unchanged or assigns it a value that
/// is constant once the parameter values fixed by the condition (the *sources*) are substituted.
/// For pairs of trackable parameters that are both fixed by the condition of some summand (the
/// *scopes*), the set of reachable value pairs is over-approximated by a joint least fixpoint, in
/// which the condition of a summand on parameters outside the pair is checked against the other
/// pairs. From the resulting invariant, additional sources are derived for each summand, and
/// summands that are never enabled in a reachable state are marked as dead.

#ifndef MCRL2_LPS_DETAIL_CONTROL_INVARIANT_ANALYSIS_H
#define MCRL2_LPS_DETAIL_CONTROL_INVARIANT_ANALYSIS_H

#include "mcrl2/data/join.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
#include "mcrl2/lps/specification.h"

#include <algorithm>
#include <cassert>
#include <map>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

namespace mcrl2::lps::detail
{

/// \brief Computes a pairwise invariant over the trackable parameters of an LPS, the sources it
/// implies for each summand, and the summands that are never enabled in a reachable state.
/// Summands are numbered with the action summands first, followed by the deadlock summands.
/// Parameters are identified by their index in the process parameters.
class control_invariant_analysis
{
public:
  using value_pair = std::pair<data::data_expression, data::data_expression>;
  using scope = std::pair<std::size_t, std::size_t>;
  using valuation = std::map<std::size_t, data::data_expression>;

protected:
  const specification& m_spec;
  data::rewriter m_rewr;
  std::vector<data::variable> m_parameters;

  // Per summand.
  std::vector<valuation> m_sources;
  std::vector<valuation> m_targets;
  std::vector<std::set<std::size_t>> m_assigned;
  std::vector<bool> m_dead;
  std::vector<valuation> m_derived;

  // Per parameter.
  std::vector<data::data_expression> m_init_values;
  std::vector<bool> m_trackable;
  std::vector<bool> m_control_flow;
  std::vector<std::set<data::data_expression>> m_values;

  std::vector<scope> m_scopes;
  std::map<scope, std::set<value_pair>> m_reachable;
  std::map<std::size_t, std::vector<scope>> m_scopes_of;

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
    m_init_values.clear();
    for (const data::data_expression& e: m_spec.initial_process().expressions())
    {
      m_init_values.push_back(m_rewr(e));
    }
    const std::vector<data::data_expression>& init_values = m_init_values;
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
    for (const scope& S: m_scopes)
    {
      m_reachable[S] = {{m_init_values[S.first], m_init_values[S.second]}};
      m_scopes_of[S.first].push_back(S);
      m_scopes_of[S.second].push_back(S);
    }
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

  // A trackable parameter is a control flow parameter if every summand that is not dead and that
  // changes it has a (possibly derived) source for it. Its target is then defined as well.
  void compute_control_flow_parameters()
  {
    m_control_flow.assign(m_parameters.size(), false);
    for (std::size_t i = 0; i < m_parameters.size(); ++i)
    {
      if (!m_trackable[i])
      {
        continue;
      }
      bool control_flow = true;
      for (std::size_t j = 0; j < action_summand_count() && control_flow; ++j)
      {
        if (!m_dead[j] && m_assigned[j].find(i) != m_assigned[j].end())
        {
          const valuation sj = effective_sources(j);
          control_flow = sj.find(i) != sj.end();
        }
      }
      m_control_flow[i] = control_flow;
    }
  }

public:
  /// \brief A control flow graph on the valuations of a scope (a set of control flow parameters).
  /// It has an edge (u, j, v) if summand j is applicable at vertex u and leads to v.
  struct scoped_graph
  {
    std::vector<std::size_t> scope;
    std::vector<valuation> vertices;
    std::map<valuation, std::size_t> index;
    std::vector<std::tuple<std::size_t, std::size_t, std::size_t>> edges;
  };

  /// \brief Constructor. The global variables of spec must have been instantiated.
  control_invariant_analysis(const specification& spec, const data::rewriter& rewr)
    : m_spec(spec),
      m_rewr(rewr)
  {}

  /// \brief Computes the invariant, the derived sources and the dead summands.
  void run()
  {
    const data::variable_list& parameters = m_spec.process().process_parameters();
    m_parameters.assign(parameters.begin(), parameters.end());
    compute_sources_and_targets();
    compute_trackable_parameters();
    compute_scopes();
    compute_reachable_pairs();
    derive();
    compute_control_flow_parameters();
  }

  std::size_t action_summand_count() const
  {
    return m_spec.process().action_summands().size();
  }

  std::size_t summand_count() const
  {
    return action_summand_count() + m_spec.process().deadlock_summands().size();
  }

  const std::vector<data::variable>& parameters() const
  {
    return m_parameters;
  }

  /// \brief The values of the parameters fixed by the condition of summand j.
  const valuation& sources(std::size_t j) const
  {
    return m_sources[j];
  }

  /// \brief The constant values assigned by summand j, given its sources.
  const valuation& targets(std::size_t j) const
  {
    return m_targets[j];
  }

  /// \brief The parameters that summand j assigns a value different from the parameter itself.
  const std::set<std::size_t>& assigned(std::size_t j) const
  {
    return m_assigned[j];
  }

  bool trackable(std::size_t i) const
  {
    return m_trackable[i];
  }

  /// \brief The initial value, the sources and the targets of a trackable parameter.
  const std::set<data::data_expression>& values(std::size_t i) const
  {
    return m_values[i];
  }

  const std::vector<scope>& scopes() const
  {
    return m_scopes;
  }

  /// \brief The reachable value pairs of a scope.
  const std::set<value_pair>& reachable(const scope& S) const
  {
    return m_reachable.at(S);
  }

  /// \brief Returns true if summand j is never enabled in a reachable state.
  bool dead(std::size_t j) const
  {
    return m_dead[j];
  }

  /// \brief The sources of summand j that follow from the invariant but not from its condition.
  const valuation& derived(std::size_t j) const
  {
    return m_derived[j];
  }

  /// \brief Returns true if parameter i is a control flow parameter: it is trackable, and every
  /// summand that is not dead and changes it has a (possibly derived) source for it.
  bool control_flow(std::size_t i) const
  {
    return m_control_flow[i];
  }

  /// \brief The initial value of parameter i, rewritten.
  const data::data_expression& initial_value(std::size_t i) const
  {
    return m_init_values[i];
  }

  /// \brief The sources of the trackable parameters in summand j, including the derived ones.
  valuation effective_sources(std::size_t j) const
  {
    valuation result = tracked_sources(j);
    result.insert(m_derived[j].begin(), m_derived[j].end());
    return result;
  }

  /// \brief Returns true if summand j is not dead, its sources agree with the valuation p of
  /// (some) control flow parameters, and the combination is consistent with the invariant.
  bool applicable(std::size_t j, const valuation& p) const
  {
    if (m_dead[j])
    {
      return false;
    }
    valuation q = effective_sources(j);
    for (const auto& [c, v]: p)
    {
      auto k = q.find(c);
      if (k != q.end() && k->second != v)
      {
        return false;
      }
      q[c] = v;
    }
    return consistent(q);
  }

  /// \brief Computes the control flow graph of the scope S, whose elements must be control flow
  /// parameters, by exploring the valuations of S reachable from the initial state via applicable
  /// action summands. The empty scope yields a graph with a single vertex.
  scoped_graph compute_scoped_graph(const std::vector<std::size_t>& S) const
  {
    scoped_graph G;
    G.scope = S;
    valuation init;
    for (std::size_t c: S)
    {
      assert(m_control_flow[c]);
      init[c] = m_init_values[c];
    }
    G.vertices.push_back(init);
    G.index[init] = 0;
    for (std::size_t u = 0; u < G.vertices.size(); ++u)
    {
      for (std::size_t j = 0; j < action_summand_count(); ++j)
      {
        // G.vertices may grow in this loop, so copy the vertex.
        const valuation p = G.vertices[u];
        if (!applicable(j, p))
        {
          continue;
        }
        valuation w = p;
        for (std::size_t c: S)
        {
          auto k = m_targets[j].find(c);
          if (k != m_targets[j].end())
          {
            w[c] = k->second;
          }
        }
        auto [i, inserted] = G.index.insert({w, G.vertices.size()});
        if (inserted)
        {
          G.vertices.push_back(w);
        }
        G.edges.emplace_back(u, j, i->second);
      }
    }
    return G;
  }

  /// \brief A partial valuation is consistent if its restriction to every fully determined scope is
  /// reachable.
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
};

} // namespace mcrl2::lps::detail

#endif // MCRL2_LPS_DETAIL_CONTROL_INVARIANT_ANALYSIS_H
