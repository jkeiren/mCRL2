// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/scoped_stategraph.h
/// \brief Resets data parameters of an LPS that are dead, using liveness on scoped control flow graphs.
///
/// A scope is a set of control flow parameters. For every scope in a family, the control flow
/// graph on the valuations of the scope is computed (control_invariant_analysis::compute_scoped_graph).
/// It has an edge for every summand that is applicable at a vertex, so it is a sound abstraction of
/// the reachable control flow, and the live data parameters are labelled on it by a backward
/// liveness analysis. A data parameter is reset to its initial value in a summand if some scope
/// labels it dead at the target of the summand; if this depends on the source state, the reset is
/// conditional on the values of the control flow parameters. The empty scope is always included; it
/// resets parameters that are never used again.
///
/// Optionally (use_belongs), a data parameter is only labelled in the scopes it belongs to, and only a
/// scope that rules a summand can justify a reset in it, as in the local stategraph algorithm (Keiren,
/// Wesselink and Willemse, ATVA 2014, Defs. 15-16) with control flow parameters replaced by scopes.
/// With singleton scopes this is the local algorithm. Without this restriction the analysis is at least
/// as precise, and more precise for larger scopes.
///
/// The invariant (control_invariant_analysis) that decides which summands are applicable reads the
/// parameters in its scopes. Resetting such a parameter could enable a summand that the invariant
/// rules out. The invariant is therefore made explicit, as in control_invariant: the derived sources
/// of control flow parameters are conjoined to the conditions and dead summands are removed. The
/// parameters of the invariant are significant in the condition of every summand whose sources agree
/// with the vertex, whether or not the invariant allows it there. The result is strongly bisimilar to
/// the input. Global variables are instantiated.

#ifndef MCRL2_LPS_SCOPED_STATEGRAPH_H
#define MCRL2_LPS_SCOPED_STATEGRAPH_H

#include "mcrl2/data/standard_utility.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"
#include "mcrl2/lps/control_invariant.h"
#include "mcrl2/lps/find.h"

#include <algorithm>
#include <set>
#include <vector>

namespace mcrl2::lps
{

/// \brief The family of scopes on which liveness is computed.
enum class liveness_scopes
{
  single, ///< one scope per control flow parameter (the local stategraph algorithm)
  pairs, ///< the pairs of control flow parameters that are both fixed by a summand, and all single parameters
  global ///< one scope with all control flow parameters (the global stategraph algorithm)
};

namespace detail
{

class scoped_stategraph_algorithm
{
protected:
  using analysis_type = control_invariant_analysis;
  using valuation = analysis_type::valuation;
  using scoped_graph = analysis_type::scoped_graph;

  struct scope_info
  {
    scoped_graph graph;
    std::set<std::size_t> belongs;
    std::vector<std::set<std::size_t>> label; // per vertex
    std::vector<std::vector<std::pair<std::size_t, std::size_t>>> edges_of; // per summand: (source, target)
  };

  specification& m_spec;
  data::rewriter m_rewr;
  liveness_scopes m_scopes;
  bool m_use_belongs;

  std::vector<data::variable> m_parameters;
  std::vector<bool> m_data;
  std::vector<std::set<std::size_t>> m_used_for; // per summand
  std::vector<std::set<std::size_t>> m_used_in; // per summand
  std::vector<std::set<std::size_t>> m_changed; // per summand
  std::vector<std::vector<std::set<std::size_t>>> m_fv_update; // per action summand, per parameter
  std::set<std::size_t> m_in_invariant; // the parameters that occur in a scope of the invariant
  std::vector<scope_info> m_infos;

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

  std::set<std::size_t> data_parameters_in(const std::set<data::variable>& variables) const
  {
    std::set<std::size_t> result;
    for (std::size_t i = 0; i < m_parameters.size(); ++i)
    {
      if (m_data[i] && variables.find(m_parameters[i]) != variables.end())
      {
        result.insert(i);
      }
    }
    return result;
  }

  data::data_expression next_state_value(const action_summand& s, std::size_t l) const
  {
    for (const data::assignment& a: s.assignments())
    {
      if (a.lhs() == m_parameters[l])
      {
        return a.rhs();
      }
    }
    return m_parameters[l];
  }

  // Used for, used in and changed by (ATVA 2014, Def. 14), for data parameters.
  void compute_uses()
  {
    m_used_for.assign(summand_count(), {});
    m_used_in.assign(summand_count(), {});
    m_changed.assign(summand_count(), {});
    m_fv_update.assign(action_summand_count(), {});
    for (std::size_t j = 0; j < summand_count(); ++j)
    {
      m_used_for[j] = data_parameters_in(data::find_free_variables(condition(j)));
      if (j >= action_summand_count())
      {
        continue;
      }
      const action_summand& s = m_spec.process().action_summands()[j];
      for (std::size_t d: data_parameters_in(lps::find_free_variables(s.multi_action())))
      {
        m_used_for[j].insert(d);
      }
      m_fv_update[j].assign(m_parameters.size(), {});
      for (std::size_t l = 0; l < m_parameters.size(); ++l)
      {
        const data::data_expression rhs = next_state_value(s, l);
        m_fv_update[j][l] = data_parameters_in(data::find_free_variables(rhs));
        if (rhs != m_parameters[l] && m_data[l])
        {
          m_changed[j].insert(l);
        }
        for (std::size_t d: m_fv_update[j][l])
        {
          if (d != l)
          {
            m_used_in[j].insert(d);
          }
        }
      }
    }
  }

  std::vector<std::vector<std::size_t>> scope_family(const analysis_type& analysis) const
  {
    std::vector<std::size_t> cfps;
    for (std::size_t i = 0; i < m_parameters.size(); ++i)
    {
      if (analysis.control_flow(i))
      {
        cfps.push_back(i);
      }
    }
    std::vector<std::vector<std::size_t>> result = {{}};
    if (m_scopes == liveness_scopes::global)
    {
      if (!cfps.empty())
      {
        result.push_back(cfps);
      }
      return result;
    }
    for (std::size_t c: cfps)
    {
      result.push_back({c});
    }
    if (m_scopes == liveness_scopes::pairs)
    {
      for (const analysis_type::scope& S: analysis.scopes())
      {
        if (analysis.control_flow(S.first) && analysis.control_flow(S.second))
        {
          result.push_back({S.first, S.second});
        }
      }
    }
    return result;
  }

  static bool rules(const analysis_type& analysis, const std::vector<std::size_t>& S, std::size_t j)
  {
    if (analysis.dead(j))
    {
      return false;
    }
    const valuation sources = analysis.effective_sources(j);
    return std::all_of(S.begin(), S.end(), [&](std::size_t c) { return sources.find(c) != sources.end(); });
  }

  // Without use_belongs, every data parameter belongs to every scope.
  std::set<std::size_t> compute_belongs(const analysis_type& analysis, const std::vector<std::size_t>& S) const
  {
    std::set<std::size_t> result;
    for (std::size_t d = 0; d < m_parameters.size(); ++d)
    {
      if (!m_data[d])
      {
        continue;
      }
      if (!m_use_belongs)
      {
        result.insert(d);
        continue;
      }
      bool belongs = true;
      for (std::size_t j = 0; j < summand_count() && belongs; ++j)
      {
        if (analysis.dead(j))
        {
          continue;
        }
        const bool involved = m_used_for[j].find(d) != m_used_for[j].end() || m_used_in[j].find(d) != m_used_in[j].end()
                              || m_changed[j].find(d) != m_changed[j].end();
        belongs = !involved || rules(analysis, S, j);
      }
      if (belongs)
      {
        result.insert(d);
      }
    }
    return result;
  }

  // The significant data parameters of summand j at vertex p: those in its condition simplified with
  // the values of the scope, and those in its actions.
  std::set<std::size_t> significant(std::size_t j, const valuation& p) const
  {
    std::set<std::size_t> result = in_condition(j, p);
    if (j < action_summand_count())
    {
      for (std::size_t d:
        data_parameters_in(lps::find_free_variables(m_spec.process().action_summands()[j].multi_action())))
      {
        result.insert(d);
      }
    }
    return result;
  }

  // The data parameters in the condition of summand j simplified with the values of the scope.
  std::set<std::size_t> in_condition(std::size_t j, const valuation& p) const
  {
    data::mutable_map_substitution<> sigma;
    for (const auto& [c, v]: p)
    {
      sigma[m_parameters[c]] = v;
    }
    return data_parameters_in(data::find_free_variables(m_rewr(condition(j), sigma)));
  }

  // Returns true if summand j is not dead and its sources, including the derived ones, agree with
  // the valuation p of control flow parameters. The derived sources of control flow parameters are
  // conjuncts of the strengthened condition.
  static bool sources_agree(const analysis_type& analysis, std::size_t j, const valuation& p)
  {
    if (analysis.dead(j))
    {
      return false;
    }
    const valuation& sources = analysis.sources(j);
    const valuation& derived = analysis.derived(j);
    return std::all_of(p.begin(),
      p.end(),
      [&](const std::pair<const std::size_t, data::data_expression>& cv)
      {
        auto k = sources.find(cv.first);
        if (k != sources.end())
        {
          return k->second == cv.second;
        }
        k = derived.find(cv.first);
        return k == derived.end() || k->second == cv.second;
      });
  }

  // A data parameter that occurs in a scope of the invariant may be read by a summand that the
  // invariant rules out at a vertex. Resetting it could enable that summand, so it is significant in
  // the condition of every summand whose sources agree with the vertex, ignoring the invariant. This
  // relies on the strengthened conditions and the removal of dead summands (run).
  void initialise_labels(const analysis_type& analysis, scope_info& info) const
  {
    info.label.assign(info.graph.vertices.size(), {});
    for (std::size_t u = 0; u < info.graph.vertices.size(); ++u)
    {
      const valuation& p = info.graph.vertices[u];
      for (std::size_t j = 0; j < summand_count(); ++j)
      {
        std::set<std::size_t> significant_j;
        if (analysis.applicable(j, p))
        {
          significant_j = significant(j, p);
        }
        else if (sources_agree(analysis, j, p))
        {
          for (std::size_t d: in_condition(j, p))
          {
            if (m_in_invariant.find(d) != m_in_invariant.end())
            {
              significant_j.insert(d);
            }
          }
        }
        for (std::size_t d: significant_j)
        {
          if (info.belongs.find(d) != info.belongs.end())
          {
            info.label[u].insert(d);
          }
        }
      }
    }
  }

  // Returns true if data parameter l is live after summand j in some scope that l belongs to.
  bool live_after(std::size_t j, std::size_t l) const
  {
    for (const scope_info& info: m_infos)
    {
      if (info.belongs.find(l) == info.belongs.end())
      {
        continue;
      }
      for (const auto& [u, w]: info.edges_of[j])
      {
        if (info.label[w].find(l) != info.label[w].end())
        {
          return true;
        }
      }
    }
    return false;
  }

  // The scoped labelling (ATVA 2014, Def. 16, with scopes instead of control flow parameters).
  void compute_labels()
  {
    bool changed = true;
    while (changed)
    {
      changed = false;
      for (scope_info& info: m_infos)
      {
        for (const auto& [u, j, w]: info.graph.edges)
        {
          for (std::size_t l = 0; l < m_parameters.size(); ++l)
          {
            if (!m_data[l])
            {
              continue;
            }
            const bool internal
              = info.belongs.find(l) != info.belongs.end() && info.label[w].find(l) != info.label[w].end();
            const bool external = info.belongs.find(l) == info.belongs.end() && live_after(j, l);
            if (!internal && !external)
            {
              continue;
            }
            for (std::size_t d: m_fv_update[j][l])
            {
              if (info.belongs.find(d) != info.belongs.end() && info.label[u].insert(d).second)
              {
                changed = true;
              }
            }
          }
        }
      }
    }
  }

  // The condition that the control flow parameters have the values of p.
  data::data_expression matches(const valuation& p) const
  {
    std::vector<data::data_expression> conjuncts;
    for (const auto& [c, v]: p)
    {
      conjuncts.push_back(data::equal_to(m_parameters[c], v));
    }
    return data::lazy::join_and(conjuncts.begin(), conjuncts.end());
  }

  // The condition on the source state under which data parameter d is dead after summand j: some
  // scope that owns d (and, with use_belongs, rules j) labels d dead at the target of the edge of j
  // from the projection of the source state. On reachable states, the projection of the source
  // state is the source of an edge of j in every scope. Without use_belongs the reset is therefore a
  // function of the target state.
  data::data_expression reset_condition(const analysis_type& analysis, std::size_t j, std::size_t d) const
  {
    std::vector<data::data_expression> disjuncts;
    for (const scope_info& info: m_infos)
    {
      if (info.belongs.find(d) == info.belongs.end() || (m_use_belongs && !rules(analysis, info.graph.scope, j))
          || info.edges_of[j].empty())
      {
        continue;
      }
      std::vector<data::data_expression> dead;
      std::vector<data::data_expression> live;
      for (const auto& [u, w]: info.edges_of[j])
      {
        const bool is_dead = info.label[w].find(d) == info.label[w].end();
        (is_dead ? dead : live).push_back(matches(info.graph.vertices[u]));
      }
      if (dead.empty())
      {
        continue;
      }
      if (live.empty())
      {
        return data::sort_bool::true_();
      }
      if (dead.size() <= live.size())
      {
        disjuncts.push_back(data::lazy::join_or(dead.begin(), dead.end()));
      }
      else
      {
        disjuncts.push_back(data::lazy::not_(data::lazy::join_or(live.begin(), live.end())));
      }
    }
    return data::lazy::join_or(disjuncts.begin(), disjuncts.end());
  }

  // Resets dead data parameters; returns the number of unconditional and of conditional resets.
  std::pair<std::size_t, std::size_t> reset(const analysis_type& analysis)
  {
    std::size_t unconditional = 0;
    std::size_t conditional = 0;
    for (std::size_t j = 0; j < action_summand_count(); ++j)
    {
      if (analysis.dead(j))
      {
        continue;
      }
      action_summand& s = m_spec.process().action_summands()[j];
      std::vector<data::assignment> assignments;
      for (std::size_t l = 0; l < m_parameters.size(); ++l)
      {
        data::data_expression rhs = next_state_value(s, l);
        if (m_data[l] && rhs != analysis.initial_value(l))
        {
          const data::data_expression condition = reset_condition(analysis, j, l);
          if (data::sort_bool::is_true_function_symbol(condition))
          {
            rhs = analysis.initial_value(l);
            ++unconditional;
          }
          else if (!data::sort_bool::is_false_function_symbol(condition))
          {
            rhs = data::if_(condition, analysis.initial_value(l), rhs);
            ++conditional;
          }
        }
        if (rhs != m_parameters[l])
        {
          assignments.emplace_back(m_parameters[l], rhs);
        }
      }
      s.assignments() = data::assignment_list(assignments.begin(), assignments.end());
    }
    return {unconditional, conditional};
  }

public:
  scoped_stategraph_algorithm(specification& spec, const data::rewriter& rewr, liveness_scopes scopes, bool use_belongs)
    : m_spec(spec),
      m_rewr(rewr),
      m_scopes(scopes),
      m_use_belongs(use_belongs)
  {}

  void run()
  {
    lps::detail::instantiate_global_variables(m_spec);
    analysis_type analysis(m_spec, m_rewr);
    analysis.run();
    // Make the invariant explicit, so that the relaxed significance of the parameters of the invariant
    // (initialise_labels) can rely on it: the derived sources of control flow parameters become
    // conjuncts of the conditions, and the dead summands are removed at the end. Derived sources of
    // data parameters are not needed, and would make those parameters live.
    strengthen_conditions(m_spec, analysis, true);

    const data::variable_list& parameters = m_spec.process().process_parameters();
    m_parameters.assign(parameters.begin(), parameters.end());
    m_data.assign(m_parameters.size(), false);
    for (std::size_t i = 0; i < m_parameters.size(); ++i)
    {
      m_data[i] = !analysis.control_flow(i);
    }
    compute_uses();
    for (const analysis_type::scope& S: analysis.scopes())
    {
      m_in_invariant.insert(S.first);
      m_in_invariant.insert(S.second);
    }

    std::size_t vertices = 0;
    std::size_t edges = 0;
    for (const std::vector<std::size_t>& S: scope_family(analysis))
    {
      scope_info info;
      info.graph = analysis.compute_scoped_graph(S);
      info.belongs = compute_belongs(analysis, S);
      info.edges_of.assign(action_summand_count(), {});
      for (const auto& [u, j, w]: info.graph.edges)
      {
        info.edges_of[j].emplace_back(u, w);
      }
      initialise_labels(analysis, info);
      vertices += info.graph.vertices.size();
      edges += info.graph.edges.size();
      m_infos.push_back(std::move(info));
    }
    compute_labels();
    const auto [unconditional, conditional] = reset(analysis);
    remove_dead_summands(m_spec, analysis);
    mCRL2log(log::log_level_t::verbose) << "scoped stategraph: " << m_infos.size() << " scopes with " << vertices
                                        << " vertices and " << edges << " edges, " << unconditional << " resets, "
                                        << conditional << " conditional resets" << std::endl;
  }
};

} // namespace detail

/// \brief Resets dead data parameters of an LPS using liveness on scoped control flow graphs.
/// \param use_belongs If true, a data parameter is only labelled in the scopes it belongs to, as in
/// the local stategraph algorithm.
/// Global variables are instantiated. The result is strongly bisimilar to the input.
inline void
scoped_stategraph(specification& spec, const data::rewriter& rewr, liveness_scopes scopes, bool use_belongs = false)
{
  detail::scoped_stategraph_algorithm(spec, rewr, scopes, use_belongs).run();
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_SCOPED_STATEGRAPH_H
