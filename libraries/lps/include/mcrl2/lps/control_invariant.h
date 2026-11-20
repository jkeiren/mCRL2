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
/// The invariant is computed by control_invariant_analysis (mcrl2/lps/detail/control_invariant_analysis.h).
/// The sources it derives for each summand are conjoined to the conditions, and summands that are
/// never enabled in a reachable state are removed. The result is strongly bisimilar to the input
/// (strengthening with an inductive invariant that holds initially).
///
/// Counters that are updated under a range condition (`0 < a && a < 3 -> a := a + 1`) are only
/// trackable after splitting such summands with split_ranges (mcrl2/lps/split_ranges.h).

#ifndef MCRL2_LPS_CONTROL_INVARIANT_H
#define MCRL2_LPS_CONTROL_INVARIANT_H

#include "mcrl2/lps/detail/control_invariant_analysis.h"
#include "mcrl2/lps/detail/instantiate_global_variables.h"

namespace mcrl2::lps
{

namespace detail
{

inline data::data_expression
strengthen(const control_invariant_analysis& analysis, std::size_t j, const data::data_expression& cond)
{
  data::data_expression result = cond;
  for (const auto& [i, v]: analysis.derived(j))
  {
    result = data::sort_bool::and_(data::equal_to(analysis.parameters()[i], v), result);
  }
  return result;
}

/// \brief Conjoins the derived sources of every summand that is not dead to its condition.
/// The analysis must have been computed on spec; it remains valid, since it does not read the
/// conditions after it has run.
inline void strengthen_conditions(specification& spec, const control_invariant_analysis& analysis)
{
  const std::size_t n_action = analysis.action_summand_count();
  for (std::size_t j = 0; j < analysis.summand_count(); ++j)
  {
    if (analysis.dead(j))
    {
      continue;
    }
    if (j < n_action)
    {
      action_summand& s = spec.process().action_summands()[j];
      s.condition() = strengthen(analysis, j, s.condition());
    }
    else
    {
      deadlock_summand& s = spec.process().deadlock_summands()[j - n_action];
      s.condition() = strengthen(analysis, j, s.condition());
    }
  }
}

/// \brief Removes the dead summands of spec. Afterwards the analysis no longer matches spec.
inline void remove_dead_summands(specification& spec, const control_invariant_analysis& analysis)
{
  const std::size_t n_action = analysis.action_summand_count();
  action_summand_vector action_summands;
  for (std::size_t j = 0; j < n_action; ++j)
  {
    if (!analysis.dead(j))
    {
      action_summands.push_back(spec.process().action_summands()[j]);
    }
  }
  deadlock_summand_vector deadlock_summands;
  for (std::size_t j = n_action; j < analysis.summand_count(); ++j)
  {
    if (!analysis.dead(j))
    {
      deadlock_summands.push_back(spec.process().deadlock_summands()[j - n_action]);
    }
  }
  spec.process().action_summands() = action_summands;
  spec.process().deadlock_summands() = deadlock_summands;
}

class control_invariant_algorithm
{
protected:
  specification& m_spec;
  data::rewriter m_rewr;

  static void log_statistics(const control_invariant_analysis& analysis)
  {
    std::size_t reachable_pairs = 0;
    for (const control_invariant_analysis::scope& S: analysis.scopes())
    {
      reachable_pairs += analysis.reachable(S).size();
    }
    std::size_t trackable = 0;
    for (std::size_t i = 0; i < analysis.parameters().size(); ++i)
    {
      trackable += analysis.trackable(i) ? 1 : 0;
    }
    std::size_t dead = 0;
    std::size_t derived = 0;
    for (std::size_t j = 0; j < analysis.summand_count(); ++j)
    {
      if (analysis.dead(j))
      {
        ++dead;
      }
      else
      {
        derived += analysis.derived(j).size();
      }
    }
    mCRL2log(log::log_level_t::verbose) << "control invariant: " << analysis.summand_count() << " summands, "
                                        << trackable << " trackable parameters, " << analysis.scopes().size()
                                        << " pair scopes with " << reachable_pairs << " reachable pairs, " << derived
                                        << " derived sources, " << dead << " summands removed" << std::endl;
  }

public:
  control_invariant_algorithm(specification& spec, const data::rewriter& rewr)
    : m_spec(spec),
      m_rewr(rewr)
  {}

  void run()
  {
    lps::detail::instantiate_global_variables(m_spec);
    control_invariant_analysis analysis(m_spec, m_rewr);
    analysis.run();
    log_statistics(analysis);
    strengthen_conditions(m_spec, analysis);
    remove_dead_summands(m_spec, analysis);
  }
};

} // namespace detail

/// \brief Strengthens the conditions of an LPS with a pairwise invariant over its trackable parameters,
/// and removes summands that are never enabled in a reachable state. Global variables are instantiated.
/// The result is strongly bisimilar to the input.
inline void control_invariant(specification& spec, const data::rewriter& rewr)
{
  detail::control_invariant_algorithm(spec, rewr).run();
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_CONTROL_INVARIANT_H
