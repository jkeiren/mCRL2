// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/linearise_new.h
/// \brief Linearisation of process specifications

#ifndef MCRL2_LPS_LINEARISE_NEW_H
#define MCRL2_LPS_LINEARISE_NEW_H

#include "mcrl2/core/identifier_string.h"
#include "mcrl2/data/optimized_boolean_operators.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/lps/action_summand.h"
#include "mcrl2/lps/linearise_allow_block.h"
#include "mcrl2/lps/linearise_communication.h"
#include "mcrl2/lps/linear_process.h"
#include "mcrl2/lps/linearise_utility.h"
#include "mcrl2/lps/multi_action.h"
#include "mcrl2/lps/process_initializer.h"
#include "mcrl2/process/action_name_multiset.h"
#include "mcrl2/process/allow_set.h"
#include "mcrl2/process/communication_expression.h"
#include "mcrl2/utilities/views.h"
#include <algorithm>
#include <iterator>
#include <ranges>

namespace mcrl2::lps
{

namespace detail
{
  /// \brief Merges two multi-actions by concatenation and sorting the resulting actions.
  /// \param a1 A multi-action
  /// \param a2 A multi-action
  /// \pre a1.time() == a2.time()
  /// \post actions in the result are sorted.
  inline
  multi_action merge_multi_actions(const multi_action& a1, const multi_action& a2)
  {
    assert(a1.time() == a2.time());
    multi_action result = multi_action(sort_actions(a1.actions() + a2.actions()), a1.time());
    assert(std::is_sorted(result.actions().begin(), result.actions().end(), action_compare()));
    return result;
  }

  /// \brief Extract the names of all the variables in vars.
  inline
  std::set<core::identifier_string> variable_names(const data::variable_list& vars)
  {
    std::set<core::identifier_string> result;
    std::for_each(vars.begin(), vars.end(), [&result](const data::variable& v)
    {
      result.emplace(v.name());
    });
    return result;
  }

  /// \brief Extract the multiaction name from a multiaction.
  inline
  process::multi_action_name multi_action_name(const multi_action& ma)
  {
    std::ranges::transform_view names(ma.actions(), [](const process::action& a) { return a.label().name(); });
    return process::multi_action_name(names.begin(), names.end());
  }

  /// \brief Predicate to check if all multiactions in the summand are sorted.
  inline
  bool multi_actions_are_sorted(const lps::action_summand& as)
  {
    return std::is_sorted(as.multi_action().actions().begin(), as.multi_action().actions().end(), action_compare());
  }

  /// \brief Predicate to check if all multiactions in the lpe are sorted.
  inline
  bool multi_actions_are_sorted(const lps::linear_process& lpe)
  {
    return std::all_of(
      lpe.action_summands().begin(),
      lpe.action_summands().end(),
      [](const lps::action_summand& as){ return detail::multi_actions_are_sorted(as); });
  }
}

/// \brief Structure with an LPE and all related relevant information used
/// during linearisation.
struct linearise_lpe
{
  /// LPE
  linear_process lpe;
  /// Initialization of the LPE.
  process_initializer initial_process;

  linearise_lpe() = default;
  linearise_lpe(const linear_process& lpe, const process_initializer& initial_process)
    : lpe(lpe),
      initial_process(initial_process)
  {}
};

//TODO: this currently is a naive wrapper around the computation of communication,
// this needs to be improved.
inline
void apply_communication(const process::communication_expression_list& C, linearise_lpe& lpe)
{
  process::action_name_multiset_list allowlist;
  bool is_allow = false;
  bool is_block = false;
  process::action termination_action;
  bool nosumelm = false;
  bool nodeltaelimination = false;
  bool ignore_time = true;
  data::rewriter rewr;
  lps::communicationcomposition(
      C, allowlist, is_allow, is_block, lpe.lpe.action_summands(),
      lpe.lpe.deadlock_summands(), termination_action, nosumelm, nodeltaelimination, ignore_time, rewr);
}

/// \brief Apply a set of allowed multiactions to the lpe.
inline
void apply_allow(const process::action_name_multiset_list& allowlist, linearise_lpe& lpe)
{
  bool is_allow = true;
  process::action termination_action;
  bool nodeltaelimination = false;
  bool ignore_time = true;

  lps::allowblockcomposition(allowlist, is_allow, lpe.lpe.action_summands(), lpe.lpe.deadlock_summands(), termination_action, ignore_time, nodeltaelimination);
}

  /// \brief Compute summand for the communication merge of summand1 and summand 2.
  /// \param result The resulting summand.
  /// \param summand1 The first summand.
  /// \param summand2 The second summand.
  inline void
  communication_merge(action_summand& result, const action_summand& summand1, const action_summand& summand2)
{
  result.summation_variables() = summand1.summation_variables() + summand2.summation_variables();
  data::optimized_and(result.condition(), summand1.condition(), summand2.condition());
  result.multi_action() = detail::merge_multi_actions(summand1.multi_action(), summand2.multi_action());
  result.assignments() = summand1.assignments() + summand2.assignments();
}

/// \brief Compute summand for the communication merge of summand1 and summand 2.
inline
action_summand communication_merge(const action_summand& summand1, const action_summand& summand2)
{
  action_summand result;
  communication_merge(result, summand1, summand2);
  return result;
}

/// \brief Compute the communication merge of two vectors of action summands, insert
/// the resulting summands into an insert iterator
template<typename InsertIter, typename MultiActionFilter>
void communication_merge(InsertIter it,
  const action_summand_vector& summands1,
  const action_summand_vector& summands2,
  const MultiActionFilter& filter)
{
  const auto summand_combinations
    = utilities::cartesian_product(summands1, summands2);
  std::size_t filtered_summands = 0;

  std::for_each(summand_combinations.begin(), summand_combinations.end(), [&it, &filter, &filtered_summands](const auto& summand_pair)
  {
    const action_summand merged_summand = communication_merge(summand_pair.first, summand_pair.second);
    assert(detail::multi_actions_are_sorted(merged_summand));

    if (filter(merged_summand))
    {
      *it++ = merged_summand;
    }
    else
    {
      ++filtered_summands;
    }
  });

  if constexpr (detail::EnableLineariseStatistics)
  {
    std::cout << "communication_merge: filtered out " << filtered_summands << " summands\n";
  }
}

/// \brief Linearise parallel composition of two linear processes
/// \param lpe1 A linear process
/// \param lpe2 A linear process
/// \param filter A filter that determines which summands are allowed in the final result.
/// \pre The names of process parameters in lpe1 and lpe2 are disjoint
/// \return The linear process that results from the parallel composition of lpe1 and lpe2. The result only contains multiactions allowed by the filter.
template<class ActionSummandFilter>
linearise_lpe linearise_parallel(
  const linearise_lpe& lpe1,
  const linearise_lpe& lpe2,
  ActionSummandFilter filter = [](const action_summand&) { return true; })
{
  assert(utilities::detail::has_empty_intersection(
    detail::variable_names(lpe1.lpe.process_parameters()),
    detail::variable_names(lpe2.lpe.process_parameters())));

  [[maybe_unused]]
  lps_statistics_t lpe1_statistics_before = get_statistics(lpe1.lpe);
  [[maybe_unused]]
  lps_statistics_t lpe2_statistics_before = get_statistics(lpe2.lpe);

  linearise_lpe result;

  result.lpe.process_parameters()
    = lpe1.lpe.process_parameters() + lpe2.lpe.process_parameters();

  std::back_insert_iterator<action_summand_vector> insert_it
    = std::back_inserter(result.lpe.action_summands());

  std::copy_if(
    lpe1.lpe.action_summands().begin(),
    lpe1.lpe.action_summands().end(),
    insert_it,
    filter);

  std::copy_if(
    lpe2.lpe.action_summands().begin(),
    lpe2.lpe.action_summands().end(),
    insert_it,
    filter);

  communication_merge(
    insert_it,
    lpe1.lpe.action_summands(),
    lpe2.lpe.action_summands(),
    filter);

  make_process_initializer(result.initial_process, lpe1.initial_process.expressions() + lpe2.initial_process.expressions());

  assert(detail::multi_actions_are_sorted(result.lpe));

  [[maybe_unused]]
  lps_statistics_t lpe_statistics_after = get_statistics(result.lpe);

  if constexpr (detail::EnableLineariseStatistics)
  {
    lps_statistics_t lps_statistics_after = get_statistics(result.lpe);
    std::cout << "Parallel composition of two LPEs:\n";
    std::cout << "  First LPE before:\n"
      << print(lpe1_statistics_before, 4)
      << "  Second LPE before:\n"
      << print(lpe2_statistics_before, 4)
      << "  Resulting LPE after:\n"
      << print(lpe_statistics_after, 4);
  }

  return result;
}

/// \brief Linearise the parallel composition of the LPEs in [first, last)
template<typename Iter, class ActionSummandFilter>
linearise_lpe
linearise_parallel(Iter first, Iter last, ActionSummandFilter filter = [](const action_summand&) { return true; })
{
  assert(std::distance(first, last) > 1);

  // TODO: this is now implemented rather naively as a recursive function; it would be better to implement this as a loop
  if(std::distance(first, last) == 2)
  {
    return linearise_parallel(*first, *(std::next(first)), filter);
  }
  else
  {
    const linearise_lpe& left = *first;
    const linearise_lpe right = linearise_parallel(std::next(first), last, filter);
    return linearise_parallel(left, right, filter);
  }
}

/// \brief Linearise the parallel composition of a set of linear processes in the
/// context of a communication and allow operator.
///
/// \param allow_actions A set of allowed multiactions
/// \param comm_expressions A set of communication expressions
/// \param processes A vector of linear processes to be composed in parallel
///
/// \return The linear process allow(allow_actions, comm(comm_expressions, ||processes))
inline linearise_lpe linearise_new(
  const process::action_name_multiset_list& allow_actions,
  const process::communication_expression_list& comm_expressions,
  const std::vector<linearise_lpe>& processes)
{
  process::allow_set allow_actions_(to_multi_action_name_set(allow_actions));
  // First calculate an inner allow set:
  process::allow_set inner_allow_actions = process::alphabet_operations::comm_inverse(comm_expressions, allow_actions_);
  inner_allow_actions.A_includes_subsets = true; // We allow all subsets of allowed actions

  // Calculate parallel composition with inner allow set.
  linearise_lpe result = linearise_parallel(processes.begin(),
    processes.end(),
    [&inner_allow_actions](const action_summand& as)
    { return inner_allow_actions.contains(detail::multi_action_name(as.multi_action())); });

  assert(detail::multi_actions_are_sorted(result.lpe));

  // Apply communication and allow operators.
  apply_communication(comm_expressions, result);
  apply_allow(allow_actions, result);

  return result;
}

} // namespace mcrl2::lps

#endif // MCRL2_LPS_LINEARISE_NEW_H
