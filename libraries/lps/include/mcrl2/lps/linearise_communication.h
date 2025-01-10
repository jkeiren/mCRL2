// Author(s): Jan Friso Groote, Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/linearise_communication.h
/// \brief Apply the rename operator to action summands.

#ifndef MCRL2_LPS_LINEARISE_COMMUNICATION_H
#define MCRL2_LPS_LINEARISE_COMMUNICATION_H

#include "mcrl2/atermpp/aterm_list.h"
#include "mcrl2/lps/linearise_allow_block.h"
#include "mcrl2/lps/linearise_utility.h"
#include "mcrl2/lps/sumelm.h"
#include "mcrl2/lps/stochastic_action_summand.h"
#include "mcrl2/process/process_expression.h"

#define MCRL2_COUNT_COMMUNICATION_OPERATIONS

namespace mcrl2
{

namespace lps
{

using action_name_t = core::identifier_string;
using action_multiset_t = process::action_list; // sorted w.r.t. action_compare
using action_name_multiset_t = core::identifier_string_list; // sorted w.r.t. action_label_compare


inline
core::identifier_string_list names(const action_multiset_t& actions)
{
  core::identifier_string_list result;
  atermpp::make_term_list(result, actions.begin(), actions.end(), [](const process::action& action) { return action.label().name(); });
  return result;
}

// Check that the sorts of both termlists match.
inline
data::data_expression pairwiseMatch(const data::data_expression_list& l1, const data::data_expression_list& l2, const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)
{
  if (l1.size()!=l2.size())
  {
    return data::sort_bool::false_();
  }

  data::data_expression_list::const_iterator i2=l2.begin();
  data::data_expression result=data::sort_bool::true_();
  for(const data::data_expression& t1: l1)
  {
    if (t1.sort()!=i2->sort())
    {
      return data::sort_bool::false_();
    }
    result=data::lazy::and_(result,RewriteTerm(equal_to(t1,*i2)));
    ++i2;
  }
  return result;
}

// a tuple_list contains pairs of actions (multi-action) and the condition under which this action
// can occur.
struct tuple_list
{
  std::vector < action_multiset_t > actions;
  std::vector < data::data_expression > conditions;

  std::size_t size() const
  {
    assert(action.size() == conditions.size());
    return actions.size();
  }

  tuple_list() = default;

  tuple_list(const std::vector < action_multiset_t>& actions_, const std::vector< data::data_expression >& conditions_)
    : actions(actions_), conditions(conditions_)
  {}

  tuple_list(std::vector < action_multiset_t>&& actions_, std::vector< data::data_expression >&& conditions_)
    : actions(std::move(actions_)), conditions(std::move(conditions_))
  {}
};

/// Extends the list S to S ++ L',
/// where L' is the list L in which firstaction is inserted into every action, and each condition is strengthened with condition.
///
/// Note that by using move semantics for L, we force the caller to transfer ownership of L to this function,
/// and make it explicit that L should not be used by the caller afterwards.
/// If firstaction == action(), it is not added to the multiactions in L', but the conditions will be strengthened.
/// \pre condition != sort_bool::false_()
inline
void addActionCondition(
  const process::action& firstaction,
  const data::data_expression& condition,
  tuple_list&& L,
  tuple_list& S)
{
  assert(condition!=sort_bool::false_()); // It makes no sense to add an action with condition false, as it cannot happen anyhow.

  // If S is empty, do not copy the vectors, but simply perform the operation in L and move.
  // This is a common special case
  if (S.size() == 0)
  {
    if (firstaction != process::action())
    {
      for (action_multiset_t& m: L.actions)
      {
        m = insert(firstaction, m);
      }
    }

    // Strengthen the conditions in L with condition and append to S.
    for (data::data_expression& x: L.conditions)
    {
      x = data::lazy::and_(x, condition);
    }
    S = std::move(L);
    return;
  }

  if (firstaction == process::action())
  {
    S.actions.insert(S.actions.end(), std::make_move_iterator(L.actions.begin()), std::make_move_iterator(L.actions.end()));
  }
  else
  {
    for (action_multiset_t& m: L.actions)
    {
      m = insert(firstaction, m);
      S.actions.emplace_back(std::move(m));
    }
  }

  // Strengthen the conditions in L with condition and append to S.
  for (const data::data_expression& x: L.conditions)
  {
    S.conditions.emplace_back(data::lazy::and_(x, condition));
  }
}

/// Data structure to store the communication function more efficiently.
class comm_entry
{
  protected:
    /// Left-hand sides of communication expressions
    const std::vector<action_name_multiset_t> m_lhs;

    /// Right-hand sides of communication expressions
    const std::vector<action_name_t> m_rhs;

    /// Temporary data using in determining whether communication is allowed.
    /// See usages of the data structure below.
    std::vector<action_name_multiset_t::const_iterator> m_lhs_iters; // offset into lhs
    std::vector<bool> m_match_failed;

    void reset_temporary_data()
    {
      for (std::size_t i = 0; i < size(); ++i)
      {
        m_lhs_iters[i] = m_lhs[i].begin();
        m_match_failed[i] = false;
      }
    }

    /// Check if m is contained in a lhs in the communication entry.
    /// Returns true if this is the case, false otherwise.
    /// Postcondition: for every i such that m is not contained in lhs[i], match_failed[i] is true.
    /// NB: resets temporary data before performing computations.
    bool match_multiaction(const core::identifier_string_list& names) {
      reset_temporary_data();

      // m must match a lhs; check every action
      for (const action_name_t& actionname: names)
      {

        // check every lhs for actionname
        bool comm_ok = false;
        for (std::size_t i=0; i < size(); ++i)
        {
          if (m_match_failed[i]) // lhs i does not match
          {
            continue;
          }
          if (m_lhs_iters[i] == m_lhs[i].end()) // lhs cannot match actionname
          {
            m_match_failed[i]=true;
            continue;
          }
          if (actionname != *m_lhs_iters[i])
          {
            // no match
            m_match_failed[i] = true;
          }
          else
          {
            // possible match; on to next action
            ++m_lhs_iters[i];
            comm_ok = true;
          }
        }

        if (!comm_ok)   // no (possibly) matching lhs
        {
          return false;
        }
      }

      // There must be an lhs that contains m.
      return true;
    }

    // Initialization of lhs, defined as static function so it can be used in the constructor.
    // Allows lhs to be defined as const.
    static std::vector < action_name_multiset_t > init_lhs(const process::communication_expression_list& communications)
    {
      std::vector<action_name_multiset_t> result;
      for (const process::communication_expression& l: communications)
      {
        const core::identifier_string_list& names = l.action_name().names();
        result.emplace_back(names.begin(), names.end());
      }
      return result;
    }

    // Initialization of rhs, defined as static function so it can be used in the constructor.
    // Allows rhs to be defined as const.
    static std::vector <action_name_t> init_rhs(const process::communication_expression_list& communications)
    {
      std::vector <action_name_t> result;
      for (const process::communication_expression& l: communications)
      {
        result.push_back(l.name());
      }
      return result;
    }

  public:
    // comm_entries are not copyable.
    comm_entry(const comm_entry& )=delete;
    comm_entry& operator=(const comm_entry& )=delete;

    comm_entry(const process::communication_expression_list& communications)
        : m_lhs(init_lhs(communications)),
          m_rhs(init_rhs(communications)),
          m_lhs_iters(communications.size()),
          m_match_failed(communications.size())
    {}

    ~comm_entry() = default;

    std::size_t size() const
    {
      assert(lhs.size()==rhs.size() && rhs.size()==m_lhs_iters.size() && m_lhs_iters.size()==match_failed.size());
      return m_lhs.size();
    }

    /// Determine if there exists a communication expression a1|...|an -> b in comm_table
    /// such that m' \subseteq a1|...|an , where m' is the multiset of actionnames for multiaction m.
    process::action_label can_communicate(const action_multiset_t& m)
    {
      /* this function indicates whether the actions in m
                   consisting of actions and data occur in C, such that
                   a communication can take place. If not process::action_label() is delivered,
                   otherwise the resulting action is the result. */

      const core::identifier_string_list m_names = names(m);

      process::action_label result; // if no match fount, return process::action_label()

      if(match_multiaction(m_names))
      {
        // there is a lhs containing m; find it
        for (std::size_t i = 0; i < size(); ++i)
        {
          // lhs i matches only if comm_table[i] is empty
          if ((!m_match_failed[i]) && m_lhs_iters[i] == m_lhs[i].end())
          {
            if (m_rhs[i] == process::tau())
            {
              throw mcrl2::runtime_error("Cannot linearise a process with a communication operator, containing a communication that results in tau or that has an empty right hand side");
            }
            result = process::action_label(m_rhs[i], m.begin()->label().sorts());
            break;
          }
        }
      }

      return result;
    }

  template <typename ConstIterType>
  bool might_communicate(const action_multiset_t& m,
      ConstIterType n_first,
      ConstIterType n_last)
    {
      /* this function indicates whether the actions in m
         consisting of actions and data occur in C, such that
         a communication might take place (i.e. m is a subbag
         of the lhs of a communication in C).
         if n is not empty, then all actions of a matching communication
         that are not in m should be in n (i.e. there must be a
         subbag o of n such that m+o can communicate. */
      const core::identifier_string_list m_names = names(m);

      bool result = false;

      if(match_multiaction(m_names))
      {
        // the rest of actions of lhs that are not in m should be in n
        // rest[i] contains the part of n in which lhs i has to find matching actions
        // if rest[i] cannot match the next remaining action in the left hand side, stored in m_lhs_iters[i], i.e., rest[i] becomes empty
        // before matching all actions in the lhs, we set it to std::nullopt.
        // N.B. when rest[i] becomes empty after matching all actions in the lhs,
        // rest[i].empty() is a meaningful result: we have a successful match.
        std::vector<std::optional<ConstIterType>>
          rest(size(), n_first); // pairs of iterator into n; the second element of the pair indicates the end of the range in n.

        // check every lhs
        for (std::size_t i = 0; i < size(); ++i)
        {
          if (m_match_failed[i]) // lhs i did not contain m
          {
            continue;
          }

          // as long as there are still unmatched actions in lhs i...
          while (m_lhs_iters[i] != m_lhs[i].end())
          {
            assert(rest[i] != std::nullopt);
            // .. find them in rest[i]
            if (*rest[i] == n_last) // no luck
            {
              rest[i] = std::nullopt;
              break;
            }
            // get first action in lhs i
            const action_name_t& comm_name = *m_lhs_iters[i];
            action_name_t rest_name = (*rest[i])->label().name();
            // find it in rest[i]
            while (comm_name != rest_name)
            {
              ++(*rest[i]);
              if (*rest[i] == n_last) // no more
              {
                rest[i] = std::nullopt;
                break;
              }
              rest_name = (*rest[i])->label().name();
            }
            if (comm_name != rest_name) // action was not found
            {
              break;
            }

            // action found; try next
            ++(*rest[i]);
            ++m_lhs_iters[i];
          }

          if (rest[i] != std::nullopt) // lhs was found in rest[i]
          {
            result = true;
            break;
          }
        }
      }

      return result;
    }
};

/// \prototype
inline
tuple_list makeMultiActionConditionList_aux(
  action_multiset_t::const_iterator multiaction_first,
  action_multiset_t::const_iterator multiaction_last,
  comm_entry& comm_table,
  const action_multiset_t& r,
  const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm);

inline
tuple_list phi(const action_multiset_t& m,
               const data::data_expression_list& d,
               const action_multiset_t& w,
               const action_multiset_t::const_iterator& n_first,
               const action_multiset_t::const_iterator& n_last,
               const action_multiset_t& r,
               comm_entry& comm_table,
               const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)
{
  /* phi is a function that yields a list of pairs
     indicating how the actions in m|w|n can communicate.
     The pairs contain the resulting multi action and
     a condition on data indicating when communication
     can take place. In the communication all actions of
     m, none of w and a subset of n can take part in the
     communication. d is the data parameter of the communication
     and comm_table contains a list of multiaction action pairs indicating
     possible communications */

  if (!comm_table.might_communicate(m, n_first, n_last))
  {
    return tuple_list();
  }
  if (n_first == n_last)
  {
    const process::action_label c = comm_table.can_communicate(m); /* returns process::action_label() if no communication
                                                              is possible */
    if (c!=process::action_label())
    {
      tuple_list T=makeMultiActionConditionList_aux(w.begin(), w.end(),comm_table,r,RewriteTerm);
      tuple_list result;
      addActionCondition(process::action(c,d), data::sort_bool::true_(), std::move(T), result);
      return result;
    }
    /* c==NULL, actions in m cannot communicate */
    return tuple_list();
  }
  /* if n=[a(f)] \oplus o */
  const process::action& firstaction=*n_first;

  const data::data_expression condition=pairwiseMatch(d,firstaction.arguments(),RewriteTerm);
  if (condition==data::sort_bool::false_())
  {
    // a(f) cannot take part in communication as the arguments do not match. Move to w and continue with next action
    const tuple_list result = phi(m,d,insert(firstaction, w),std::next(n_first), n_last,r,comm_table,RewriteTerm);
    return result;
  }
  else
  {
    tuple_list T=phi(insert(firstaction, m),d,w,std::next(n_first), n_last,r,comm_table,RewriteTerm);

    tuple_list result = phi(m,d,insert(firstaction, w),std::next(n_first), n_last,r,comm_table,RewriteTerm);
    addActionCondition(
             process::action(),
             condition,
             std::move(T),
             result);
    return result;
  }
}

template <typename ConstIterType>
bool xi(const action_multiset_t& alpha,
        const ConstIterType& beta_first,
        const ConstIterType& beta_last,
        comm_entry& comm_table)
{
  if (beta_first == beta_last)
  {
    return comm_table.can_communicate(alpha)!=process::action_label();
  }

  const action_multiset_t alpha_ = insert(*beta_first, alpha);

  if (comm_table.can_communicate(alpha_)!=process::action_label())
  {
    return true;
  }

  bool result = false;
  if (comm_table.might_communicate(alpha_,std::next(beta_first), beta_last))
  {
    result = xi(alpha,std::next(beta_first), beta_last,comm_table);
  }

  result = result || xi(alpha,std::next(beta_first), beta_last, comm_table);
  return result;
}

inline
data::data_expression psi(const action_multiset_t& alpha, comm_entry& comm_table, const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)
{
  const action_multiset_t alpha_reverse = reverse(alpha);
  action_multiset_t::const_iterator alpha_first = alpha_reverse.begin();
  const action_multiset_t::const_iterator alpha_last = alpha_reverse.end();

  data::data_expression cond = data::sort_bool::false_();

  action_multiset_t actl; // used in inner loop.
  while (alpha_first != alpha_last)
  {
    action_multiset_t::const_iterator beta_first = std::next(alpha_first);
    const action_multiset_t::const_iterator beta_last = alpha_last;

    while (beta_first != beta_last)
    {
      actl = action_multiset_t();
      actl = insert(*beta_first, actl);
      actl = insert(*alpha_first, actl);
      if (comm_table.might_communicate(actl,std::next(beta_first), beta_last) && xi(actl,std::next(beta_first), beta_last,comm_table))
      {
        // sort and remove duplicates??
        cond = data::lazy::or_(cond,pairwiseMatch(alpha_first->arguments(),beta_first->arguments(),RewriteTerm));
      }
      beta_first = std::next(beta_first);
    }

    alpha_first = std::next(alpha_first);
  }
  return data::lazy::not_(cond);
}

// returns a list of tuples.
inline
tuple_list makeMultiActionConditionList_aux(
  action_multiset_t::const_iterator multiaction_first,
  action_multiset_t::const_iterator multiaction_last,
  comm_entry& comm_table,
  const action_multiset_t& r,
  const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)
{
  /* This is the function gamma(m,C,r) provided
     by Muck van Weerdenburg in Calculation of
     Communication with open terms [1]. */
  if (multiaction_first == multiaction_last)
  {
    tuple_list t;
    t.conditions.push_back((r.empty())?static_cast<const data::data_expression&>(data::sort_bool::true_()):psi(r,comm_table,RewriteTerm));
    t.actions.push_back(action_multiset_t());
    return t;
  }

  const process::action& firstaction = *multiaction_first;

  action_multiset_t m({firstaction});
  action_multiset_t w;
  tuple_list S=phi(m,
                         firstaction.arguments(),
                         w,
                         std::next(multiaction_first), multiaction_last,
                         r,comm_table, RewriteTerm);

  tuple_list T=makeMultiActionConditionList_aux(std::next(multiaction_first), multiaction_last,comm_table,
                       insert(firstaction, r),RewriteTerm);
  addActionCondition(firstaction,data::sort_bool::true_(),std::move(T),S);
  return S;
}

inline
tuple_list makeMultiActionConditionList(
  const action_multiset_t& multiaction,
  const process::communication_expression_list& communications,
  const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)
{
  comm_entry comm_table(communications);
  action_multiset_t r;
  return makeMultiActionConditionList_aux(multiaction.begin(), multiaction.end(), comm_table, r, RewriteTerm);
}

/// Apply the communication composition to a list of action summands.
inline
void communicationcomposition(
  process::communication_expression_list communications,
  process::action_name_multiset_list allowlist,  // This is a list of list of identifierstring.
  const bool is_allow,                          // If is_allow or is_block is set, perform inline allow/block filtering.
  const bool is_block,
  stochastic_action_summand_vector& action_summands,
  deadlock_summand_vector& deadlock_summands,
  const process::action& terminationAction,
  const bool nosumelm,
  const bool nodeltaelimination,
  const bool ignore_time,
  const std::function<data::data_expression(const data::data_expression&)>& RewriteTerm)

{
  /* We follow the implementation of Muck van Weerdenburg, described in
     a note: Calculation of communication with open terms. */

  mCRL2log(mcrl2::log::verbose) <<
        (is_allow ? "- calculating the communication operator modulo the allow operator on " :
         is_block ? "- calculating the communication operator modulo the block operator on " :
                    "- calculating the communication operator on ") << action_summands.size() << " action summands";

#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
  mCRL2log(mcrl2::log::info) << "Calculating communication operator using a set of " << communications.size() << " communication expressions." << std::endl;
#endif

  // Ensure communications and allowlist are sorted. We rely on the sort order later.
  communications = sort_communications(communications);
  if (is_allow)
  {
    allowlist = sort_multi_action_labels(allowlist);
  }

  deadlock_summand_vector resulting_deadlock_summands;
  deadlock_summands.swap(resulting_deadlock_summands);

  const bool inline_allow = is_allow || is_block;
  if (inline_allow)
  {
    // Inline allow is only supported for ignore_time,
    // for in other cases generation of delta summands cannot be inlined in any simple way.
    assert(!nodeltaelimination && ignore_time);
    deadlock_summands.push_back(deadlock_summand(data::variable_list(), data::sort_bool::true_(),deadlock()));
  }

  stochastic_action_summand_vector resulting_action_summands;

  for (const stochastic_action_summand& smmnd: action_summands)
  {
    const data::variable_list& sumvars = smmnd.summation_variables();
    const process::action_list& multiaction = smmnd.multi_action().actions();
    const data::data_expression& time = smmnd.multi_action().time();
    const data::data_expression& condition = smmnd.condition();
    const data::assignment_list& nextstate = smmnd.assignments();
    const stochastic_distribution& dist = smmnd.distribution();

    if (!inline_allow)
    {
      /* Recall a delta summand for every non delta summand.
       * The reason for this is that with communication, the
       * conditions for summands can become much more complex.
       * Many of the actions in these summands are replaced by
       * delta's later on. Due to the more complex conditions it
       * will be hard to remove them. By adding a default delta
       * with a simple condition, makes this job much easier
       * later on, and will in general reduce the number of delta
       * summands in the whole system */

      // Create new list of summand variables containing only those that occur in the condition or the timestamp.
      data::variable_list newsumvars;
      atermpp::make_term_list(newsumvars, sumvars.begin(), sumvars.end(), [](const data::variable& v) { return v; },
        [&condition, &time](const data::variable& v) { return occursinterm(condition, v) || occursinterm(time, v); });

      resulting_deadlock_summands.emplace_back(newsumvars, condition, deadlock(time));
    }

    /* the multiactionconditionlist is a list containing
       tuples, with a multiaction and the condition,
       expressing whether the multiaction can happen. All
       conditions exclude each other. Furthermore, the list
       is not empty. If no communications can take place,
       the original multiaction is delivered, with condition
       true. */

    const tuple_list multiactionconditionlist=
      makeMultiActionConditionList(
        multiaction,
        communications,
        RewriteTerm);

#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
    mCRL2log(mcrl2::log::info) << "Calculating communication on multiaction with " << multiaction.size() << " actions results in " << multiactionconditionlist.size() << " potential summands" << std::endl;
    std::size_t disallowed_summands = 0;
    std::size_t blocked_summands = 0;
    std::size_t false_condition_summands = 0;
    std::size_t added_summands = 0;
#endif

    for (std::size_t i=0 ; i<multiactionconditionlist.size(); ++i)
    {

      const process::action_list& multiaction=multiactionconditionlist.actions[i];

      if (is_allow && !allow_(allowlist, multiaction,terminationAction))
      {
#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
        ++disallowed_summands;
#endif
        continue;
      }
      if (is_block && encap(allowlist,multiaction))
      {
#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
        ++blocked_summands;
#endif
        continue;
      }

      const data::data_expression communicationcondition=
        RewriteTerm(multiactionconditionlist.conditions[i]);

      const data::data_expression newcondition=RewriteTerm(
                                           data::lazy::and_(condition,communicationcondition));
      stochastic_action_summand new_summand(sumvars,
                                 newcondition,
                                 smmnd.multi_action().has_time()?multi_action(multiaction, smmnd.multi_action().time()):multi_action(multiaction),
                                 nextstate,
                                 dist);
      if (!nosumelm)
      {
        if (sumelm(new_summand))
        {
          new_summand.condition() = RewriteTerm(new_summand.condition());
        }
      }
#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
      if (new_summand.condition()==data::sort_bool::false_())
      {
        ++false_condition_summands;
      }
#endif
      if (new_summand.condition()!=data::sort_bool::false_())
      {
        resulting_action_summands.push_back(new_summand);
#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
        ++added_summands;
#endif
      }
    }

#ifdef MCRL2_COUNT_COMMUNICATION_OPERATIONS
     mCRL2log(mcrl2::log::info) << "Statistics of new summands: " << std::endl
     << "- Disallowed summands: " << disallowed_summands << std::endl
     << "- Blocked summands: " << blocked_summands << std::endl
     << "- Summands with false condition: " << false_condition_summands << std::endl
     << "- New summands added: " << added_summands << std::endl;
#endif

  }

  action_summands.swap(resulting_action_summands);

  /* Now the resulting delta summands must be added again */
  if (!inline_allow && !nodeltaelimination)
  {
    for (const deadlock_summand& summand: resulting_deadlock_summands)
    {
      insert_timed_delta_summand(action_summands, deadlock_summands, summand, ignore_time);
    }
  }

  mCRL2log(mcrl2::log::verbose) << " resulting in " << action_summands.size() << " action summands and " << deadlock_summands.size() << " delta summands\n";
}

} // namespace lps

} // namespace mcrl2



#endif // MCRL2_LPS_LINEARISE_COMMUNICATION_H
