// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/action.h
/// \brief The class action.

#ifndef MCRL2_LPS_ACTION_H
#define MCRL2_LPS_ACTION_H

#include <cassert>
#include "mcrl2/data/data_expression.h"
#include "mcrl2/data/detail/data_functional.h"
#include "mcrl2/data/data_specification.h"
#include "mcrl2/lps/action_label.h"

namespace mcrl2
{

namespace lps
{

//--- start generated class action ---//
/// \brief An action
class action: public atermpp::aterm_appl
{
  public:
    /// \brief Default constructor.
    action()
      : atermpp::aterm_appl(core::detail::constructAction())
    {}

    /// \brief Constructor.
    /// \param term A term
    action(const atermpp::aterm& term)
      : atermpp::aterm_appl(term)
    {
      assert(core::detail::check_term_Action(m_term));
    }

    /// \brief Constructor.
    action(const action_label& label, const data::data_expression_list& arguments)
      : atermpp::aterm_appl(core::detail::gsMakeAction(label, arguments))
    {}

    const action_label& label() const
    {
      return atermpp::aterm_cast<const action_label>(atermpp::arg1(*this));
    }

    const data::data_expression_list& arguments() const
    {
      return atermpp::aterm_cast<const data::data_expression_list>(atermpp::list_arg2(*this));
    }
};

/// \brief list of actions
typedef atermpp::term_list<action> action_list;

/// \brief vector of actions
typedef std::vector<action>    action_vector;


/// \brief Test for a action expression
/// \param t A term
/// \return True if it is a action expression
inline
bool is_action(const atermpp::aterm_appl& t)
{
  return core::detail::gsIsAction(t);
}

//--- end generated class action ---//

// template function overloads
std::string pp(const action& x);
std::string pp(const action_list& x);
std::string pp(const action_vector& x);
action normalize_sorts(const action& x, const data::data_specification& dataspec);
lps::action translate_user_notation(const lps::action& x);
std::set<data::variable> find_free_variables(const lps::action& x);

/// \brief Compares the signatures of two actions
/// \param a An action
/// \param b An action
/// \return Returns true if the actions a and b have the same label, and
/// the sorts of the arguments of a and b are equal.
inline
bool equal_signatures(const action& a, const action& b)
{
  if (a.label() != b.label())
  {
    return false;
  }

  const data::data_expression_list& a_args = a.arguments();
  const data::data_expression_list& b_args = b.arguments();

  if (a_args.size() != b_args.size())
  {
    return false;
  }

  return std::equal(a_args.begin(), a_args.end(), b_args.begin(), mcrl2::data::detail::equal_data_expression_sort());
}

} // namespace lps

} // namespace mcrl2

#endif // MCRL2_LPS_ACTION_H
