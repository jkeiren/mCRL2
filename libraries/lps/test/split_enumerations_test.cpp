// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file split_enumerations_test.cpp
/// \brief Tests for splitting summands on the values of a parameter of an enumerated sort.

#define BOOST_TEST_MODULE split_enumerations_test
#include <boost/test/included/unit_test.hpp>

#include "mcrl2/data/join.h"
#include "mcrl2/lps/parse.h"
#include "mcrl2/lps/split_enumerations.h"

#include <algorithm>

using namespace mcrl2;

namespace
{

const std::string scheduler_sorts = "sort Slot = struct None | A | B | C;\n"
                                    "map next: Slot -> Slot;\n"
                                    "eqn next(A) = B; next(B) = C; next(C) = None; next(None) = A;\n";

lps::specification split_enumerations(const std::string& text, std::size_t max_values = 32)
{
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::split_enumerations_options options;
  options.max_values = max_values;
  lps::split_enumerations(spec, rewr, options);
  return spec;
}

// Returns true if every summand that assigns to p assigns a constant.
bool has_constant_updates(const lps::specification& spec, const data::variable& p)
{
  const lps::action_summand_vector& summands = spec.process().action_summands();
  return std::all_of(summands.begin(),
    summands.end(),
    [&](const lps::action_summand& s)
    {
      const data::assignment_list& assignments = s.assignments();
      return std::all_of(assignments.begin(),
        assignments.end(),
        [&](const data::assignment& a) { return a.lhs() != p || data::is_constant(a.rhs()); });
    });
}

data::variable parameter(const lps::specification& spec)
{
  return spec.process().process_parameters().front();
}

} // namespace

// The slot of a scheduler is split into one summand per value that satisfies the condition, and
// each of them assigns a constant.
BOOST_AUTO_TEST_CASE(test_scheduler)
{
  const lps::specification spec = split_enumerations(scheduler_sorts
                                                     + "act a;\n"
                                                       "proc P(s: Slot) =\n"
                                                       "     (s != None) -> a . P(next(s))\n"
                                                       "   + (s == None) -> tau . P(A);\n"
                                                       "init P(None);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 4U);
  BOOST_CHECK(has_constant_updates(spec, parameter(spec)));
}

// A Boolean that is toggled is split as well.
BOOST_AUTO_TEST_CASE(test_bool)
{
  const lps::specification spec = split_enumerations("act a;\n"
                                                     "proc P(b: Bool) = a . P(!b);\n"
                                                     "init P(true);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 2U);
  BOOST_CHECK(has_constant_updates(spec, parameter(spec)));
}

// A parameter that some summand assigns a value depending on other data is not split, since it
// would not become a control flow parameter.
BOOST_AUTO_TEST_CASE(test_data_update)
{
  const lps::specification spec = split_enumerations(scheduler_sorts
                                                     + "act a;\n"
                                                       "proc P(s: Slot, t: Slot) =\n"
                                                       "     (s != None) -> a . P(s = next(s))\n"
                                                       "   + (s == None) -> tau . P(s = t);\n"
                                                       "init P(None, A);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 2U);
}

// A sort with more values than the maximum is not split.
BOOST_AUTO_TEST_CASE(test_max_values)
{
  const std::string text = scheduler_sorts
                           + "act a;\n"
                             "proc P(s: Slot) = a . P(next(s));\n"
                             "init P(None);\n";
  BOOST_CHECK_EQUAL(split_enumerations(text, 3).process().action_summands().size(), 1U);
  BOOST_CHECK_EQUAL(split_enumerations(text, 4).process().action_summands().size(), 4U);
}

// A sort with a constructor that has arguments is not split.
BOOST_AUTO_TEST_CASE(test_non_enumeration)
{
  const lps::specification spec
    = split_enumerations("sort D = struct d1 | d2(b: Bool);\n"
                         "map f: D -> D;\n"
                         "eqn f(d1) = d2(true); f(d2(true)) = d2(false); f(d2(false)) = d1;\n"
                         "act a;\n"
                         "proc P(x: D) = a . P(f(x));\n"
                         "init P(d1);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 1U);
}
