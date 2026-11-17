// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file scoped_stategraph_test.cpp
/// \brief Tests for resetting dead data parameters using liveness on scoped control flow graphs.

#define BOOST_TEST_MODULE scoped_stategraph_test
#include <boost/test/included/unit_test.hpp>

#include "mcrl2/lps/parse.h"
#include "mcrl2/lps/scoped_stategraph.h"
#include "mcrl2/lps/split_ranges.h"

#include <algorithm>

using namespace mcrl2;

namespace
{

// The number of summands that reset parameter x to false.
std::size_t resets_of_x(const std::string& text, lps::liveness_scopes scopes)
{
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::split_ranges(spec, rewr);
  lps::scoped_stategraph(spec, rewr, scopes);
  const lps::action_summand_vector& summands = spec.process().action_summands();
  return std::count_if(summands.begin(),
    summands.end(),
    [](const lps::action_summand& s)
    {
      const data::assignment_list& assignments = s.assignments();
      return std::any_of(assignments.begin(),
        assignments.end(),
        [](const data::assignment& a)
        { return std::string(a.lhs().name()) == "x" && a.rhs() == data::sort_bool::false_(); });
    });
}

} // namespace

// The running example of the stategraph notes (doc/plans/stategraph/theory.md, §1.4): a counter a
// hands control to two slots with program counters s1 and s2; slot 1 writes x, slot 2 reads it.
// Liveness per control flow parameter finds nothing; the pair (a, s1) shows that x is dead when a
// becomes 3 (summands 5 and 6); all control flow parameters together also show that x is dead after
// the read (summand 4).
BOOST_AUTO_TEST_CASE(test_running_example)
{
  const std::string text = "act write, read: Bool;\n"
                           "proc P(a: Nat, s1, s2: Pos, x: Bool) =\n"
                           "     sum v: Bool. (a == 1 && s1 == 1) -> write(v) . P(a, 2, s2, v)\n"
                           "   + (s1 == 2 && 0 < a && a < 3) -> tau . P(a + 1, 1, s2, x)\n"
                           "   + (a == 2 && s2 == 1) -> tau . P(a, s1, 2, x)\n"
                           "   + (s2 == 2) -> read(x) . P(a, s1, 3, x)\n"
                           "   + (s2 == 3 && 0 < a && a < 3) -> tau . P(a + 1, s1, 1, x)\n"
                           "   + (a == 3) -> tau . P(1, s1, s2, x);\n"
                           "init P(1, 1, 1, false);\n";
  BOOST_CHECK_EQUAL(resets_of_x(text, lps::liveness_scopes::single), 0U);
  BOOST_CHECK_EQUAL(resets_of_x(text, lps::liveness_scopes::pairs), 2U);
  BOOST_CHECK_EQUAL(resets_of_x(text, lps::liveness_scopes::global), 3U);
}

// As the running example, but slot 1 writes x in the step that hands control to slot 2, as in code
// generated from PLC-style models (theory.md, Ex. 5.8). Then liveness per control flow parameter
// already shows that x is dead from slot 2's completion until slot 1 writes it again.
BOOST_AUTO_TEST_CASE(test_write_on_completion)
{
  const std::string text = "act write, read: Bool;\n"
                           "proc P(a: Nat, s1, s2: Pos, x: Bool) =\n"
                           "     (a == 1 && s1 == 1) -> tau . P(a, 2, s2, x)\n"
                           "   + sum v: Bool. (s1 == 2 && 0 < a && a < 3) -> write(v) . P(a + 1, 1, s2, v)\n"
                           "   + (a == 2 && s2 == 1) -> tau . P(a, s1, 2, x)\n"
                           "   + (s2 == 2) -> read(x) . P(a, s1, 3, x)\n"
                           "   + (s2 == 3 && 0 < a && a < 3) -> tau . P(a + 1, s1, 1, x)\n"
                           "   + (a == 3) -> tau . P(1, s1, s2, x);\n"
                           "init P(1, 1, 1, false);\n";
  BOOST_CHECK_EQUAL(resets_of_x(text, lps::liveness_scopes::single), 3U);
  BOOST_CHECK_EQUAL(resets_of_x(text, lps::liveness_scopes::pairs), 4U);
}

// A data parameter that is never used is reset by the empty scope, also without control flow
// parameters. (y is not trackable: its new value depends on a summation variable.)
BOOST_AUTO_TEST_CASE(test_unused)
{
  const std::string text = "act a: Bool;\n"
                           "proc P(x, y: Bool) =\n"
                           "     sum v: Bool. a(x) . P(v, !v);\n"
                           "init P(false, false);\n";
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::scoped_stategraph(spec, rewr, lps::liveness_scopes::single);
  const data::assignment_list& assignments = spec.process().action_summands().front().assignments();
  const bool y_reset = std::any_of(assignments.begin(),
    assignments.end(),
    [](const data::assignment& a)
    { return std::string(a.lhs().name()) == "y" && a.rhs() == data::sort_bool::false_(); });
  BOOST_CHECK(y_reset);
}
