// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file control_invariant_test.cpp
/// \brief Tests for strengthening an LPS with a pairwise control invariant.

#define BOOST_TEST_MODULE control_invariant_test
#include <boost/test/included/unit_test.hpp>

#include "mcrl2/data/join.h"
#include "mcrl2/lps/control_invariant.h"
#include "mcrl2/lps/parse.h"

#include <algorithm>

using namespace mcrl2;

namespace
{

lps::specification control_invariant(const std::string& text)
{
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::control_invariant(spec, rewr);
  return spec;
}

data::variable parameter(const lps::specification& spec, const std::string& name)
{
  const data::variable_list& parameters = spec.process().process_parameters();
  auto i = std::find_if(parameters.begin(),
    parameters.end(),
    [&](const data::variable& v) { return std::string(v.name()) == name; });
  BOOST_REQUIRE(i != parameters.end());
  return *i;
}

bool has_conjunct(const data::data_expression& condition, const data::data_expression& conjunct)
{
  return data::split_and(condition).contains(conjunct);
}

} // namespace

// A counter a hands control to three slots with program counters s1, s2, s3. Slot 1 writes x and
// slot 2 reads it. As in generated code, the completion step of every slot is present for every
// counter value, and the step that reads x only tests the program counter of its slot.
BOOST_AUTO_TEST_CASE(test_scheduler)
{
  const std::string text = "act write, read: Bool;\n"
                           "proc P(a, s1, s2, s3: Pos, x: Bool) =\n"
                           "     sum v: Bool. (a == 1 && s1 == 1) -> write(v) . P(a, 2, s2, s3, v)\n"
                           "   + (s1 == 2 && a == 1) -> tau . P(2, 1, s2, s3, x)\n"
                           "   + (s1 == 2 && a == 2) -> tau . P(3, 1, s2, s3, x)\n"
                           "   + (s1 == 2 && a == 3) -> tau . P(1, 1, s2, s3, x)\n"
                           "   + (a == 2 && s2 == 1) -> tau . P(a, s1, 2, s3, x)\n"
                           "   + (s2 == 2) -> read(x) . P(a, s1, 3, s3, x)\n"
                           "   + (s2 == 3 && a == 1) -> tau . P(2, s1, 1, s3, x)\n"
                           "   + (s2 == 3 && a == 2) -> tau . P(3, s1, 1, s3, x)\n"
                           "   + (s2 == 3 && a == 3) -> tau . P(1, s1, 1, s3, x)\n"
                           "   + (a == 3 && s3 == 1) -> tau . P(a, s1, s2, 2, x)\n"
                           "   + (s3 == 2 && a == 1) -> tau . P(2, s1, s2, 1, x)\n"
                           "   + (s3 == 2 && a == 2) -> tau . P(3, s1, s2, 1, x)\n"
                           "   + (s3 == 2 && a == 3) -> tau . P(1, s1, s2, 1, x);\n"
                           "init P(1, 1, 1, 1, false);\n";

  const lps::specification spec = control_invariant(text);

  // Only the completion steps at the slot's own counter value remain.
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 7U);

  // The step that reads x is only enabled when the counter has the value of slot 2.
  const data::variable a = parameter(spec, "a");
  const lps::action_summand_vector& summands = spec.process().action_summands();
  auto read = std::find_if(summands.begin(),
    summands.end(),
    [](const lps::action_summand& s)
    {
      return !s.multi_action().actions().empty()
             && std::string(s.multi_action().actions().front().label().name()) == "read";
    });
  BOOST_REQUIRE(read != summands.end());
  BOOST_CHECK(has_conjunct(read->condition(), data::equal_to(a, data::sort_pos::pos("2"))));
}

// A counter that is incremented under a range condition is split into one summand per value, so
// that its successor value is a constant.
BOOST_AUTO_TEST_CASE(test_range_split)
{
  const std::string text = "proc P(a: Nat) =\n"
                           "     (0 < a && a < 3) -> tau . P(a + 1)\n"
                           "   + (a == 3) -> tau . P(1);\n"
                           "init P(1);\n";

  const lps::specification spec = control_invariant(text);
  const lps::action_summand_vector& summands = spec.process().action_summands();
  BOOST_CHECK_EQUAL(summands.size(), 3U);

  const data::variable a = parameter(spec, "a");
  for (const char* value: {"1", "2"})
  {
    BOOST_CHECK(std::any_of(summands.begin(),
      summands.end(),
      [&](const lps::action_summand& s)
      { return has_conjunct(s.condition(), data::equal_to(a, data::sort_nat::nat(value))); }));
  }
}

// A summand that is not enabled in any reachable state is removed, also if the parameters it tests
// are set without testing their previous value.
BOOST_AUTO_TEST_CASE(test_dead_summand)
{
  const std::string text = "proc P(a: Nat, s: Pos) =\n"
                           "     (s == 1) -> tau . P(1, 2)\n"
                           "   + (s == 2) -> tau . P(0, 1)\n"
                           "   + (s == 1 && a == 1) -> tau . P(a, s);\n"
                           "init P(0, 1);\n";

  const lps::specification spec = control_invariant(text);
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 2U);
}
