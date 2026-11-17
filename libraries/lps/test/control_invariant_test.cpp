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
#include "mcrl2/lps/split_ranges.h"

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

// The running example of the theory note (doc/plans/stategraph/theory.md, §1.4): a counter a hands
// control to two slots with program counters s1 and s2; slot 1 writes x, slot 2 reads it, and a slot
// ends by incrementing the counter under a range condition.
BOOST_AUTO_TEST_CASE(test_scoped_graphs)
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
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::split_ranges(spec, rewr);
  lps::detail::control_invariant_analysis analysis(spec, rewr);
  analysis.run();

  // a, s1 and s2 are control flow parameters, x is not.
  const std::size_t a = 0;
  const std::size_t s1 = 1;
  const std::size_t s2 = 2;
  BOOST_CHECK(analysis.control_flow(a));
  BOOST_CHECK(analysis.control_flow(s1));
  BOOST_CHECK(analysis.control_flow(s2));
  BOOST_CHECK(!analysis.control_flow(3));

  // Two of the eight summands (slot 1 ending at a = 2, slot 2 ending at a = 1) are dead; each of the
  // other six has an edge in every scoped graph.
  using graph = lps::detail::control_invariant_analysis::scoped_graph;
  const graph empty = analysis.compute_scoped_graph({});
  BOOST_CHECK_EQUAL(empty.vertices.size(), 1U);
  BOOST_CHECK_EQUAL(empty.edges.size(), 6U);

  const graph g_a = analysis.compute_scoped_graph({a});
  BOOST_CHECK_EQUAL(g_a.vertices.size(), 3U);
  BOOST_CHECK_EQUAL(g_a.edges.size(), 6U);

  // The vertices of the pair scope {a, s1} are the reachable pairs (1,1), (1,2), (2,1) and (3,1).
  const graph g_a_s1 = analysis.compute_scoped_graph({a, s1});
  BOOST_CHECK_EQUAL(g_a_s1.vertices.size(), 4U);
  BOOST_CHECK_EQUAL(g_a_s1.edges.size(), 6U);
  for (const auto& [va, vs1]:
    std::vector<std::pair<std::string, std::string>>{{"1", "1"}, {"1", "2"}, {"2", "1"}, {"3", "1"}})
  {
    const lps::detail::control_invariant_analysis::valuation p
      = {{a, rewr(data::sort_nat::nat(va))}, {s1, rewr(data::sort_pos::pos(vs1))}};
    BOOST_CHECK(g_a_s1.index.find(p) != g_a_s1.index.end());
  }

  // With all control flow parameters, the graph is the six-state cycle of reachable control states.
  const graph g_all = analysis.compute_scoped_graph({a, s1, s2});
  BOOST_CHECK_EQUAL(g_all.vertices.size(), 6U);
  BOOST_CHECK_EQUAL(g_all.edges.size(), 6U);
}
