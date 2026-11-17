// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file split_ranges_test.cpp
/// \brief Tests for splitting summands on small ranges of a numeric parameter.

#define BOOST_TEST_MODULE split_ranges_test
#include <boost/test/included/unit_test.hpp>

#include "mcrl2/data/join.h"
#include "mcrl2/lps/parse.h"
#include "mcrl2/lps/split_ranges.h"

#include <algorithm>

using namespace mcrl2;

namespace
{

lps::specification split_ranges(const std::string& text, std::size_t max_range = 16)
{
  lps::specification spec = lps::parse_linear_process_specification(text);
  data::rewriter rewr(spec.data());
  lps::split_ranges_options options;
  options.max_range = max_range;
  lps::split_ranges(spec, rewr, options);
  return spec;
}

bool has_summand_with_conjunct(const lps::specification& spec, const data::data_expression& conjunct)
{
  const lps::action_summand_vector& summands = spec.process().action_summands();
  return std::any_of(summands.begin(),
    summands.end(),
    [&](const lps::action_summand& s) { return data::split_and(s.condition()).contains(conjunct); });
}

data::variable parameter(const lps::specification& spec)
{
  return spec.process().process_parameters().front();
}

} // namespace

// A counter that is incremented under a range condition is split into one summand per value.
BOOST_AUTO_TEST_CASE(test_counter)
{
  const lps::specification spec = split_ranges("proc P(a: Nat) =\n"
                                               "     (0 < a && a < 3) -> tau . P(a + 1)\n"
                                               "   + (a == 3) -> tau . P(1);\n"
                                               "init P(1);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 3U);
  const data::variable a = parameter(spec);
  BOOST_CHECK(has_summand_with_conjunct(spec, data::equal_to(a, data::sort_nat::nat("1"))));
  BOOST_CHECK(has_summand_with_conjunct(spec, data::equal_to(a, data::sort_nat::nat("2"))));
}

// The bounds may also be given with >= and >, and the parameter may be on either side.
BOOST_AUTO_TEST_CASE(test_greater)
{
  const lps::specification spec = split_ranges("proc P(a: Pos) =\n"
                                               "     (a >= 2 && 5 > a) -> tau . P(a + 1)\n"
                                               "   + (a == 5) -> tau . P(2);\n"
                                               "init P(2);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 4U);
  const data::variable a = parameter(spec);
  BOOST_CHECK(has_summand_with_conjunct(spec, data::equal_to(a, data::sort_pos::pos("4"))));
}

// A summand that sets the parameter to a constant or leaves it unchanged is not split.
BOOST_AUTO_TEST_CASE(test_constant_update)
{
  const lps::specification spec = split_ranges("act a: Nat;\n"
                                               "proc P(a: Nat) =\n"
                                               "     (0 < a && a < 3) -> tau . P(0)\n"
                                               "   + (0 < a && a < 3) -> a(a) . P(a)\n"
                                               "   + (a == 0) -> tau . P(1);\n"
                                               "init P(1);\n");
  BOOST_CHECK_EQUAL(spec.process().action_summands().size(), 3U);
}

// A range with more values than the maximum is not split.
BOOST_AUTO_TEST_CASE(test_max_range)
{
  const std::string text = "proc P(a: Nat) =\n"
                           "     (0 < a && a < 5) -> tau . P(a + 1)\n"
                           "   + (a == 5) -> tau . P(1);\n"
                           "init P(1);\n";
  BOOST_CHECK_EQUAL(split_ranges(text, 3).process().action_summands().size(), 2U);
  BOOST_CHECK_EQUAL(split_ranges(text, 4).process().action_summands().size(), 5U);
}
