// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file linearise_new_test.cpp
/// \brief Some tests for the linearisation algorithms.

// TODO: This file is a test that should be part of the LPS library instead of
// the LTS library. However, from the LPS library we cannot generate an LTS.
// In general, generating LTSes and checking equivalence is a good way to test
// LPS transformations. We should find a better place for this test (and similar
// ones).

#include <cstddef>
#include <sstream>
#define BOOST_TEST_MODULE linearise_new_test
#include <boost/test/included/unit_test.hpp>

#include "mcrl2/lps/stochastic_specification.h"

#include "mcrl2/lps/linearise.h"
#include "mcrl2/lps/linearise_new.h"
#include "mcrl2/lps/parse.h"

#include "mcrl2/lts/lts_builder.h"
#include "mcrl2/lts/lts_algorithm.h"
#include "mcrl2/lts/lts_equivalence.h"
#include "mcrl2/lts/state_space_generator.h"
#include "mcrl2/process/action_name_multiset.h"
#include "mcrl2/process/communication_expression.h"
#include "mcrl2/process/detail/alphabet_parse.h"
#include "mcrl2/process/process_specification.h"
#include "mcrl2/utilities/test_utilities.h"



using namespace mcrl2;

inline std::string npar_action_declarations_text(const std::size_t N)
{
  std::stringstream npar_action_declarations;
  npar_action_declarations << "act\n";
  for (std::size_t i = 0; i < N; ++i)
  {
    if (i > 0)
    {
      npar_action_declarations << ",\n";
    }
    npar_action_declarations << "    a" << i << ", a" << i << "', a" << i << "''";
    npar_action_declarations << ", b" << i << ", b" << i << "', b" << i << "''";
    npar_action_declarations << ", c" << i;
  }
  npar_action_declarations << ";\n";
  return npar_action_declarations.str();
}

inline std::string npar_allow_set_text(const std::size_t N)
{
  std::stringstream allow_text;
  allow_text << "{";
  for (std::size_t i = 0; i < N; ++i)
  {
    if (i > 0)
    {
      allow_text << ", ";
    }
    allow_text << "a" << i << ", b" << i << "|b" << (i+2)%N << ", c" << i;
  }
  allow_text << "}";
  return allow_text.str();
}

inline std::string npar_comm_set_text(const std::size_t N)
{
  std::stringstream comm_text;
  comm_text << "{";
  for (std::size_t i = 0; i < N; ++i)
  {
    if (i > 0)
    {
      comm_text << ", ";
    }
    comm_text << "a" << i << "'|a" << i << "'' -> a" << i;
    // << ", ";
    //comm_text << "b" << i << "'|b" << i << "'' -> b" << i;
  }
  comm_text << "}";
  return comm_text.str();
}

inline std::string npar_process_text(const std::size_t i, const std::size_t N)
{
  std::stringstream process_text;

  process_text << "proc P" << i << " = a" << i << "' . P" << i << " + a" << (i + 1) % N << "'' . P" << i
               << " + b" << i << "' . P" << i << " + b" << (i + 2) % N << "'' . P" << i << " + c" << i << " . P" << i << ";\n";

  return process_text.str();
}

inline
std::string generate_npar_text(const std::size_t N)
{
  std::stringstream npar_spec;

  // action declarations
  npar_spec << npar_action_declarations_text(N);

  // processes
  for (std::size_t i = 0; i < N; ++i)
  {
    npar_spec << npar_process_text(i, N);
  }

  // initial process
  npar_spec << "init\n";
  npar_spec << "allow(" << npar_allow_set_text(N) << ",\n";
  npar_spec << "    comm(" << npar_comm_set_text(N) << ",\n";


  for (std::size_t i = 0; i < N; ++i)
  {
    if (i > 0)
    {
      npar_spec << " || ";
    }
    npar_spec << "P" << i;
  }
  npar_spec << "));\n";

  return npar_spec.str();
}

inline
process::action_label_list npar_action_declarations(const std::size_t N)
{
  return process::parse_action_declaration(npar_action_declarations_text(N));
}


/// \brief generate the process specification for linearization.
/// This allows testing with the old lineariser.
inline
process::process_specification npar_process_specification(const std::size_t N)
{
  std::string spec_text = generate_npar_text(N);
  std::cerr << spec_text << "\n";
  return process::parse_process_specification(spec_text);
}

inline
process::action_name_multiset_list npar_allow_actions(const std::size_t N)
{
  return process::detail::parse_allow_set(npar_allow_set_text(N));
}

inline
process::communication_expression_list npar_comm_actions(const std::size_t N)
{

  return process::detail::parse_comm_set(npar_comm_set_text(N));
}

inline
lps::specification npar_process(const std::size_t i, const std::size_t N)
{
  std::stringstream process_text;
  process_text << npar_action_declarations_text(N) << "\n";
  process_text << npar_process_text(i, N) << "\n";
  process_text << "init P" << i << ";\n";

  std::cerr << process_text.str() << "\n";
  return lps::parse_linear_process_specification(process_text);
}

inline
std::vector<lps::specification> npar_processes(const std::size_t N)
{
  std::vector<lps::specification> result;
  for (std::size_t i = 0; i < N; ++i)
  {
    result.emplace_back(npar_process(i, N));
  }
  return result;
}

// Similar to the function in linearization_instantiation_compare_test.cpp
template<class LTS_TYPE>
inline LTS_TYPE translate_lps_to_lts(const lps::specification& specification)
{
  lps::explorer_options options;
  options.trace_prefix = "lps_linearise_new_test";
  options.search_strategy = lps::es_breadth;
  options.save_at_end = true;
  const std::string& output_filename = utilities::temporary_filename("lps_linearise_new_test_file");

  LTS_TYPE result;
  data::rewriter rewr
    = lps::construct_rewriter(specification, options.rewrite_strategy, options.remove_unused_rewrite_rules);
  lps::explorer<false, false, lps::specification> explorer(specification, options, rewr);
  lts::state_space_generator<false, false, lps::specification> generator(specification, options, explorer);
  auto builder = create_lts_builder(specification, options, result.type());
  generator.explore(*builder);
  builder->save(output_filename);

  result.load(output_filename);
  return result;
}

/// \brief Linearise process specifications using the old lineariser.
/// The alphabet axioms are not applied and time is ignored to match the behaviour of the new lineariser.
inline
std::pair<lps::specification, long long> linearise_old(const process::process_specification& proc_spec)
{
  lps::t_lin_options lin_options;
  lin_options.ignore_time = true;
  lin_options.apply_alphabet_axioms = false;
  auto timestamp = std::chrono::system_clock::now();
  lps::stochastic_specification result = lps::linearise(proc_spec, lin_options);
  auto lin_duration
    = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - timestamp).count();
  std::cerr << "Old lineariser took " << lin_duration << " ms.\n";
  return {remove_stochastic_operators(result), lin_duration};
}

BOOST_AUTO_TEST_CASE(linearise_npar)
{
  std::cerr << "Testing for three processes\n";

  // Generate LPS using old lineariser based on process specification.
  process::process_specification proc_spec = npar_process_specification(3);
  std::pair<lps::specification, long long> old_result = linearise_old(proc_spec);

  // Generate LPS using new lineariser based on parallel processes.
  process::action_name_multiset_list allow_actions = npar_allow_actions(3);
  process::communication_expression_list comm_actions = npar_comm_actions(3);
  std::vector<lps::specification> processes = npar_processes(3);
  std::vector<lps::linearise_lpe> lpe_processes;
  std::transform(processes.begin(), processes.end(), std::back_inserter(lpe_processes),[](const lps::specification& spec)
  {
    return lps::linearise_lpe(spec.process(), spec.initial_process());
  });

  std::cerr << "Running new linearization\n";
  auto timestamp = std::chrono::system_clock::now();
  lps::linearise_lpe new_result = lps::linearise_new(allow_actions, comm_actions, lpe_processes);
  auto lin_duration
    = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - timestamp).count();
  std::cerr << "New lineariser took " << lin_duration << " ms.\n";

  lps::specification new_spec = lps::specification(proc_spec.data(), proc_spec.action_labels(), std::set<data::variable>(), new_result.lpe, new_result.initial_process);

  lts::lts_lts_t old_lts = translate_lps_to_lts<lts::lts_lts_t>(old_result.first);
  lts::lts_lts_t new_lts = translate_lps_to_lts<lts::lts_lts_t>(new_spec);

  BOOST_CHECK(lts::compare(new_lts, old_lts, lts::lts_eq_bisim));
}
