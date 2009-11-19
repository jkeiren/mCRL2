// Author(s): Jeroen Keiren, Jeroen van der Wulp, Jan Friso Groote
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/data_specification.h
/// \brief The class data_specification.

#include <algorithm>
#include <functional>
#include <iostream>
#include <map>

#include "boost/bind.hpp"
#include "boost/iterator/transform_iterator.hpp"

#include "mcrl2/atermpp/algorithm.h"
#include "mcrl2/atermpp/substitute.h"
#include "mcrl2/core/detail/soundness_checks.h"
#include "mcrl2/data/map_substitution.h"
#include "mcrl2/data/utility.h"
#include "mcrl2/data/data_specification.h"
#include "mcrl2/data/detail/sequence_algorithm.h"
#include "mcrl2/data/detail/data_utility.h"
#include "mcrl2/data/bool.h"
#include "mcrl2/data/pos.h"
#include "mcrl2/data/nat.h"
#include "mcrl2/data/int.h"
#include "mcrl2/data/real.h"
#include "mcrl2/data/list.h"
#include "mcrl2/data/set.h"
#include "mcrl2/data/bag.h"
#include "mcrl2/data/structured_sort.h"
#include "mcrl2/data/application.h"
#include "mcrl2/data/find.h"
#include "mcrl2/data/print.h"
#include "mcrl2/data/detail/internal_format_conversion.h"
#include "mcrl2/data/detail/dependent_sorts.h"

namespace mcrl2 {

  namespace data {
    /// \cond INTERNAL_DOCS
    namespace detail {

      /// \brief Specialised remove_if for manipulating std::set, std::map, std::multimap containers
      /* template < typename Container, typename Predicate >
      void remove_if(Container& container, Predicate p) 
      { Container temporary;
        std::remove_copy_if(container.begin(), container.end(), std::inserter(temporary, temporary.end()), p);
        container.swap(temporary);
      } */

      struct sort_map_substitution_adapter 
      { atermpp::map< sort_expression, sort_expression > const& m_map;
        atermpp::aterm_appl operator()(atermpp::aterm_appl a) 
        { if (is_sort_expression(a))
          { atermpp::map< sort_expression, sort_expression >::const_iterator i = m_map.find(sort_expression(a)); 
            if (i != m_map.end())
            { return i->second;
            }
          }
          return a;
        }

        sort_map_substitution_adapter(atermpp::map< sort_expression, sort_expression > const& map) : m_map(map)
        {}
      };

      /* template < typename Expression >
      inline bool is_system_defined(data_specification const& s, Expression const& c)
      {
        return s.is_system_defined(c);
      } */

      bool has_legacy_name(sort_expression const& s)
      { return is_basic_sort(s) && (std::string(basic_sort(s).name()).find("@legacy_") == 0);
      }

      atermpp::map< sort_expression, sort_expression > make_compatible_renaming_map(const data_specification& s)
      {
        // Generates names for a specification assuming that no sorts with name prefix @legacy_ exist
        struct legacy_name_generator 
        { std::set< basic_sort > m_generated;
          static std::string sort_name(const sort_expression& target)
          { if (target.is_container_sort())
            { return container_sort(target).container_type().function().name();
            }
            else
            { return "structured_sort";
            }
          }

          // \brief find `THE' identifier for a structured sort or container sort
          basic_sort generate_name(const sort_expression& target)
          { basic_sort generated(fresh_identifier(m_generated, std::string("@legacy_").append(sort_name(target))));
            m_generated.insert(generated);
            return generated;
          }
        } generator;

        atermpp::map< sort_expression, sort_expression > renamings;

        // Step one: fix a name for all container sorts (legacy requirement)
        /* for (data_specification::aliases_const_range r(s.aliases()); !r.empty(); r.advance_begin(1))
        {
          sort_expression reference(s.normalise_sorts(r.front().reference()));

          if (renamings.find(reference) == renamings.end())
          {
            for (atermpp::map< sort_expression, sort_expression >::iterator i = renamings.begin(); i != renamings.end(); ++i)
            {
              renamings[atermpp::replace(i->first, reference, r.front().name())] = i->second;
            }

            renamings[reference] = r.front().name();
          }
        } */

        for (data_specification::sorts_const_range r(s.sorts()); !r.empty(); r.advance_begin(1))
        { if (r.front().is_container_sort() || r.front().is_structured_sort())
          { if (renamings.find(r.front()) == renamings.end())
            { basic_sort name(generator.generate_name(r.front()));

              for (atermpp::map< sort_expression, sort_expression >::iterator i = renamings.begin(); i != renamings.end(); ++i)
              { renamings[atermpp::replace(i->first, r.front(), name)] = i->second;
              }

              renamings[r.front()] = name;
            }
          }
        }
        return renamings;
      }

      /// Compatible conversion to ATerm is needlessly complicated only to appease the type checker
      /// As a side effect data checked against the compatible specification
      /// may refer to names that do not exist at the level data_specification objects.
      /// This function reverts the naming to make data terms usable in combination with data_specification objects.
      /// \note temporary measure until a type checker at data level becomes available
      template < typename Term >
      Term apply_compatibility_renamings(const data_specification& s, Term const& term)
      { // Maps container sort expressions to a unique name
        atermpp::map< sort_expression, sort_expression > renamings(make_compatible_renaming_map(s));
        return atermpp::replace(term, sort_map_substitution_adapter(renamings));
      }

      template
      variable_list apply_compatibility_renamings(const data_specification& s, variable_list const& term);
      template
      atermpp::aterm_appl apply_compatibility_renamings(const data_specification& s, atermpp::aterm_appl const& term);

      template < typename Term >
      Term undo_compatibility_renamings(const data_specification& s, Term const& term)
      { // Maps container sort expressions to a unique name
        atermpp::map< sort_expression, sort_expression > renamings(make_compatible_renaming_map(s));
        atermpp::map< sort_expression, sort_expression > inverse_renamings;

        for (atermpp::map< sort_expression, sort_expression >::const_iterator i = renamings.begin(); i != renamings.end(); ++i)
        { inverse_renamings[i->second] = i->first;
        }

        return atermpp::replace(term, sort_map_substitution_adapter(inverse_renamings));
      }

      template
      variable_list undo_compatibility_renamings(const data_specification& s, variable_list const& term);
      template
      atermpp::aterm_appl undo_compatibility_renamings(const data_specification& s, atermpp::aterm_appl const& term);

      /**
       * \param[in] compatible whether the produced ATerm is compatible with the `format after type checking'
       *
       * The compatible transformation should eventually disappear, it is only
       * here for compatibility with the old parser, type checker and pretty
       * print implementations.
       **/
      atermpp::aterm_appl data_specification_to_aterm_data_spec(const data_specification& s, bool compatible)
      { using namespace core::detail;

        if (compatible)
        { atermpp::set< atermpp::aterm_appl > sorts;

          // Maps container sort expressions to a unique name
          atermpp::map< sort_expression, sort_expression > renamings(make_compatible_renaming_map(s));

          sort_map_substitution_adapter renaming_substitution(renamings);

          for (atermpp::map< sort_expression, sort_expression >::const_iterator i = renamings.begin(); i != renamings.end(); ++i)
          { if (detail::has_legacy_name(i->second))
            { sorts.insert(alias(i->second, i->first));
            }
          }

          for (data_specification::sorts_const_range r(s.m_sorts); !r.empty(); r.advance_begin(1))
          { if ((!r.front().is_basic_sort() || !s.is_alias(basic_sort(r.front()))) &&
			 !r.front().is_container_sort() && !r.front().is_structured_sort())
            { sorts.insert(r.front());
            }
          }

          return gsMakeDataSpec(
             gsMakeSortSpec(convert< atermpp::aterm_list >(s.m_sorts) + 
                            convert< atermpp::aterm_list >(data_specification::aliases_const_range(s.m_aliases))),
             gsMakeConsSpec(atermpp::replace(convert< atermpp::aterm_list >(
                                     data_specification::constructors_const_range(s.m_constructors)), renaming_substitution)),
             gsMakeMapSpec(atermpp::replace(convert< atermpp::aterm_list >(
                                     data_specification::constructors_const_range(s.m_mappings)), renaming_substitution)),
             gsMakeDataEqnSpec(atermpp::replace(convert< atermpp::aterm_list >(s.m_equations), renaming_substitution)));
        }
        else
        { return gsMakeDataSpec(
             gsMakeSortSpec(convert< atermpp::aterm_list >(s.m_sorts) +
                            convert< atermpp::aterm_list >(data_specification::aliases_const_range(s.m_aliases))),
             gsMakeConsSpec(convert< atermpp::aterm_list >(data_specification::constructors_const_range(s.m_constructors))),
             gsMakeMapSpec(convert< atermpp::aterm_list >(data_specification::constructors_const_range(s.m_mappings))),
             gsMakeDataEqnSpec(convert< atermpp::aterm_list >(s.m_equations)));
        }
      }
    } // namespace detail
    /// \endcond

    void data_specification::normalise_sorts() const
    { // Normalise the sorts of the constructors.
      m_normalised_sorts.clear();
      m_normalised_constructors.clear();
      m_normalised_mappings.clear();
      m_normalised_equations.clear();
      reconstruct_m_normalised_aliases();
      for(atermpp::set< sort_expression >::const_iterator i=m_sorts.begin();
           i!=m_sorts.end(); ++i)
      { m_normalised_sorts.insert(normalise_sorts(*i));
        import_system_defined_sort(*i);
      }

      for(atermpp::set< sort_expression >::const_iterator i=m_sorts_in_context.begin();
           i!=m_sorts_in_context.end(); ++i)
      { import_system_defined_sort(*i);
      }

      for(ltr_aliases_map ::const_iterator i=m_aliases.begin();  
           i!=m_aliases.end(); ++i)
      { m_normalised_sorts.insert(normalise_sorts(i->first));
        m_normalised_sorts.insert(normalise_sorts(i->second));
        import_system_defined_sort(i->first);
        import_system_defined_sort(i->second);
      }

      // sort_to_symbol_map new_constructors;
      for(sort_to_symbol_map::const_iterator i=m_constructors.begin();
           i!=m_constructors.end(); ++i)
      { const sort_expression normalised_sort=normalise_sorts(i->first);
        const function_symbol normalised_constructor=normalise_sorts(i->second);
        if (!search_constructor(normalised_constructor))
        { m_normalised_constructors.insert(std::pair<sort_expression, function_symbol>
                     (normalised_sort,normalised_constructor));
        }
        m_normalised_sorts.insert(normalised_sort);
      }

      // Normalise the sorts of the mappings.
      for(sort_to_symbol_map::const_iterator i=m_mappings.begin();
           i!=m_mappings.end(); ++i)
      { const sort_expression normalised_sort=normalise_sorts(i->first);
        const function_symbol normalised_mapping=normalise_sorts(i->second);
        if (!search_constructor(normalised_mapping))
        { m_normalised_mappings.insert((std::pair<sort_expression, function_symbol>
                      (normalised_sort,normalised_mapping)));
        }
        m_normalised_sorts.insert(normalised_sort);
      }
     
      // Normalise the sorts of the expressions and variables in equations.
      for(atermpp::set< data_equation >::const_iterator i=m_equations.begin();
           i!=m_equations.end(); ++i)
      { add_system_defined_equation(*i);
      }
    }

    /// \pre sort.is_system_defined()
    void data_specification::import_system_defined_sort(sort_expression const& sort) const
    { 
      const sort_expression normalised_sort=normalise_sorts(sort);
      // add sorts, constructors, mappings and equations
      if (normalised_sort == sort_bool::bool_())
      { sort_bool::add_bool_to_specification(*this);
      }
      else if (normalised_sort == sort_real::real_())
      { sort_real::add_real_to_specification(*this);
        import_system_defined_sort(sort_int::int_()); // A full definition of Int is required
                                                      // as the rewrite rules of Real rely on it.
      }
      else if (normalised_sort == sort_int::int_())
      { sort_int::add_int_to_specification(*this);
        import_system_defined_sort(sort_nat::nat());  // See above, Int requires Nat.
      }
      else if (normalised_sort == sort_nat::nat())
      { sort_nat::add_nat_to_specification(*this);
        import_system_defined_sort(sort_pos::pos());  // See above, Nat requires Pos.
      }
      else if (normalised_sort == sort_pos::pos())
      { sort_pos::add_pos_to_specification(*this);    
      }
      else
      { if (sort.is_container_sort())
        { sort_expression element_sort(container_sort(sort).element_sort());
          if (sort_list::is_list(sort))
          { sort_list::add_list_to_specification(*this, element_sort);
          }
          else if (sort_set::is_set(sort))
          { sort_set::add_set_to_specification(*this, element_sort);
          }
          else if (sort_bag::is_bag(sort))
          { sort_bag::add_bag_to_specification(*this, element_sort);
          }
        }
        else if (sort.is_structured_sort())
        { insert_mappings_constructors_for_structured_sort(sort);
        }
      }
      add_standard_mappings_and_equations(normalised_sort);
    }

    template < typename Container, typename Sequence >
    void insert(Container& container, Sequence sequence)
    { container.insert(sequence.begin(), sequence.end());
    }

    ///\brief Adds standard sorts when necessary
    ///
    /// Assumes that if constructors of a sort are part of the specification,
    /// then the sort was already imported.
    void data_specification::make_complete() const
    { std::set< sort_expression > dependent_sorts;

      // make sure that sort bool is part of the specification
      dependent_sorts.insert(sort_bool::bool_());

      // sorts
      // dependent_sorts.insert(m_sorts.begin(), m_sorts.end());

      // constructors
      insert(dependent_sorts, make_sort_range(constructors_const_range(m_constructors)));

      // mappings
      insert(dependent_sorts, make_sort_range(constructors_const_range(m_mappings)));

      // equations
      for (equations_const_range r(m_equations); !r.empty(); r.advance_begin(1))
      { // make function sort in case of constants to add the corresponding sort as needed
        insert(dependent_sorts, find_sort_expressions(r.front()));
      }

      // aliases, with both left and right hand sides.
      for(ltr_aliases_map::const_iterator i=m_aliases.begin();
                  i!=m_aliases.end(); ++i)
      { dependent_sorts.insert(i->first);
        insert(dependent_sorts,find_sort_expressions(i->second));
      } 

      m_sorts_in_context.insert(dependent_sorts.begin(),dependent_sorts.end());
      data_is_not_necessarily_normalised_anymore();
    }

    template < typename Term >
    void data_specification::gather_sorts(Term const& term, std::set< sort_expression >& sorts)
    {
      std::set< sort_expression > all_sorts;

      find_sort_expressions(term, std::inserter(all_sorts, all_sorts.end()));

      for (std::set< sort_expression >::const_iterator i = sorts.begin(); i != sorts.end(); ++i)
      { sorts.insert(normalise_sorts(*i));
      }
    }

    template void data_specification::gather_sorts< sort_expression >(sort_expression const&, std::set< sort_expression >&);
    template void data_specification::gather_sorts< data_expression >(data_expression const&, std::set< sort_expression >&);
    template void data_specification::gather_sorts< data_equation >(data_equation const&, std::set< sort_expression >&);
    template void data_specification::gather_sorts< function_symbol >(function_symbol const&, std::set< sort_expression >&);

    // Assumes that a system defined sort s is not (full) part of the specification if:
    //  - the set of sorts does not contain s
    //  - the specification has no constructors for s
    void data_specification::make_complete(std::set< sort_expression > const& sorts) const
    { atermpp::set < sort_expression >::size_type old_size=m_sorts_in_context.size();
      m_sorts_in_context.insert(sorts.begin(),sorts.end());
      if (m_sorts_in_context.size()!=old_size)
      { data_is_not_necessarily_normalised_anymore();
      } 
    }

    void data_specification::make_complete(data_expression const& e) const
    { make_complete(find_sort_expressions(e));
    }

    void data_specification::make_complete(data_equation const& e) const
    { make_complete(find_sort_expressions(e));
    }

    void data_specification::make_complete(sort_expression const& s) const
    { atermpp::set < sort_expression >::size_type old_size=m_sorts_in_context.size();
      m_sorts_in_context.insert(s);

      if (m_sorts_in_context.size()!=old_size)
      { data_is_not_necessarily_normalised_anymore();
      }
    }

    class finiteness_helper 
    { protected:

        typedef std::set< sort_expression >             dependent_sort_set;
        data_specification const&                       m_specification;
        std::map< sort_expression, dependent_sort_set > m_dependent_sorts;
        std::multiset< sort_expression >                m_visiting;
        dependent_sort_set const& dependent_sorts(sort_expression const& s)
        {
          std::map< sort_expression, dependent_sort_set >::iterator i = m_dependent_sorts.find(s);
          if (i == m_dependent_sorts.end())
          {
            i = m_dependent_sorts.insert(i, std::make_pair(s, static_cast< dependent_sort_set const& >(
						data::find_dependent_sorts(m_specification, s))));
          }
          return i->second;
        }

        bool search(dependent_sort_set const& source, sort_expression const& s)
        {
          return source.find(s) != source.end();
        }

      public:

        finiteness_helper(data_specification const& specification) : m_specification(specification)
        { }

        bool is_finite(const sort_expression& s)
        {
          if (s.is_basic_sort())
          {
            return is_finite(basic_sort(s));
          }
          else if (s.is_container_sort())
          {
            return is_finite(container_sort(s));
          }
          else if (s.is_function_sort())
          {
            return is_finite(function_sort(s));
          }
          else if (s.is_structured_sort())
          {
            return is_finite(structured_sort(s));
          }

          return false;
        }

        bool is_finite(const basic_sort& s)
        {
          // sort_expression actual_sort = m_specification.find_referenced_sort(s);
          sort_expression actual_sort = s;

          if (actual_sort != s)
          {
            return is_finite(actual_sort);
          }
          else {
            m_visiting.insert(s);

            for (data_specification::constructors_const_range r(m_specification.constructors(s)); !r.empty(); r.advance_begin(1))
            {
              if (r.front().sort().is_function_sort())
              {
                for (boost::iterator_range< dependent_sort_set::const_iterator > c(dependent_sorts(r.front().sort())); !c.empty(); c.advance_begin(1))
                {
                  if (!c.front().is_function_sort())
                  {
                    if ((c.front() == s) || (m_visiting.find(c.front()) == m_visiting.end() && !is_finite(c.front())))
                    {
                      return false;
                    }
                  }
                }
              }
            }

            m_visiting.erase(m_visiting.find(s));
          }

          return !search(dependent_sorts(s), s) && !m_specification.constructors(actual_sort).empty();
        }

        bool is_finite(const function_sort& s)
        {
          for (boost::iterator_range< function_sort::domain_const_range::iterator > i(s.domain()); !i.empty(); i.advance_begin(1))
          {
            if (m_visiting.find(i.front()) == m_visiting.end() && !is_finite(i.front()))
            {
              return false;
            }
          }

          return (s.codomain() != s) ? is_finite(s.codomain()) : false;
        }

        bool is_finite(const container_sort& s)
        {
          return (s.is_set_sort()) ? is_finite(s.element_sort()) : false;
        }

        bool is_finite(const alias& s)
        {
          return is_finite(s.reference());
        }

        bool is_finite(const structured_sort& s)
        {
          m_visiting.insert(s);

          for (boost::iterator_range< dependent_sort_set::const_iterator > c(dependent_sorts(s)); !c.empty(); c.advance_begin(1))
          {
            if (m_visiting.find(c.front()) == m_visiting.end() && !is_finite(c.front()))
            {
              return false;
            }
          }

          m_visiting.erase(m_visiting.find(s));

          return true;
        }
    };

    /// \brief Checks whether a sort is certainly finite.
    ///
    /// \param[in] s A sort expression
    /// \return true if s can be determined to be finite,
    ///      false otherwise.
    bool data_specification::is_certainly_finite(const sort_expression& s) const
    {
      return finiteness_helper(*this).is_finite(s);
    }

    bool data_specification::is_well_typed() const
    {
      // check 1)
      if (!detail::check_data_spec_sorts(constructors(), m_sorts))
      {
        std::clog << "data_specification::is_well_typed() failed: not all of the sorts appearing in the constructors "
                  << pp(constructors()) << " are declared in " << pp(m_sorts) << std::endl;
        return false;
      }

      // check 2)
      if (!detail::check_data_spec_sorts(mappings(), m_sorts))
      {
        std::clog << "data_specification::is_well_typed() failed: not all of the sorts appearing in the mappings "
                  << pp(mappings()) << " are declared in " << pp(m_sorts) << std::endl;
        return false;
      }

      return true;
    }

                /*****************************************/
                /*                                       */
                /*  m_normalised_aliases_are_up_to_date  */
                /*                                       */
                /*****************************************/

    void data_specification::reconstruct_m_normalised_aliases() const
    { 
     // First reset the normalised aliases and the mappings and constructors that have been
     // inherited to basic sort aliases during a previous round of sort normalisation.
     m_normalised_aliases.clear(); 

     // Copy m_normalised_aliases. Simple aliases are stored from left to 
     // right. If the right hand side is non trivial (struct, list, set or bag)
     // the alias is stored from right to left.
     for(ltr_aliases_map::const_iterator i=m_aliases.begin();
               i!=m_aliases.end(); ++i)
     { assert(m_normalised_aliases.count(i->first)==0); // sort aliases have a unique left hand side.
       if (is_structured_sort(i->second) ||
           is_function_sort(i->second) ||
           is_container_sort(i->second))
       { // We deal here with a declaration of the shape sort A=ComplexType.
         // Rewrite every occurrence of ComplexType to A. Suppose that there are
         // two declarations of the shape sort A=ComplexType; B=ComplexType then
         // ComplexType is rewritten to A and B is also rewritten to A.
         const atermpp::map< sort_expression, sort_expression >::const_iterator j=m_normalised_aliases.find(i->second);
         if (j!=m_normalised_aliases.end())
         { m_normalised_aliases[i->first]=j->second;
         }
         else 
         { m_normalised_aliases[i->second]=i->first;
         }
       }
       else
       { // We are dealing with a sort declaration of the shape sort A=B.
         // Every occurrence of sort A is normalised to sort B.
         assert(is_basic_sort(i->first));
         m_normalised_aliases[i->first]=i->second;
       }
     }

     // Close the mapping m_normalised_aliases under itself. If a rewriting
     // loop is detected, throw a runtime error.

     for(atermpp::map< sort_expression, sort_expression >::iterator i=m_normalised_aliases.begin();
              i!=m_normalised_aliases.end(); i++)
     { std::set < sort_expression > sort_already_seen;
       sort_expression result_sort=i->second;

       std::set< sort_expression > all_sorts;
       if (is_container_sort(i->first) || is_function_sort(i->first))
       { find_sort_expressions(i->first, std::inserter(all_sorts, all_sorts.end()));
       }
       while (m_normalised_aliases.count(result_sort)>0)
       { sort_already_seen.insert(result_sort);
         result_sort= m_normalised_aliases.find(result_sort)->second;
         if (sort_already_seen.count(result_sort))
         { mcrl2::runtime_error("Sort alias " + pp(result_sort) + " is defined in terms of itself.");
         }

         for (std::set< sort_expression >::const_iterator j = all_sorts.begin(); j != all_sorts.end(); ++j)
         { if (*j==result_sort)
           { mcrl2::runtime_error("Sort alias " + pp(i->first) + " depends on sort" +
                                           pp(result_sort) + ", which is circularly defined.\n");
           }
         }
       }
       // So the normalised sort of i->first is result_sort. 
       i->second=result_sort;
     }
    }

    /* template <typename Object> Object data_specification::normalise_sorts(const Object& o) const
    { 
      std::cerr << "Object " << o << "\n";
      substitution < Object, sort_expression, Object > sigma(m_normalised_aliases);
      return sigma(o);
    } */

    sort_expression data_specification::normalise_sorts_helper(const sort_expression & e) const
    { // Check whether e has already a normalised sort
      // If yes return it.
      const atermpp::map< sort_expression, sort_expression >::const_iterator i=m_normalised_aliases.find(e);
      if (i!=m_normalised_aliases.end())
      { 
        return i->second;
      }

      if (e.is_basic_sort())
      { // Apparently, e is already a normalised sort.
        return e;
      }
      else if (e.is_function_sort())
      { 
        atermpp::vector< sort_expression > new_domain;
        for (boost::iterator_range< function_sort::domain_const_range::iterator > r(function_sort(e).domain()); 
                  !r.empty(); r.advance_begin(1))
        { new_domain.push_back(normalise_sorts_helper(r.front()));
        }
        return function_sort(new_domain, normalise_sorts_helper(function_sort(e).codomain()));
      }
      else if (e.is_container_sort())
      { return container_sort(container_sort(e).container_type(), normalise_sorts_helper(container_sort(e).element_sort()));
      }
      else if (e.is_structured_sort())
      { atermpp::vector< structured_sort_constructor > new_constructors;
        for (structured_sort::constructors_const_range r(structured_sort(e).struct_constructors()); !r.empty(); r.advance_begin(1))
        { atermpp::vector< structured_sort_constructor_argument > new_arguments;
          for (structured_sort_constructor::arguments_const_range ra(r.front().arguments()); !ra.empty(); ra.advance_begin(1))
          { new_arguments.push_back(structured_sort_constructor_argument(normalise_sorts_helper(ra.front().sort()), ra.front().name()));
          }
          new_constructors.push_back(structured_sort_constructor(r.front().name(), new_arguments, r.front().recogniser()));
        }
        return structured_sort(new_constructors);
      }
      return e;
    } 

    sort_expression data_specification::normalise_sorts(const sort_expression & e) const
    { normalise_specification_if_required();
      return normalise_sorts_helper(e);
    }

    function_symbol data_specification::normalise_sorts(function_symbol const& f) const
    { normalise_specification_if_required();
      return function_symbol(f.name(),normalise_sorts(f.sort()));
    }

    data_expression data_specification::normalise_sorts(data_expression const& e) const
    { normalise_specification_if_required();
      if (e.is_abstraction())
      { const abstraction a(e);
        const abstraction::variables_const_range variables=a.variables();
        variable_vector normalised_variables;
        for(abstraction::variables_const_range::const_iterator i=variables.begin();
              i!=variables.end(); ++i)
        { normalised_variables.push_back(variable(i->name(),normalise_sorts(i->sort())));
        }
        
        return abstraction(a.binding_operator(),normalised_variables,normalise_sorts(a.body()));
      }
      if (e.is_application())
      { const application a(e);
        const application::arguments_const_range args=a.arguments();
        data_expression_vector normalised_arguments;
        for(application::arguments_const_range::const_iterator i=args.begin();
            i!=args.end(); ++i)
        { normalised_arguments.push_back(normalise_sorts(*i));
        }
        return application(normalise_sorts(a.head()),normalised_arguments);
      }
      if (e.is_function_symbol())
      { return function_symbol(function_symbol(e).name(),normalise_sorts(e.sort()));
      }
      /* if (e.is_list_expression())
      { return 
      } */
      if (e.is_variable())
      { return variable(variable(e).name(),normalise_sorts(e.sort()));
      }
      assert(e.is_where_clause());
      const where_clause w(e);
      const where_clause::declarations_const_range decls=w.declarations();
      assignment_vector normalised_assignments;
      for(atermpp::term_list <assignment>::const_iterator i=decls.begin();
             i!=decls.end(); ++i)
      { const variable v=i->lhs();
        const data_expression exp=i->rhs();
        normalised_assignments.push_back(assignment(normalise_sorts(v),normalise_sorts(exp)));
      }
      
      return where_clause(normalise_sorts(w.body()),normalised_assignments);
    }
    /// \endcond

    /// There are two types of representations of ATerms:
    ///  - the bare specification that does not contain constructor, mappings
    ///    and equations for system defined sorts
    ///  - specification that includes all system defined information (legacy)
    /// The last type must eventually dissapear but is unfortunately still in
    /// use in a substantial amount of source code.
    /// Note, all sorts with name prefix @legacy_ are eliminated
    void data_specification::build_from_aterm(atermpp::aterm_appl const& term)
    { 
      assert(core::detail::check_rule_DataSpec(term));

      // Note backwards compatibility measure: alias is no longer a sort_expression
      atermpp::term_list< atermpp::aterm_appl >  term_sorts(atermpp::list_arg1(atermpp::arg1(term)));
      atermpp::term_list< function_symbol >      term_constructors(atermpp::list_arg1(atermpp::arg2(term)));
      atermpp::term_list< function_symbol >      term_mappings(atermpp::list_arg1(atermpp::arg3(term)));
      atermpp::term_list< data_equation >        term_equations(atermpp::list_arg1(atermpp::arg4(term)));

      // Store the sorts and aliases.
      for (atermpp::term_list_iterator< atermpp::aterm_appl > i = term_sorts.begin(); i != term_sorts.end(); ++i)
      { if (data::is_alias(*i)) // Compatibility with legacy code
        { if (!detail::has_legacy_name(alias(*i).name()))
          { add_alias(*i);
          }
        }
        else 
        { m_sorts.insert(*i);
        } 
      }

      // Store the constructors.
      for (atermpp::term_list_iterator< function_symbol > i = term_constructors.begin(); i != term_constructors.end(); ++i)
      { assert(!search_constructor(*i));
        assert(!search_mapping(*i));
        m_constructors.insert(sort_to_symbol_map::value_type(i->sort().target_sort(), *i));
      }

      // Store the mappings.
      for (atermpp::term_list_iterator< function_symbol > i = term_mappings.begin(); i != term_mappings.end(); ++i)
      { assert(!search_constructor(*i));
        assert(!search_mapping(*i));
        m_mappings.insert(sort_to_symbol_map::value_type(i->sort().target_sort(), *i));
      }

      // Store the equations.
      for (atermpp::term_list_iterator< data_equation > i = term_equations.begin(); i != term_equations.end(); ++i)
      { m_equations.insert(*i);
      }

    }
  } // namespace data
} // namespace mcrl2

