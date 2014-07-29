// Author(s): Gijs Kant
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/pbes_explorer.cpp
/// \brief
#include <queue>
#include <set>

#include "mcrl2/atermpp/detail/utility.h"
#include "mcrl2/data/rewrite_strategy.h"
#include "mcrl2/data/representative_generator.h"
#include "mcrl2/pbes/io.h"
#include "mcrl2/pbes/algorithms.h"
#include "mcrl2/pbes/pbes_explorer.h"
#include "mcrl2/pbes/detail/ppg_visitor.h"

using namespace atermpp;
using namespace mcrl2;
using namespace mcrl2::pbes_system;
using namespace mcrl2::pbes_system::detail;
using namespace mcrl2::core;
using namespace mcrl2::data;

namespace mcrl2
{

namespace pbes_system
{

namespace detail
{
  template <typename MapContainer>
  typename MapContainer::mapped_type map_at(const MapContainer& m, typename MapContainer::key_type key)
  {
    typename MapContainer::const_iterator i = m.find(key);
    if (i == m.end())
    {
      throw mcrl2::runtime_error("map_at: key is not present in the map: " + key);
    }
    return i->second;
  }
}

/// lts_type

lts_type::lts_type(int state_length)
{
    this->state_length = state_length;
}


lts_type::~lts_type()
{}


int lts_type::get_state_length() const
{
    return this->state_length;
}


int lts_type::get_number_of_state_types() const
{
    return this->state_type_list.size();
}


int lts_type::get_state_type_no(int part) const
{
    return this->state_type_no.at(part);
}

std::string lts_type::get_state_type_name(int type_no) const
{
    return this->state_type_list.at(type_no);
}

const std::vector<std::string>& lts_type::get_state_names() const
{
    return state_names;
}


const std::vector<std::string>& lts_type::get_state_types() const
{
    return state_types;
}


size_t lts_type::get_number_of_state_labels() const
{
    return this->state_label_names.size();
}


const std::vector<std::string>& lts_type::get_state_labels() const
{
    return state_label_names;
}


const std::vector<std::string>& lts_type::get_state_label_types() const
{
    return state_label_types;
}


size_t lts_type::get_number_of_edge_labels() const
{
    return this->edge_label_names.size();
}


const std::vector<std::string>& lts_type::get_edge_labels() const
{
    return edge_label_names;
}


const std::vector<std::string>& lts_type::get_edge_label_types() const
{
    return edge_label_types;
}


void lts_type::add_state(const std::string& name, const std::string& type)
{
    //std::clog << "Adding state part " << this->state_names->size() << ": "
    //        << info::get_param_signature(name, type)
    //        << std::endl;
    this->state_names.push_back(name);
    this->state_types.push_back(type);
    int type_index;
    std::map<std::string,int>::iterator type_index_it = this->state_type_index.find(type);
    if (type_index_it != this->state_type_index.end()) {
        type_index = type_index_it->second;
    } else {
        this->state_type_list.push_back(type);
        type_index = this->state_type_list.size() - 1;
        this->state_type_index[type] = type_index;
    }
    this->state_type_no.push_back(type_index);
    //std::clog << "  type_no = " << type_index << ": " << this->state_type_list->at(type_index) << std::endl;
}


void lts_type::add_state_label(const std::string& name,
                                  const std::string& type)
{
    this->state_label_names.push_back(name);
    this->state_label_types.push_back(type);
}


void lts_type::add_edge_label(const std::string& name,
                                 const std::string& type)
{
    this->edge_label_names.push_back(name);
    this->edge_label_types.push_back(type);
}




/// lts_info

lts_info::lts_info(pbes& p, pbes_greybox_interface* pgg, bool reset = false, bool always_split = false):
    p(p),
    pgg(pgg),
    reset_option(reset),
    always_split_option(always_split),
    type(0)
{
    if (!is_ppg(p))
    {
        throw std::runtime_error("PBES is not a PPG! Please rewrite with pbesrewr -pppg.");
    }
    //std::clog << "info: resetOption = " << (this->resetOption ? "true":"false") << ", reset = " << reset << std::endl;
    compute_lts_type();
    compute_transition_groups();
    compute_dependency_matrix();
}


void lts_info::compute_lts_type()
{
    //std::clog << "pbes_type:" << std::endl;
    mCRL2log(log::verbose) << "Compute LTS type." << std::endl;
    std::vector<std::string> params;
    std::map<std::string,std::string> paramtypes;
    data::representative_generator default_expression_generator(p.data());

    for (std::vector<pbes_equation>::iterator eqn = p.equations().begin(); eqn
            != p.equations().end(); ++eqn) {
        //std::clog << core::pp((*eqn).symbol()) << " " << (*eqn).variable().name()
        //        << std::endl;

        propositional_variable var = (*eqn).variable();
        for (atermpp::term_list<variable>::const_iterator param =
                var.parameters().begin(); param != var.parameters().end(); ++param) {
            variable varparam = (*param);
            std::string signature = get_param_signature(varparam);
            bool new_param = true;
            for (std::vector<std::string>::iterator par = params.begin(); par
                        != params.end(); ++par) {
               if (signature == (*par)) new_param = false;
            }
            if (new_param) {
                params.push_back(signature);
                paramtypes[signature] = core::pp(varparam.sort());
                //std::clog << "paramtypes[" << signature << "] = " << paramtypes[signature] << std::endl;
                data_expression e(default_expression_generator(varparam.sort()));
                pbes_expression e1 = pgg->rewrite_and_simplify_expression(e,false);
                this->param_default_values.push_back(atermpp::down_cast<const data::data_expression>(e1));
            }
        }
        //params.sort();
    }
    this->type = lts_type(1 + params.size());
    this->type.add_state("var", "string"); // Propositional variable name

    int i = 0;
    for (std::vector<std::string>::iterator param = params.begin(); param
            != params.end(); ++param) {
        std::string signature = (*param);
        this->type.add_state(signature, paramtypes[signature]);
        this->param_index[signature] = i;
        i++;
    }

    this->type.add_state_label("priority", "int");
    this->type.add_state_label("type", "int");

    //this->type->add_edge_label("", "");
    //std::clog << "-- end of pbes_type." << std::endl;
    mCRL2log(log::verbose) << "end of compute_lts_type." << std::endl;
}


inline bool lts_info::is_pass_through_state(propositional_variable_instantiation propvar)
{
    std::string varname = std::string(propvar.name());
    data::variable_list params = this->variable_parameters[varname];
    data::data_expression_list values = propvar.parameters();
    if (params.size() != values.size())
    {
        return false;
    }
    else
    {
        data::variable_list::const_iterator param_it = params.begin();
        for(data::data_expression_list::const_iterator value_it = values.begin(); value_it != values.end(); ++value_it)
        {
            if (!tr::is_variable(*value_it))
            {
                return false;
            }
            else
            {
                data::variable param(*param_it);
                data::variable param_expr(*value_it);
                if (param != param_expr)
                {
                    return false;
                }
            }
            if (param_it != params.end())
            {
                ++param_it;
            }
        }
    }
    return true;
}


inline int lts_info::count_variables(pbes_expression e)
{
    if (tr::is_prop_var(e))
    {
        return 1;
    }
    else if (tr::is_and(e) || tr::is_or(e) || tr::is_imp(e))
    {
        return count_variables(tr::left(e)) + count_variables(tr::right(e));
    }
    else if (tr::is_forall(e) || tr::is_exists(e))
    {
        if (count_variables(tr::arg(e)) > 0)
        {
            return INT_MAX;
        }
        else
        {
            return 0;
        }
    }
    else if (tr::is_not(e))
    {
        return count_variables(tr::arg(e));
    }
    else if (tr::is_data(e))
    {
        return 0;
    }
    else
    {
        throw(std::runtime_error("Unexpected expression: " + pbes_system::pp(e)));
    }
}

std::vector<pbes_expression> lts_info::split_expression_and_substitute_variables(pbes_expression e, int current_priority, operation_type current_type, std::set<std::string> vars_stack)
{
    std::vector<pbes_expression> result;
    std::vector<pbes_expression> parts;
    if (is_simple_expression(e))
    {
        result.push_back(e);
    }
    else if (!tr::is_prop_var(e) && count_variables(e) <= 1 && !always_split_option)
    {
        result.push_back(e);
    }
    else if (tr::is_and(e)) {
        parts = pbes_expr::split_conjuncts(e, true);
    } else if (tr::is_or(e)) {
        parts = pbes_expr::split_disjuncts(e, true);
    } else {
        parts.push_back(e);
    }

    bool pass_through = true;

    for(std::vector<pbes_expression>::iterator p_it = parts.begin(); pass_through && p_it != parts.end(); ++p_it)
    {
        pbes_expression part = *p_it;
        if (tr::is_prop_var(part))
        {
            // Try to substitute the variable instantiation with the associated expression

            propositional_variable_instantiation propvar = (propositional_variable_instantiation)part;
            if (is_pass_through_state(propvar))
            {
                // The variable instantiation only copies the current parameters and local data variables,
                // so substitution is safe with respect to that.

                std::string varname = std::string(propvar.name());
                int priority = this->variable_priority[varname];
                operation_type type = this->variable_type[varname];
                pbes_expression expr = this->variable_expression[varname];

                if ((priority == current_priority) &&
                    (current_type == type || is_simple_expression(expr) || count_variables(expr) <= 1) &&
                    vars_stack.find(varname) == vars_stack.end())
                {
                    // The associated equation has the same priority and operation type as the current equation,
                    // so substitution is safe.

                    //std::clog << "    Substituting variable instantiation: " << pbes_system::pp(part) << std::endl
                    //          << "      with: " << pbes_system::pp(expr) << std::endl;

                    // Recursively try to further substitute variables:
                    // (vars_stack is used to prevent infinite recursion)
                    std::set<std::string> new_vars_stack(vars_stack.begin(), vars_stack.end());
                    new_vars_stack.insert(varname);
                    std::vector<pbes_expression> part_result = split_expression_and_substitute_variables(expr, current_priority, current_type, new_vars_stack);
                    result.insert(result.end(), part_result.begin(), part_result.end());
                }
                else
                {
                    result.push_back(part);
                }
            }
            else
            {
                pass_through = false;
            }
        }
        else
        {
            pass_through = false;
        }
    }
    if (!pass_through)
    {
        if (always_split_option && !parts.empty())
        {
            // the old behaviour of the explorer: always split conjunctions and disjunctions
            // into subexpressions that form groups
            result = parts;
        }
        else
        {
            // the new behaviour: only split expressions if every part is a pass-through variable instantiation,
            // i.e., all values are copied and not changed.
            result.clear();
            result.push_back(e);
        }
    }
    return result;
}


void lts_info::compute_transition_groups()
{
    mCRL2log(log::verbose) << "Compute transition groups." << std::endl;

    int group = 0;
    int priority = 0;
    operation_type type = parity_game_generator::PGAME_AND;
    fixpoint_symbol symbol = fixpoint_symbol::nu();
    ppg_visitor checker;

    std::string name = "true";
    propositional_variable t(name);
    this->variables[name] = t;
    this->variable_type[name] = type;
    this->variable_symbol[name] = symbol;
    this->variable_priority[name] = priority;
    this->variable_parameters[name] = t.parameters();
    this->variable_parameter_signatures[name] = get_param_sequence(t.parameters());
    this->variable_parameter_indices[name] = this->get_param_indices(t.parameters());
    this->variable_parameter_index_positions[name] = this->get_param_index_positions(t.parameters());
    this->transition_expression_plain.push_back(tr::true_());
    this->transition_expression.push_back(pgg->rewrite_and_simplify_expression(tr::true_()));
    this->transition_variable_name.push_back(name);
    this->transition_type.push_back(type);
    group++;
    priority++;

    name = "false";
    type = parity_game_generator::PGAME_OR;
    symbol = fixpoint_symbol::mu();
    propositional_variable f(name);
    this->variables[name] = f;
    this->variable_type[name] = type;
    this->variable_symbol[name] = symbol;
    this->variable_priority[name] = priority;
    this->variable_parameters[name] = f.parameters();
    this->variable_parameter_signatures[name] = get_param_sequence(f.parameters());
    this->variable_parameter_indices[name] = this->get_param_indices(f.parameters());
    this->variable_parameter_index_positions[name] = this->get_param_index_positions(f.parameters());
    this->transition_expression_plain.push_back(tr::false_());
    this->transition_expression.push_back(pgg->rewrite_and_simplify_expression(tr::false_()));
    this->transition_variable_name.push_back(name);
    this->transition_type.push_back(type);
    group++;
    priority++;

    symbol = fixpoint_symbol::nu();

    for (std::vector<pbes_equation>::iterator eqn = p.equations().begin(); eqn
            != p.equations().end(); ++eqn) {
        pbes_expression expr = pgg->get_pbes_equation((*eqn).variable().name()).formula();
        std::string variable_name = (*eqn).variable().name();
        this->variables[variable_name] = (*eqn).variable();
        type = pgg->get_expression_operation(expr);
        this->variable_type[variable_name] = type;
        this->variable_symbol[variable_name] = (*eqn).symbol();
        if ((*eqn).symbol() != symbol) {
            priority++;
            symbol = (*eqn).symbol();
        }
        mCRL2log(log::verbose) << "Adding var " << variable_name << ", priority=" << priority << ", symbol=" << symbol << std::endl;
        this->variable_priority[variable_name] = priority;
        this->variable_parameters[variable_name] = (*eqn).variable().parameters();
        this->variable_parameter_signatures[variable_name] = get_param_sequence((*eqn).variable().parameters());
        this->variable_parameter_indices[variable_name] = this->get_param_indices((*eqn).variable().parameters());
        this->variable_parameter_index_positions[variable_name] = this->get_param_index_positions((*eqn).variable().parameters());
        this->variable_expression[variable_name] = expr;
    }

    // Skip 'unused' equations....
    std::set<std::string> variable_set;
    {
        propositional_variable_instantiation init = p.initial_state();
        std::queue<std::string> variable_queue;
        variable_queue.push(init.name());
        variable_set.insert(init.name());
        while (!variable_queue.empty())
        {
            std::string var = variable_queue.front();
            variable_queue.pop();
            type = this->variable_type[var];
            priority = this->variable_priority[var];
            pbes_expression expr = this->variable_expression[var];
            std::set<std::string> vars_stack;
            std::vector<pbes_expression> expression_parts = split_expression_and_substitute_variables(expr, priority, type, vars_stack);
            for (std::vector<pbes_expression>::const_iterator e =
                    expression_parts.begin(); e != expression_parts.end(); ++e) {
                 std::set<std::string> occ_vars = lts_info::occ(*e);
                 for (std::set<std::string>::const_iterator var_str = variable_set.begin(); var_str != variable_set.end(); ++var_str)
                 {
                   occ_vars.erase(*var_str);
                 }
                 for(std::set<std::string>::const_iterator occ_var = occ_vars.begin(); occ_var != occ_vars.end(); ++occ_var)
                 {
                     variable_queue.push(*occ_var);
                 }
                 variable_set.insert(occ_vars.begin(), occ_vars.end());
            }
        }
        mCRL2log(log::debug) << "Set of 'used' variables: " << std::endl;
        for (std::set<std::string>::const_iterator var_str = variable_set.begin(); var_str != variable_set.end(); ++var_str)
        {
            mCRL2log(log::debug) << "  " << (*var_str) << std::endl;
        }
        mCRL2log(log::debug) << std::endl;
    }

    for (std::vector<pbes_equation>::iterator eqn = p.equations().begin(); eqn
            != p.equations().end(); ++eqn) {
        std::string variable_name = (*eqn).variable().name();
        if (variable_set.find(variable_name) != variable_set.end())
        {
            type = this->variable_type[variable_name];
            priority = this->variable_priority[variable_name];
            pbes_expression expr = this->variable_expression[variable_name];
            std::set<std::string> vars_stack;
            //std::clog << std::endl << "Generating groups for equation " << variable_name << std::endl;
            std::vector<pbes_expression> expression_parts = split_expression_and_substitute_variables(expr, priority, type, vars_stack);
            for (std::vector<pbes_expression>::const_iterator e =
                    expression_parts.begin(); e != expression_parts.end(); ++e) {
                this->transition_expression_plain.push_back(*e);
                this->transition_expression.push_back(pgg->rewrite_and_simplify_expression(*e));
                this->transition_variable_name.push_back(variable_name);
                this->transition_type.push_back(type);
                mCRL2log(log::debug) << "Add transition group " << group << ": "
                        << (type==parity_game_generator::PGAME_AND ? "AND" : "OR") << " " << variable_name << " "
                        << pbes_system::pp(*e) << std::endl;
                group++;
            }
        }
    }
    number_of_groups = group;
    //std::clog << "Added " << group << " transition groups." << std::endl;
    mCRL2log(log::debug) << "end of compute_transition_groups." << std::endl;
}


void lts_info::compute_dependency_matrix()
{
    mCRL2log(log::verbose) << "Compute dependency matrix." << std::endl;
    for(int group=0; group < number_of_groups; group++)
    {
        std::vector<bool> dep_row;
        std::vector<bool> read_row;
        std::vector<bool> write_row;
        bool r = is_read_dependent_propvar(group);
        bool w = is_write_dependent_propvar(group);
        bool d = r || w;
        dep_row.push_back(d);
        read_row.push_back(r);
        write_row.push_back(w);
        for (int part = 1; part < type.get_state_length(); part++)
        {
            r = is_read_dependent_parameter(group, part);
            w = is_write_dependent_parameter(group, part);
            d = r || w;
            dep_row.push_back(d);
            read_row.push_back(r);
            write_row.push_back(w);
        }
        matrix[group] = dep_row;
        read_matrix[group] = read_row;
        write_matrix[group] = write_row;
    }
    mCRL2log(log::verbose) << "end of compute_dependency_matrix." << std::endl;
}


bool lts_info::get_reset_option() const
{
    return reset_option;
}


int lts_info::get_number_of_groups() const
{
    return number_of_groups;
}


const std::vector<pbes_expression>& lts_info::get_transition_expressions() const
{
    return transition_expression;
}


const std::vector<std::string>& lts_info::get_transition_variable_names() const
{
    return transition_variable_name;
}


const std::vector<lts_info::operation_type>& lts_info::get_transition_types() const
{
    return transition_type;
}


const std::map<std::string, propositional_variable>& lts_info::get_variables() const
{
    return variables;
}


const std::map<std::string, lts_info::operation_type>& lts_info::get_variable_types() const
{
    return variable_type;
}

const std::map<std::string, fixpoint_symbol>& lts_info::get_variable_symbols() const
{
    return variable_symbol;
}


const std::map<std::string, int>& lts_info::get_variable_priorities() const
{
    return variable_priority;
}


const std::map<std::string, data::variable_list>& lts_info::get_variable_parameters() const
{
    return variable_parameters;
}


const std::map<std::string, std::vector<std::string> >& lts_info::get_variable_parameter_signatures() const
{
    return variable_parameter_signatures;
}


const std::map<std::string, std::vector<int> >& lts_info::get_variable_parameter_indices() const
{
    return variable_parameter_indices;
}


const std::map<std::string, std::map<int,int> >& lts_info::get_variable_parameter_index_positions() const
{
    return variable_parameter_index_positions;
}


const lts_type& lts_info::get_lts_type() const
{
    return type;
}


const std::map<int,std::vector<bool> >& lts_info::get_dependency_matrix() const
{
    return matrix;
}


const std::map<int,std::vector<bool> >& lts_info::get_read_matrix() const
{
    return read_matrix;
}


const std::map<int,std::vector<bool> >& lts_info::get_write_matrix() const
{
    return write_matrix;
}


int lts_info::get_index(const std::string& signature)
{
    return param_index[signature];
}


const data_expression& lts_info::get_default_value(int index)
{
    return param_default_values.at(index);
}


bool lts_info::is_read_dependent_propvar(int /* group */)
{
    return true;
}


bool lts_info::is_read_dependent_parameter(int group, int part)
{
    if (group==0 || group==1) return false;
    std::string p = type.get_state_names()[part];
    pbes_expression phi = transition_expression_plain[group];
    std::set<std::string> usedSet = used(phi);
    std::string X = transition_variable_name[group];
    if (usedSet.find(p) == usedSet.end())
    {
        return false; // Parameter is not in used(phi).
    }
    std::set<std::string> params = lts_info::get_param_set(variable_parameters[X]);
    if (params.find(p) != params.end())
    {
        return true; // Parameter is both in used(phi) and in params(X).
    }
    return false; // Parameter is in used(phi), but not in params(X).
}


bool lts_info::is_write_dependent_propvar(int group)
{
    if (group==0 || group==1) return false;
    pbes_expression phi = transition_expression_plain[group];
    std::string X = transition_variable_name[group];
    if (lts_info::tf(phi))
    {
        return true;
    }
    std::set<std::string> occ = lts_info::occ(phi);
    if (occ.empty())
    {
        return false; // Not dependent if occ(phi) == {}.
    }
    else if (occ.size() == 1)
    {
        bool containsX = occ.find(X) != occ.end();
        return !containsX; // Not dependent if occ(phi) == {X}.
    }
    else
    {
        return true; // Dependent, because occ(phi) contains multiple elements.
    }
}


bool lts_info::is_write_dependent_parameter(int group , int part)
{
  if (group==0 || group==1) return false;
    std::string p = type.get_state_names().at(part);
    pbes_expression phi = transition_expression_plain[group];
    std::string X = transition_variable_name[group];
    if (this->reset_option) {
        if (lts_info::tf(phi))
        {
            // phi may have boolean result (not only propositional variable instantiations)
            return true;
        }
        std::set<std::string> params = lts_info::get_param_set(variable_parameters[X]);
        std::set<std::string> resetSet = reset(phi, params);
        if (resetSet.find(p) != resetSet.end())
        {
            return true; // Dependent, because p in reset(phi, params(X)).
        }
    }
    std::set<std::string> emptySet;
    std::set<std::string> changedSet = changed(phi, emptySet);
    bool changedSetContainsP = (changedSet.find(p) != changedSet.end());
    return changedSetContainsP; // Dependent, because p in changed(phi, {}).
}


std::set<std::string> lts_info::changed(const pbes_expression& phi, const std::set<std::string>& L)
{
    std::set<std::string> result;
    if (tr::is_not(phi))
    {
        result = changed(tr::arg(phi), L);
    }
    else if (tr::is_and(phi) || tr::is_or(phi) || tr::is_imp(phi))
    {
        std::set<std::string> l = changed(tr::left(phi), L);
        result.insert(l.begin(), l.end());
        std::set<std::string> r = changed(tr::right(phi), L);
        result.insert(r.begin(), r.end());
    }
    else if (tr::is_forall(phi) || tr::is_exists(phi))
    {
        std::set<std::string> LL;
        LL.insert(L.begin(), L.end());
        data::variable_list vars = tr::var(phi);
        for (data::variable_list::const_iterator var =
                vars.begin(); var != vars.end(); ++var)
        {
            variable variable = *var;
            LL.insert(get_param_signature(variable));
        }
        result = changed(tr::arg(phi), LL);
    }
    else if (tr::is_prop_var(phi))
    {
        std::vector<std::string> var_param_signatures =
                    variable_parameter_signatures[tr::name(phi)];
        data::data_expression_list values = tr::param(phi);
        assert(var_param_signatures.size() == values.size());
        data::data_expression_list::const_iterator val = values.begin();
        for (std::vector<std::string>::const_iterator param =
                var_param_signatures.begin(); param != var_param_signatures.end(); ++param) {
            std::string param_signature = *param;
            if (tr::is_variable(*val))
            {
                const variable& value = atermpp::down_cast<variable>(*val);
                std::string value_signature = get_param_signature(value);
                if (param_signature != value_signature || L.find(value_signature) != L.end())
                {
                    result.insert(param_signature);
                }
            }
            else
            {
                result.insert(param_signature);
            }
            if (val != values.end()) {
                ++val;
            }
        }
    }
    return result;
}


std::set<std::string> lts_info::reset(const pbes_expression& phi, const std::set<std::string>& d)
{
    std::set<std::string> result;
    if (tr::is_not(phi))
    {
        result = reset(tr::arg(phi), d);
    }
    else if (tr::is_and(phi) || tr::is_or(phi) || tr::is_imp(phi))
    {
        std::set<std::string> l = reset(tr::left(phi), d);
        result.insert(l.begin(), l.end());
        std::set<std::string> r = reset(tr::right(phi), d);
        result.insert(r.begin(), r.end());
    }
    else if (tr::is_forall(phi) || tr::is_exists(phi))
    {
        result = reset(tr::arg(phi), d);
    }
    else if (tr::is_prop_var(phi))
    {
        std::set<std::string> params;
        std::vector<std::string> var_params =
                    variable_parameter_signatures[tr::name(phi)];
        for (std::vector<std::string>::const_iterator param =
                var_params.begin(); param != var_params.end(); ++param) {
            std::string signature = *param;
            params.insert(signature);
        }
        for (std::set<std::string>::const_iterator s = d.begin(); s != d.end(); ++s) {
            std::string signature = *s;
            if (params.find(signature) == params.end())
            {
                result.insert(signature);
            }
        }
    }
    return result;
}


bool lts_info::tf(const pbes_expression& phi)
{
    if (tr::is_not(phi))
    {
        return tf(tr::arg(phi));
    }
    else if (tr::is_and(phi) || tr::is_or(phi) || tr::is_imp(phi))
    {
        return tf(tr::left(phi)) || tf(tr::right(phi));
    }
    else if (tr::is_forall(phi) || tr::is_exists(phi))
    {
        return tf(tr::arg(phi));
    }
    else if (tr::is_prop_var(phi))
    {
        return false;
    }
    return true;
}


std::set<std::string> lts_info::occ(const pbes_expression& expr)
{
    std::set<std::string> result;
    if (tr::is_prop_var(expr))
    {
        result.insert(tr::name(expr));
    }
    else if (tr::is_and(expr) || tr::is_or(expr) ||tr::is_imp(expr))
    {
        std::set<std::string> l = occ(tr::left(expr));
        result.insert(l.begin(), l.end());
        std::set<std::string> r = occ(tr::right(expr));
        result.insert(r.begin(), r.end());
    }
    else if (tr::is_forall(expr) || tr::is_exists(expr) || tr::is_not(expr))
    {
        result = occ(tr::arg(expr));
    }
    return result;
}


std::set<std::string> lts_info::free(const pbes_expression& expr)
{
    std::set<std::string> result;
    data::variable_list free_vars = tr::free_variables(expr);
    for (data::variable_list::iterator v = free_vars.begin(); v != free_vars.end(); ++v)
    {
        variable var = *v;
        result.insert(get_param_signature(var));
    }
    return result;
}


std::set<std::string> lts_info::used(const pbes_expression& expr)
{
    std::set<std::string> emptySet;
    return used(expr, emptySet);
}


std::set<std::string> lts_info::used(const pbes_expression& expr, const std::set<std::string>& L)
{
    //std::clog << "lts_info::used(" << bqnf_visitor<equation_type, term_type>::print_brief(expr) << ", L)" << std::endl;
    std::set<std::string> result;
    if (tr::is_data(expr))
    {
        std::set<std::string> fv = free(expr);
        result.insert(fv.begin(), fv.end());
    }
    if (tr::is_prop_var(expr))
    {
        data::variable_list var_params =
                    variable_parameters[tr::name(expr)];
        data::data_expression_list values = tr::param(expr);
        assert(var_params.size() == values.size());
        data::data_expression_list::const_iterator val = values.begin();
        for (data::variable_list::const_iterator param =
                var_params.begin(); param != var_params.end(); ++param) {
            variable parameter = *param;
            std::string param_signature = get_param_signature(parameter);
            if (tr::is_variable(*val))
            {
                const variable& value = atermpp::down_cast<variable>(*val);
                std::string value_signature = get_param_signature(value);
                if (param_signature != value_signature || L.find(value_signature) != L.end())
                {
                    result.insert(value_signature);
                }
            }
            else
            {
                // add free variables in data expression
                std::set<std::string> l = used(*val, L);
                result.insert(l.begin(), l.end());
            }
            if (val != values.end()) {
                ++val;
            }
        }
    }
    else if (tr::is_and(expr) || tr::is_or(expr) || tr::is_imp(expr))
    {
        std::set<std::string> l = used(tr::left(expr), L);
        result.insert(l.begin(), l.end());
        std::set<std::string> r = used(tr::right(expr), L);
        result.insert(r.begin(), r.end());
    }
    else if (tr::is_not(expr))
    {
        result = used(tr::arg(expr), L);
    }
    else if (tr::is_forall(expr) || tr::is_exists(expr))
    {
        std::set<std::string> LL;
        LL.insert(L.begin(), L.end());
        data::variable_list vars = tr::var(expr);
        for (data::variable_list::const_iterator var =
                vars.begin(); var != vars.end(); ++var)
        {
            variable variable = *var;
            LL.insert(get_param_signature(variable));
        }
        result = used(tr::arg(expr), LL);
    }
    return result;
}




std::string lts_info::state_to_string(const ltsmin_state& state)
{
    //std::clog << "info::to_string" << std::endl;
    std::string result;
    std::stringstream ss;
    operation_type type = detail::map_at(get_variable_types(), state.get_variable());
    ss << (type==parity_game_generator::PGAME_AND ? "AND" : "OR");
    ss << ":" << state.get_variable();
    ss << "(";
    const std::vector<data_expression>& param_values = state.get_parameter_values();
    std::vector<std::string> param_signatures =
                this->variable_parameter_signatures[state.get_variable()];
    std::vector<std::string>::const_iterator param_signature =
            param_signatures.begin();
    for (std::vector<data_expression>::const_iterator param_value =
            param_values.begin(); param_value != param_values.end(); ++param_value) {
        if (param_value != param_values.begin())
            ss << ", ";
        ss << *param_signature << " = ";
        ss << *param_value;
        if (param_signature != param_signatures.end())
        {
            ++param_signature;
        }
    }
    ss << ")";
    result = ss.str();
    return result;
}


std::set<std::string> lts_info::get_param_set(const data::variable_list& params)
{
    std::set<std::string> result;
    for (data::variable_list::const_iterator param =
                params.begin(); param != params.end(); ++param) {
        variable parameter = *param;
        result.insert(get_param_signature(parameter));
    }
    return result;
}


std::vector<std::string> lts_info::get_param_sequence(const data::variable_list& params)
{
    std::vector<std::string> result;
    for (data::variable_list::const_iterator param =
                params.begin(); param != params.end(); ++param) {
        variable parameter = *param;
        result.push_back(get_param_signature(parameter));
    }
    return result;
}


std::vector<int> lts_info::get_param_indices(const data::variable_list& params)
{
    std::vector<int> result;
    for (data::variable_list::const_iterator param =
                params.begin(); param != params.end(); ++param) {
        variable parameter = *param;
        int index = this->get_index(get_param_signature(parameter));
        result.push_back(index);
    }
    return result;
}


std::map<int,int> lts_info::get_param_index_positions(const data::variable_list& params)
{
    std::map<int,int> result;
    int i = 0;
    for (data::variable_list::const_iterator param =
                params.begin(); param != params.end(); ++param) {
        variable parameter = *param;
        int index = this->get_index(get_param_signature(parameter));
        result.insert(std::make_pair(index,i));
        i++;
    }
    return result;
}


std::map<variable,std::string> lts_info::variable_signatures;


std::string lts_info::get_param_signature(const variable& param)
{
    std::map<variable,std::string>::const_iterator i = variable_signatures.find(param);
    if (i == variable_signatures.end())
    {
        std::string paramname = param.name();
        std::string paramtype = core::pp(param.sort());
        std::string signature = get_param_signature(paramname, paramtype);
        variable_signatures[param] = signature;
        return signature;
    }
    return i->second;
}


std::string lts_info::get_param_signature(const std::string& paramname,
                                         const std::string& paramtype)
{
    return paramname + ":" + paramtype;
}




/// ltsmin_state

ltsmin_state::ltsmin_state(const std::string& varname)
{
    this->var = varname;
}


ltsmin_state::ltsmin_state(const std::string& varname,
                       const pbes_expression& e)
{
    data_expression novalue;
    //std::clog << "ltsmin_state v = " << pp(v) << std::endl;
    this->var = varname;
    if (tr::is_prop_var(e)) {
        assert(std::string(tr::name(e)) == varname);
        //std::clog << "ltsmin_state: var = " << tr::name(e) << std::endl;
        const data::data_expression_list& values = tr::param(e);
        for (data::data_expression_list::iterator val = values.begin(); val != values.end(); ++val)
        {
            if (*val == novalue)
            {
                throw(std::runtime_error("Error in ltsmin_state: state expression contains NoValue: "
                                    + to_string(e)));
            }
            this->add_parameter_value(*val);
            //std::clog << "ltsmin_state: " << *val << std::endl;
        }
        //std::clog << std::endl;
    } else {
        throw(std::runtime_error("Not a valid state expression! " + to_string(e)));
    }
}

bool ltsmin_state::operator<( const ltsmin_state& other ) const
{
  if (this->var < other.var) return true;
  else if (this->var == other.var)
  {
    if (param_values.size() < other.param_values.size()) return true;
    else if (param_values.size() == other.param_values.size())
    {
      if (param_values < other.param_values) return true;
    }
  }
  return false;
}


bool ltsmin_state::operator==( const ltsmin_state& other ) const
{
  return this->var==other.var
      && param_values.size()==other.param_values.size()
      && param_values == other.param_values;
}


std::string ltsmin_state::get_variable() const
{
    return var;
}


const std::vector<data_expression>& ltsmin_state::get_parameter_values() const
{
    return param_values;
}


void ltsmin_state::add_parameter_value(const data_expression& value)
{
    param_values.push_back(value);
}


pbes_expression ltsmin_state::to_pbes_expression() const
{
    data_expression_vector parameter_values;
    for (std::vector<data_expression>::const_iterator param_value =
            param_values.begin(); param_value != param_values.end(); ++param_value) {
        parameter_values.push_back(*param_value);
    }
    data_expression_list parameter_values_list(parameter_values.begin(), parameter_values.end());
    // Create propositional variable instantiation.
    propositional_variable_instantiation expr =
            propositional_variable_instantiation(core::identifier_string(var), parameter_values_list);
    return expr;
}


std::string ltsmin_state::state_to_string() const
{
    std::string result;
    std::stringstream ss;
    ss << (type==parity_game_generator::PGAME_AND ? "AND" : "OR");
    ss << ":" << var;
    ss << "[" << std::endl;
    for (std::vector<data_expression>::const_iterator entry =
            param_values.begin(); entry != param_values.end(); ++entry) {
        if (entry != param_values.begin())
            ss << std::endl << "  value = ";
        ss << *entry;
    }
    ss << "]";
    result = ss.str();
    return result;
}




/// explorer

explorer::explorer(const std::string& filename, const std::string& rewrite_strategy = "jittyc", bool reset_flag = false, bool always_split_flag = false)
{
    load_pbes(p, filename);
    for (std::vector<pbes_equation>::iterator eqn = p.equations().begin(); eqn
                != p.equations().end(); ++eqn) {
        std::string variable_name = (*eqn).variable().name();
        //std::clog << "varname = " << variable_name << std::endl;
    }
    pbes_system::algorithms::normalize(p);
    if (!is_ppg(p))
    {
        mCRL2log(log::info) << "Rewriting to PPG..." << std::endl;
        p = detail::to_ppg(p);
        mCRL2log(log::info) << "Rewriting done." << std::endl;
    }
    this->pgg = new pbes_greybox_interface(p, true, true, data::parse_rewrite_strategy(rewrite_strategy));
    this->info = new lts_info(p, pgg, reset_flag, always_split_flag);
    //std::clog << "explorer" << std::endl;
    for (int i = 0; i < info->get_lts_type().get_number_of_state_types(); i++) {
        std::map<data_expression,int> data2int_map;
        this->localmaps_data2int.push_back(data2int_map);
        std::vector<data_expression> int2data_map;
        this->localmaps_int2data.push_back(int2data_map);
    }
    //std::clog << "-- end of explorer." << std::endl;
}


explorer::explorer(const pbes& p_, const std::string& rewrite_strategy = "jittyc", bool reset_flag = false, bool always_split_flag = false)
{
    p = p_;
    this->pgg = new pbes_greybox_interface(p, true, true, data::parse_rewrite_strategy(rewrite_strategy));
    this->info = new lts_info(p, pgg, reset_flag, always_split_flag);
    //std::clog << "explorer" << std::endl;
    for (int i = 0; i < info->get_lts_type().get_number_of_state_types(); i++) {
        std::map<data_expression,int> data2int_map;
        this->localmaps_data2int.push_back(data2int_map);
        std::vector<data_expression> int2data_map;
        this->localmaps_int2data.push_back(int2data_map);
    }
    //std::clog << "-- end of explorer." << std::endl;
}


explorer::~explorer()
{
    delete info;
    delete pgg;
}


lts_info* explorer::get_info() const
{
    return info;
}


ltsmin_state explorer::get_initial_state() const
{
    propositional_variable_instantiation initial_state = pgg->get_initial_state();
    return this->get_state(initial_state);
}


void explorer::initial_state(int* state)
{
    ltsmin_state initial_state = this->get_initial_state();
    ltsmin_state dummy("dummy");
    this->to_state_vector(initial_state, state, dummy, 0);
}


ltsmin_state explorer::get_state(const propositional_variable_instantiation& expr) const
{
    //std::clog << "-- get_state --" << std::endl;
    //std::clog << "  expr = " << expr << std::endl;
    propositional_variable_instantiation novalue;
    assert(tr::is_prop_var(expr) && expr != novalue);
    std::string varname = tr::name(expr);
    //std::clog << "  varname = " << varname << std::endl;
    ltsmin_state s(varname, expr);
    return s;
}


ltsmin_state explorer::true_state()
{
    return ltsmin_state("true");
}


ltsmin_state explorer::false_state()
{
    return ltsmin_state("false");
}


data::data_expression explorer::string_to_data(const std::string& s) {
    aterm t = atermpp::read_term_from_string(s);
    data::data_expression value(t);
    pbes_expression result = pgg->rewrite_and_simplify_expression(value);
    return atermpp::down_cast<const data::data_expression>(result);
}


int explorer::get_index(int type_no, const std::string& s)
{
    if (type_no==0)
    {
        return get_string_index(s);
    }
    else
    {
        data_expression value = this->string_to_data(s);
        return get_value_index(type_no, value);
    }
}


int explorer::get_string_index(const std::string& s)
{
    std::map<std::string,int>::iterator it = this->localmap_string2int.find(s);
    int index;
    if (it != this->localmap_string2int.end()) {
        index = it->second;
    } else {
        this->localmap_int2string.push_back(s);
        index = this->localmap_int2string.size() - 1;
        //std::clog << "[" << getpid() << "] get_string_index DEBUG push_back " << index << ": " << s << std::endl;
        this->localmap_string2int.insert(std::make_pair(s,index));
    }
    //std::clog << "get_string_index result =" << index << " (" << this->localmap_int2string->size() << ")" << std::endl;
    return index;
}


int explorer::get_value_index(int type_no, const data_expression& value)
{
    //std::clog << "    get_value_index type_no=" << type_no << " (" << info->get_lts_type().get_number_of_state_types() << ")" << std::endl;
    //std::clog << "                type=" << info->get_lts_type().get_state_type_name(type_no) << std::endl;
    //std::clog << "                value=" << value << std::endl;
    std::map<data_expression,int>& data2int_map = this->localmaps_data2int.at(type_no);
    std::map<data_expression,int>::iterator it = data2int_map.find(value);
    int index;
    if (it != data2int_map.end()) {
        index = it->second;
    } else {
        this->localmaps_int2data.at(type_no).push_back(value);
        index = this->localmaps_int2data.at(type_no).size() - 1;
        data2int_map.insert(std::make_pair(value,index));
    }
    return index;
}


void explorer::to_state_vector(const ltsmin_state& dst_state, int* dst, const ltsmin_state& src_state, int* const& src)
{
    //std::clog << "to_state_vector: " << dst_state.to_string() << std::endl;

    data_expression novalue;
    //std::clog << "-- to_state_vector -- " << std::endl;
    int state_length = info->get_lts_type().get_state_length();

    std::string varname = dst_state.get_variable();
    std::string src_varname;
    bool same_var = false;
    if (!(src==0)) {
        src_varname = src_state.get_variable();
        same_var = (varname==src_varname);
    }
    int varindex;
    if (same_var) {
        varindex = src[0];
    } else {
        varindex = this->get_string_index(varname);
    }
    dst[0] = varindex;
    //std::clog << "  to_state_vector: DEBUG: varname = " << varname << " index = " << varindex << (same_var ? " SAME VAR": "") << std::endl;


    // data_expression values[state_length]; N.B. This is not portable C++
    // MCRL2_SYSTEM_SPECIFIC_ALLOCA(values, data_expression, state_length);
    std::vector < data_expression > values(state_length);

    if (info->get_reset_option() || src == 0) {
        int type_no;
        for (int i = 1; i < state_length; i++) {
            data_expression default_value = info->get_default_value(i-1);
            values[i] = default_value;
            type_no = info->get_lts_type().get_state_type_no(i);
            dst[i] = this->get_value_index(type_no, values[i]);
        }
    } else {
        for (int i = 1; i < state_length; i++) {
            dst[i] = src[i];
        }
    }
    bool error = false;
    const std::vector<data_expression>& parameter_values = dst_state.get_parameter_values();
    std::vector<int> parameter_indices =
                        detail::map_at(info->get_variable_parameter_indices(), varname);
    std::vector<std::string> parameter_signatures =
                    detail::map_at(info->get_variable_parameter_signatures(), varname);
    std::vector<std::string>::iterator param_signature = parameter_signatures.begin();
    int value_index = 0;
    for(std::vector<int>::iterator param_index = parameter_indices.begin();
            param_index != parameter_indices.end(); ++param_index)
    {
        int i = *param_index + 1;
        int type_no = info->get_lts_type().get_state_type_no(i);
        values[i] = parameter_values[value_index];
        if (values[i]==novalue)
        {
            error = true;
        } else {
          if (src==0) {
                // no source state available; compute index for value.
                dst[i] = this->get_value_index(type_no, values[i]);
            }
            else
            {
                // lookup src parameter value
                // FIXME: this could be computed statically: a map from src_var, dst_var and part to boolean
                std::map<int,int> src_param_index_positions = detail::map_at(info->get_variable_parameter_index_positions(), src_state.get_variable());
                std::map<int,int>::iterator src_param_index_position_it = src_param_index_positions.find(*param_index);
                if ( src_param_index_position_it != src_param_index_positions.end()
                        && src_state.get_parameter_values()[src_param_index_position_it->second] == values[i])
                {
                    // src value exists and is equal to the dst value.
                    // save to copy index from src_state
                    // which has been done earlier
                } else {
                    // parameter value has changed or does not exists in src; compute index for value.
                    dst[i] = this->get_value_index(type_no, values[i]);
                }
            }
        }
        if (param_signature != parameter_signatures.end())
        {
            ++param_signature;
        }
        value_index++;
    }
    if (error)
    {
        throw(std::runtime_error("Error in to_state_vector: NoValue in parameters of dst_state: "
                            + info->state_to_string(dst_state) + "."));
    }
    //std::clog << "-- to_state_vector: done --" << std::endl;
}


std::string explorer::get_value(int type_no, int index)
{
    //std::clog << "get_value type_no = " << type_no << " index = " << index << std::endl;
    if (type_no==0)
    {
        return this->get_string_value(index);
    }
    else
    {
        data_expression value = get_data_value(type_no, index);
        std::string s = data::pp(value);
        return s;
    }
}


const std::string& explorer::get_string_value(int index)
{
    if (index >= (int)(localmap_int2string.size()))
    {
        throw(std::runtime_error("Error in get_string_value: Value not found for index " + boost::lexical_cast<std::string>(index) + "."));
    }
    return localmap_int2string.at(index);
}


const data_expression& explorer::get_data_value(int type_no, int index)
{
    std::vector<data_expression>& int2data_map = this->localmaps_int2data.at(type_no);
    if (index >= (int)(int2data_map.size()))
    {
        throw(std::runtime_error("Error in get_data_value: Value not found for type_no "
                                            + boost::lexical_cast<std::string>(type_no) + " at index " + boost::lexical_cast<std::string>(index) + "."));
    }
    return int2data_map.at(index);
}


ltsmin_state explorer::from_state_vector(int* const& src)
{
    //std::clog << "-- from_state_vector(model, src) --" << std::endl;
    data_expression novalue;
    int state_length = info->get_lts_type().get_state_length();

    std::string varname = this->get_string_value(src[0]);
    //std::clog << "from_state_vector: varname = " << varname << std::endl;

    bool error = false;

    // data_expression values[state_length]; N.B. This is not portable C++
    // MCRL2_SYSTEM_SPECIFIC_ALLOCA(values, data_expression, state_length);
    std::vector <data_expression> values(state_length);

    int type_no;
    for (int i = 1; i < state_length; i++) {
        //std::clog << "from_state_vector: values: " << i << " (" << src[i] << "): " << std::endl;
        type_no = info->get_lts_type().get_state_type_no(i);
        values[i] = this->get_data_value(type_no, src[i]);
        //std::clog << "from_state_vector:   " << values[i].to_string() << std::endl;
    }
    //std::clog << "from_state_vector: values done." << std::endl;
    data_expression_vector parameters;
    std::vector<int> parameter_indices =
            detail::map_at(info->get_variable_parameter_indices(), varname);
    for (std::vector<int>::iterator param_index = parameter_indices.begin(); param_index
            != parameter_indices.end(); ++param_index) {
        if (values[*param_index+1]==novalue)
        {
            error = true;
            //std::clog << "from_state_vector: varname = " << varname << ", values[" << *param_index+1 << "] = " << values[*param_index+1].to_string() << "(" << src[*param_index+1] << ")" << std::endl;
        }
        parameters.push_back(values[*param_index+1]);
    }
    if (error)
    {
        throw(std::runtime_error("Error in from_state_vector: NoValue in parameters."));
    }
    data_expression_list paramlist(parameters.begin(), parameters.end());
    propositional_variable_instantiation state_expression(varname, paramlist);
    //std::clog << "from_state_vector: state_expression = " << state_expression.to_string() << std::endl;
    ltsmin_state state = this->get_state(state_expression);
    //std::clog << "from_state_vector: state = " << state->to_string() << std::endl;
    return state;
}


std::vector<ltsmin_state> explorer::get_successors(const ltsmin_state& state)
{
    //std::cout << "get_successors: " << state->to_string() << std::endl;
    std::vector<ltsmin_state> result;

    pbes_expression e = state.to_pbes_expression();
    assert(core::detail::check_term_PropVarInst(e));
    if (state.get_variable()=="true")
    {
        // Adding true=true
        result.push_back(state);
    }
    else if (state.get_variable()=="false")
    {
        // Adding false=false
        result.push_back(state);
    }
    else
    {
        std::set<pbes_expression> successors
                = pgg->get_successors(e);
        operation_type type = detail::map_at(info->get_variable_types(), state.get_variable());
        for (std::set<pbes_expression>::const_iterator expr = successors.begin(); expr
                != successors.end(); ++expr) {
            if (tr::is_prop_var(*expr)) {
                result.push_back(get_state(atermpp::down_cast<propositional_variable_instantiation>(*expr)));
            } else if (tr::is_true(*expr)) {
                if (type != parity_game_generator::PGAME_AND)
                {
                    result.push_back(true_state());
                }
            } else if (tr::is_false(*expr)) {
                if (type != parity_game_generator::PGAME_OR)
                {
                    result.push_back(false_state());
                }
            } else {
                throw(std::runtime_error("!! Successor is NOT a propvar: " + pbes_system::pp(*expr)));
            }
        }
    }
    return result;
}


std::vector<ltsmin_state> explorer::get_successors(const ltsmin_state& state,
                                                     int group)
{
    //std::clog << "get_successors: " << state.to_string() << ", group=" << group << std::endl;
    std::vector<ltsmin_state> result;

    if (group == 0 && state.get_variable()=="true")
    {
        // Adding true=true
        result.push_back(state);
    }
    else if (group == 1 && state.get_variable()=="false")
    {
        // Adding false=false
        result.push_back(state);
    }
    else
    {
        std::string varname = state.get_variable();
        std::string group_varname = info->get_transition_variable_names()[group];
        if (varname==group_varname)
        {
            pbes_expression e = state.to_pbes_expression();
            std::set<pbes_expression> successors
                    = pgg->get_successors(e, group_varname,
                                             info->get_transition_expressions()[group]);
            operation_type type = detail::map_at(info->get_variable_types(), state.get_variable());
            for (std::set<pbes_expression>::const_iterator expr = successors.begin(); expr
                    != successors.end(); ++expr) {
                //std::clog << "* Successor: " << *expr << std::endl;
                if (tr::is_prop_var(*expr)) {
                    result.push_back(get_state(atermpp::down_cast<propositional_variable_instantiation>(*expr)));
                } else if (tr::is_true(*expr)) {
                    if (type != parity_game_generator::PGAME_AND)
                    {
                        result.push_back(true_state());
                    }
                } else if (tr::is_false(*expr)) {
                    if (type != parity_game_generator::PGAME_OR)
                    {
                        result.push_back(false_state());
                    }
                } else {
                    throw(std::runtime_error("!! Successor is NOT a propvar: " + pbes_system::pp(*expr)));
                }
            }
        }
    }
    return result;
}


} // namespace pbes_system

} // namespace mcrl2
