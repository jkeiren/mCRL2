// Author(s): Aad Mathijssen, Jeroen Keiren
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file data_common.h

#ifndef MCRL2_DATA_COMMON_H
#define MCRL2_DATA_COMMON_H

#include <aterm2.h>
#include "mcrl2/lps/specification.h"
#include "mcrl2/utilities/aterm_ext.h"
#include "libstruct.h"

using namespace ::mcrl2::utilities;

// --------------------------
// Auxiliary list operations
// --------------------------

ATermList merge_list(ATermList l, ATermList m);
//Pre: l and m are two lists without duplicates
//Ret: a list with all elements of l and m precisely once

ATermList subtract_list(ATermList l, ATermList m);
//Pre: l and m are two lists
//Ret: a copy of l without elements that occur in m

// ---------------------------------------------
// Auxiliary functions for system defined sorts
// ---------------------------------------------

inline const char* struct_prefix() { return "Struct@"; }
inline const char* list_prefix()   { return "List@";   }
inline const char* set_prefix()    { return "Set@";    }
inline const char* bag_prefix()    { return "Bag@";    }
inline const char* lambda_prefix() { return "lambda@"; }

//Pre: sort_expr is sort expression
//Ret: sort_expr is the implementation of a structured sort
inline bool is_struct_sort_id(ATermAppl sort_expr)
{
  if (gsIsSortId(sort_expr)) {
    return strncmp(
      struct_prefix(),
      ATgetName(ATgetAFun(ATAgetArgument(sort_expr, 0))),
      strlen(struct_prefix())) == 0;
  } else {
    return false;
  }
}

//Pre: sort_expr is sort expression
//Ret: sort_expr is the implementation of a list sort
inline bool is_list_sort_id(ATermAppl sort_expr)
{
  if (gsIsSortId(sort_expr)) {
    return strncmp(
      list_prefix(),
      ATgetName(ATgetAFun(ATAgetArgument(sort_expr, 0))),
      strlen(list_prefix())) == 0;
  } else {
    return false;
  }
}

//Pre: sort_expr is sort expression
//Ret: sort_expr is the implementation of a set sort
inline bool is_set_sort_id(ATermAppl sort_expr)
{
  if (gsIsSortId(sort_expr)) {
    return strncmp(
      set_prefix(),
      ATgetName(ATgetAFun(ATAgetArgument(sort_expr, 0))),
      strlen(set_prefix())) == 0;
  } else {
    return false;
  }
}

//Pre: sort_expr is sort expression
//Ret: sort_expr is the implementation of a bag sort
inline bool is_bag_sort_id(ATermAppl sort_expr)
{
  if (gsIsSortId(sort_expr)) {
    return strncmp(
      bag_prefix(),
      ATgetName(ATgetAFun(ATAgetArgument(sort_expr, 0))),
      strlen(bag_prefix())) == 0;
  } else {
    return false;
  }
}

//Pre: data_expr is a data expression
//Ret: data_expr is an operation identifier for the implementation of a lambda
//     abstraction
inline bool is_lambda_op_id(ATermAppl data_expr)
{
  if (gsIsOpId(data_expr)) {
    return strncmp(
      lambda_prefix(),
      ATgetName(ATgetAFun(ATAgetArgument(data_expr, 0))),
      strlen(lambda_prefix())) == 0;
  } else {
    return false;
  }
}

bool is_list_enum_impl(ATermAppl data_expr);
//Ret: data_expr is the implementation of a list enumeration
// Prefixes for system defined sorts

// ---------------------------------------------------------
// Definition and auxiliary functions for data declarations
// ---------------------------------------------------------

typedef struct {
  ATermList sorts;
  ATermList cons_ops;
  ATermList ops;
  ATermList data_eqns;
} t_data_decls;
//The type t_data_decls represents data declarations, i.e. sort, constructor,
//operation and data equation declarations

//Post: all fields of p_data_decls have been initialized with the empty list.
void inline initialize_data_decls(t_data_decls *p_data_decls)
{
  p_data_decls->sorts     = ATmakeList0();
  p_data_decls->cons_ops  = ATmakeList0();
  p_data_decls->ops       = ATmakeList0();
  p_data_decls->data_eqns = ATmakeList0();
}

#define data_decls_is_initialised(data_decls)\
(data_decls.sorts != NULL && data_decls.cons_ops  != NULL &&\
 data_decls.ops   != NULL && data_decls.data_eqns != NULL)
//Ret: indicates whether the elements of data_decls are initialised

//Pre: substs is a list of substitutions
//     recursive denotes wheter to apply substitutions recursively through the terms
//Post: p_data_decls in which substs have been applied to sorts, cons_ops, ops and data_eqns
void inline subst_values_list_data_decls(ATermList substs, t_data_decls *p_data_decls, bool recursive)
{
   p_data_decls->sorts     = gsSubstValues_List(substs, p_data_decls->sorts,     recursive);
   p_data_decls->cons_ops  = gsSubstValues_List(substs, p_data_decls->cons_ops,  recursive);
   p_data_decls->ops       = gsSubstValues_List(substs, p_data_decls->ops,       recursive);
   p_data_decls->data_eqns = gsSubstValues_List(substs, p_data_decls->data_eqns, recursive);
}

//Pre: *p_data_decls_1 = v_data_decls_1, *p_data_decls_2 = v_data_decls_2
//Post: *p_data_decls_1 = v_data_decls_1 + v_data_decls_2, *p_data_decls_2 = v_data_decls_2
void inline concat_data_decls(t_data_decls *p_data_decls_1, t_data_decls *p_data_decls_2)
{
  p_data_decls_1->sorts     = ATconcat(p_data_decls_1->sorts,     p_data_decls_2->sorts);
  p_data_decls_1->cons_ops  = ATconcat(p_data_decls_1->cons_ops,  p_data_decls_2->cons_ops);
  p_data_decls_1->ops       = ATconcat(p_data_decls_1->ops,       p_data_decls_2->ops);
  p_data_decls_1->data_eqns = ATconcat(p_data_decls_1->data_eqns, p_data_decls_2->data_eqns);
}

//Pre: *p_data_decls_1 = v_data_decls_1, *p_data_decls_2 = v_data_decls_2
//Post: *p_data_decls_1 = v_data_decls_1 from which everything that is also in v_data_decls_2
//      has been removed.
//      *p_data_decls_2 = v_data_decls_2
void inline subtract_data_decls(t_data_decls *p_data_decls_1, t_data_decls *p_data_decls_2)
{
  p_data_decls_1->sorts     = subtract_list(p_data_decls_1->sorts,     p_data_decls_2->sorts);
  p_data_decls_1->cons_ops  = subtract_list(p_data_decls_1->cons_ops,  p_data_decls_2->cons_ops);
  p_data_decls_1->ops       = subtract_list(p_data_decls_1->ops,       p_data_decls_2->ops);
  p_data_decls_1->data_eqns = subtract_list(p_data_decls_1->data_eqns, p_data_decls_2->data_eqns);
}

//Ret: data_decls1 is equal to data_decls2
inline bool data_decls_equal(t_data_decls data_decls1,
  t_data_decls data_decls2)
{
  return
    ATisEqual(data_decls1.sorts, data_decls2.sorts) &&
    ATisEqual(data_decls1.cons_ops, data_decls2.cons_ops) &&
    ATisEqual(data_decls1.ops, data_decls2.ops) &&
    ATisEqual(data_decls1.data_eqns, data_decls2.data_eqns);
}

//Ret: data declarations of lps_spec
inline t_data_decls get_data_decls(lps::specification &lps_spec)
{
  t_data_decls data_decls;
  data_decls.sorts     = (ATermList) lps_spec.data().sorts();
  data_decls.cons_ops  = (ATermList) lps_spec.data().constructors();
  data_decls.ops       = (ATermList) lps_spec.data().mappings();
  data_decls.data_eqns = (ATermList) lps_spec.data().equations();
  return data_decls;
}

//Ret: lps_spec in which the data declarations are replaced by data_decls
inline void set_data_decls(lps::specification &lps_spec, t_data_decls data_decls)
{
  assert(data_decls_is_initialised(data_decls));
  if (!data_decls_equal(data_decls, get_data_decls(lps_spec))) {
    lps::data_specification data(data_decls.sorts, data_decls.cons_ops, data_decls.ops, data_decls.data_eqns);
    lps_spec = lps::set_data_specification(lps_spec, data);
  }
}

ATermAppl add_data_decls(ATermAppl spec, t_data_decls data_decls);
//Pre: spec is a specification that adheres to the internal syntax of an
//     arbitary phase
//Ret: spec in which the data declarations from data_decls are added

// --------------------
// Auxiliary functions
// --------------------

//pre: BoolExpr is a boolean expression, SortExpr is of type Pos, Nat, Int or
//     Real.
//ret: if(BoolExpr, 1, 0) of sort SortExpr
inline ATermAppl bool_to_numeric(ATermAppl BoolExpr, ATermAppl SortExpr)
{
  // TODO Maybe enforce that SortExpr is a PNIR sort
  return gsMakeDataExprIf(BoolExpr,
           gsMakeOpId(gsString2ATermAppl("1"), SortExpr),
           gsMakeOpId(gsString2ATermAppl("0"), SortExpr));
}

ATermList get_free_vars(ATermAppl data_expr);
//Pre: data_expr is a data expression that adheres to the internal syntax after
//     type checking
//Ret: The free variables in data_expr

ATermList get_function_sorts(ATerm term);
//Pre: term adheres to the internal format
//Ret: a list of all function sorts occurring in term, where each element is
//     unique

//pre: Term to perform beta reduction on,
//     this is the top-level function, which should be used when
//     there is no appropriate context.
//ret: Term with beta reduction performed on it.
ATerm beta_reduce_term(ATerm Term);

#endif //MCRL2_DATA_COMMON_H

