/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Saurabh Joshi Daniel Kroening Rajdeep Mukherjee

\*******************************************************************/
#ifndef __CPROVER_HASCO_PATH_SYMEX_H
#define __CPROVER_HASCO_PATH_SYMEX_H
#include <path-symex/locs.h>
#include <path-symex/path_symex_class.h>
//#include <path-symex/path_symex_state.h>
#include "../hasco/path_search.h"
#include "../solver/incremental_solver.h"
#include "path_symex_state_ed.h"
// path-symex early detection

class path_symext_edt : public path_symext, public messaget
{
//#ifdef FULL_INCREMENTAL
    incremental_solvert& solver;
//#else
//  decision_proceduret& solver;
//#endif
public:
    /*static unsigned number_of_dropped_states;
    static unsigned number_of_paths;
    static unsigned number_of_steps;
    static unsigned number_of_VCCs;
    static unsigned number_of_VCCs_after_simplification;
    static unsigned number_of_failed_properties;
    static unsigned number_of_feasible_cond;
    static unsigned number_of_infeasible_cond;*/
    void operator()(
            path_symex_state_edt &state,
            std::list<path_symex_state_edt> &further_states);
//#ifdef FULL_INCREMENTAL
    path_symext_edt(incremental_solvert& _satcheck):path_symext(),solver(_satcheck){}
//#else
//path_symext_edt(decision_proceduret& _satcheck):path_symext(),solver(_satcheck){}
//#endif
protected:
    virtual void do_goto(
            path_symex_state_edt &state,
            std::list<path_symex_state_edt> &further_states);
    virtual void function_call_rec(
            path_symex_state_edt &state,
            const code_function_callt &call,
            const exprt &function,
            std::list<path_symex_state_edt> &further_states);
    void report_statistics_edt();
    void function_call(
            path_symex_state_edt &state,
            const code_function_callt &call,
            std::list<path_symex_state_edt> &further_states);
};
/*unsigned int path_symext_edt::number_of_dropped_states = 0;
unsigned int path_symext_edt::number_of_paths = 0;
unsigned int path_symext_edt::number_of_steps = 0;
unsigned int path_symext_edt::number_of_VCCs = 0;
unsigned int path_symext_edt::number_of_VCCs_after_simplification = 0;
unsigned int path_symext_edt::number_of_failed_properties = 0;
unsigned int path_symext_edt::number_of_feasible_cond = 0;
unsigned int path_symext_edt::number_of_infeasible_cond = 0;*/


// Transform a state by executing a single statement.
// May occasionally yield more than one successor state
// (branches, function calls with trinary operator),
// which are put into "further_states".
// This invokes the early detection version of path-symex

/*void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states,
  const namespacet &ns);
*/
//#ifndef FULL_INCREMENTAL
//void path_symex(
// path_symex_state_edt &state,
//  std::list<path_symex_state_edt> &further_states, decision_proceduret& satcheck);
//#else
void path_symex(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states,
        incremental_solvert& satcheck);
#endif
//#endif
