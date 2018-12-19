/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Saurabh Joshi, Daniel Kroening, Rajdeep Mukherjee

\*******************************************************************/
#ifndef __CPROVER_HASCO_PATH_SYMEX_ED_H
#define __CPROVER_HASCO_PATH_SYMEX_ED_H

#include <path-symex/locs.h>
#include <path-symex/var_map.h>
#include <path-symex/path_symex_history.h>
#include <path-symex/path_symex_state.h>
#include "../solver/incremental_solver.h"


class path_symex_state_edt : public path_symex_statet
{
public:
    explicit inline path_symex_state_edt(
            var_mapt &_var_map,
            const locst &_locs,
            path_symex_historyt &_path_symex_history): path_symex_statet(_var_map,_locs,_path_symex_history),
                                                       is_branch(false),
#ifdef FULL_INCREMENTAL
            is_branch_parent(false),
#endif
                                                       branch_depth(0),
                                                       branch_parent(0)
    {
    }
    bool is_branch;
#ifdef FULL_INCREMENTAL
    bool is_branch_parent;
#endif


    inline void record_parent()
    {
      branch_parent=&(*history);
    }
    inline void record_parent(path_symex_stept* _bp)
    {
      branch_parent=_bp;
    }
    path_symex_stept* get_parent()
    {
      return branch_parent;
    }
    bool is_delta_feasible(
            decision_proceduret &decision_procedure) const;
    bool is_delta_feasible(
            incremental_solvert &decision_procedure) const;
    void delta_encode(
            incremental_solvert& decision_procedure) const;
    void delta_encode(
            decision_proceduret& decision_procedure) const;
    bool delta_check_assertion(
            incremental_solvert &decision_procedure);
    unsigned get_branch_depth() {return branch_depth;}
    void inc_branch_depth() { branch_depth++;}
    void get_path_cond(std::list<exprt>& cond) const;

protected:
    unsigned branch_depth;
    path_symex_stept* branch_parent;

};
#endif
