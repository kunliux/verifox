/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SEARCH_H
#define CPROVER_PATH_SEARCH_H

#include <util/time_stopping.h>
#include <util/options.h>

#include <goto-programs/safety_checker.h>

#include <path-symex/path_symex_state.h>
#include "../path-symex-ed/path_symex_state_ed.h"

#include <limits>

class path_searcht:public safety_checkert
{
public:
    explicit inline path_searcht(const namespacet &_ns,const optionst& _options):
            safety_checkert(_ns),
            options(_options),
            show_vcc(false),
            depth_limit(std::numeric_limits<unsigned>::max()), // no limit
            context_bound(std::numeric_limits<unsigned>::max()),
            unwind_limit(std::numeric_limits<unsigned>::max())
    {
    }
    path_symex_state_edt initial_state(
            var_mapt &var_map,
            const locst &locs,
            path_symex_historyt &path_symex_history);
    virtual resultt operator()(
            const goto_functionst &goto_functions);

    const optionst& options;
    bool show_vcc;

    unsigned depth_limit;
    unsigned context_bound;
    unsigned unwind_limit;

    // statistics
    unsigned number_of_dropped_states;
    unsigned number_of_VCCs;
    unsigned number_of_VCCs_after_simplification;
    unsigned number_of_failed_properties;
    unsigned number_of_total_paths;
    unsigned number_of_feasible_paths;
    unsigned number_of_infeasible_paths;
    unsigned number_of_SAT_query;
    unsigned number_of_new_solvers;
    absolute_timet start_time;
    time_periodt sat_time;

    enum statust { NOT_REACHED, PASS, FAIL };

    struct property_entryt
    {
        statust status;
        irep_idt description;
        goto_tracet error_trace;
    };

    typedef std::map<irep_idt, property_entryt> property_mapt;
    property_mapt property_map;

protected:
    typedef path_symex_state_edt statet;

    // State queue. Iterators are stable.
    typedef std::list<statet> queuet;
    queuet queue;

    queuet::iterator pick_state();

    bool execute(queuet::iterator state, const namespacet &);

    void check_assertion(statet &state, const namespacet &);
    void check_assertion(
            statet &state,
            const namespacet &ns,
            incremental_solvert& decision_procedure);
    void do_show_vcc(statet &state, const namespacet &);
    void check_feasibility(statet &state, const namespacet &);

    bool drop_state(const statet &state) const;

    void report_statistics();

    void initialize_property_map(
            const goto_functionst &goto_functions);
};

#endif
