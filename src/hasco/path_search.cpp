/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/time_stopping.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <path-symex/path_symex.h>
#include <path-symex/build_goto_trace.h>

#include "../path-symex-ed/path_symex.h"
#include "path_search.h"
#include "../path-symex-ed/path_symex_state_ed.h"
#include "../solver/incremental_solver.h"
#include <iostream>
/*******************************************************************\

Function: initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_state_edt path_searcht::initial_state(
        var_mapt &var_map,
        const locst &locs,
        path_symex_historyt &path_symex_history)
{
    path_symex_state_edt s(var_map, locs, path_symex_history);

    // create one new thread
    path_symex_statet::threadt &thread=s.add_thread();
    thread.pc=locs.entry_loc; // set its PC
    s.set_current_thread(0);

    return s;
}

/*******************************************************************\

Function: path_searcht::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
#if 0
path_searcht::resultt path_searcht::operator()(
  const goto_functionst &goto_functions)
{
  locst locs(ns);
  var_mapt var_map(ns);

  locs.build(goto_functions);

  // this is the container for the history-forest
  path_symex_historyt history;

  queue.push_back(initial_state(var_map, locs, history));

  // set up the statistics
  number_of_dropped_states=0;
  number_of_VCCs=0;
  number_of_VCCs_after_simplification=0;
  number_of_failed_properties=0;
  number_of_feasible_paths=0;
  number_of_infeasible_paths=0;
  number_of_SAT_query=0;
  number_of_total_paths=0;
  // stop the time
  start_time=current_time();

  initialize_property_map(goto_functions);
#ifndef FULL_INCREMENTAL
  satcheck_minisat_no_simplifiert* satcheck;
  bv_pointerst* bv_pointers;
  bool new_solver_needed=false;
  satcheck = new satcheck_minisat_no_simplifiert;
  bv_pointers=new bv_pointerst(ns,*satcheck);
#else
  incremental_solvert satcheck(ns);
#endif

  while(!queue.empty())
  {
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();
#ifndef FULL_INCREMENTAL
    if(state->is_branch) {
      if(new_solver_needed)
      {
        satcheck = new satcheck_minisat_no_simplifiert;
        bv_pointers = new bv_pointerst(ns,*satcheck);
        new_solver_needed=false;
        number_of_new_solvers++;
        number_of_SAT_query++;
        if(!state->is_feasible(*bv_pointers)) {
                number_of_infeasible_paths++;
        	    queue.erase(state);
                number_of_dropped_states++;
                delete satcheck;
                delete bv_pointers;
                new_solver_needed=true;
                continue;
              }
        else
        {
          state->is_branch=false;
        }
      }
      else
      {
        number_of_SAT_query++;
        if(!state->is_delta_feasible(*bv_pointers))
        {
          queue.erase(state);
          number_of_dropped_states++;
          delete satcheck;
          delete bv_pointers;
          new_solver_needed=true;
          continue;
        }
        else
        {
          state->is_branch=false;
        }
      }
    }
    if(drop_state(*state))
    {
      number_of_total_paths=0;
      number_of_dropped_states++;
      queue.erase(state);
      if(!new_solver_needed)
      {
      delete satcheck;
      delete bv_pointers;
      }
      new_solver_needed=true;
      continue;
    }

    if(!state->is_executable())
    {
      number_of_total_paths=0;
      queue.erase(state);
      if(!new_solver_needed)
      {
      delete satcheck;
      delete bv_pointers;
      }
      new_solver_needed=true;
      continue;
    }
#else
    queuet::iterator next=state;
    next++;
    if(state->is_branch) {
      satcheck.new_context();
      number_of_SAT_query++;
      if(!state->is_delta_feasible(satcheck))
      {
        queue.erase(state);
        satcheck.pop_context();
        number_of_dropped_states++;
        continue;
      }
      else
      {
        state->is_branch=false;
      }


        }
    else if(state->is_branch_parent)
    {

      if(next!=queue.end())
      {
        satcheck.pop_context();
      }
      queue.erase(state);
              continue;


    }

        if(drop_state(*state))
        {
          number_of_total_paths=0;
          number_of_dropped_states++;
          if(next!=queue.end())
                {
                  satcheck.pop_context();
                }
          queue.erase(state);
          continue;
        }

        if(!state->is_executable())
        {
          number_of_total_paths=0;
          if(next!=queue.end())
                {
                  satcheck.pop_context();
                }
          queue.erase(state);
          continue;
        }
#endif
    /*
    status() << "Queue " << queue.size()
             << " thread " << state->get_current_thread()
             << "/" << state->threads.size()
             << " PC " << state->pc() << messaget::eom;
    */
    // an error, possibly?
    if(state->get_instruction()->is_assert())
    {
      if(show_vcc) {
        do_show_vcc(*state, ns);
        check_feasibility(*state,ns);
      }
      else
      {
        check_assertion(*state, ns);

        // all assertions failed?
        if(number_of_failed_properties==property_map.size())
          break;
      }
    }

    // execute

#ifndef FULL_INCREMENTAL
    path_symex(*state, queue,*bv_pointers);
#else
    path_symex(*state,queue,satcheck);
#endif
  }

  report_statistics();

  return number_of_failed_properties==0?SAFE:UNSAFE;
}
#endif

path_searcht::resultt path_searcht::operator()(
        const goto_functionst &goto_functions)
{
    locst locs(ns);
    var_mapt var_map(ns);

    locs.build(goto_functions);

    // this is the container for the history-forest
    path_symex_historyt history;

    queue.push_back(initial_state(var_map, locs, history));

    // set up the statistics
    number_of_dropped_states=0;
    number_of_VCCs=0;
    number_of_VCCs_after_simplification=0;
    number_of_failed_properties=0;
    number_of_feasible_paths=0;
    number_of_infeasible_paths=0;
    number_of_SAT_query=0;
    number_of_total_paths=0;
    number_of_new_solvers=0;
    // stop the time
    start_time=current_time();

    initialize_property_map(goto_functions);
#ifndef FULL_INCREMENTAL
    incremental_solvert* satcheck = new incremental_solvert(ns,options);
    bool new_solver_needed=false;

#else
    incremental_solvert satcheck(ns,options);

#endif

    while(!queue.empty())
    {
        // Pick a state from the queue,
        // according to some heuristic.
        queuet::iterator state=pick_state();
#ifndef FULL_INCREMENTAL
        if(state->is_branch) {
            if(new_solver_needed)
            {
                satcheck = new incremental_solvert(ns,options);
                new_solver_needed=false;
                number_of_new_solvers++;
                number_of_SAT_query++;
                if(!state->is_feasible(*satcheck->solver)) {
                    number_of_infeasible_paths++;
                    queue.erase(state);
                    number_of_dropped_states++;
#ifdef SOLVERTIME
                    sat_time+=satcheck->get_solvertime();
//std::cout << "SAT time for this instance: " << sat_time << std::endl;
#endif
                    delete satcheck;
                    new_solver_needed=true;
                    continue;
                }
                else
                {
                    state->is_branch=false;
                }
            }
            else
            {
                number_of_SAT_query++;
                if(!state->is_delta_feasible(*satcheck))
                {
                    queue.erase(state);
                    number_of_dropped_states++;
#ifdef SOLVERTIME
                    sat_time+=satcheck->get_solvertime();
#endif

                    delete satcheck;
                    new_solver_needed=true;
                    continue;
                }
                else
                {
                    state->is_branch=false;
                }
            }
        }
        if(drop_state(*state))
        {
            number_of_total_paths=0;
            number_of_dropped_states++;
            queue.erase(state);
            if(!new_solver_needed)
            {
#ifdef SOLVERTIME
                sat_time+=satcheck->get_solvertime();
#endif

                delete satcheck;

            }
            new_solver_needed=true;
            continue;
        }

        if(!state->is_executable())
        {
            number_of_total_paths=0;
            queue.erase(state);
            if(!new_solver_needed)
            {
#ifdef SOLVERTIME
                sat_time+=satcheck->get_solvertime();
#endif

                delete satcheck;

            }
            new_solver_needed=true;
            continue;
        }
#else
        queuet::iterator next=state;
    next++;
    if(state->is_branch) {
      satcheck.new_context();
      number_of_SAT_query++;
      if(!state->is_delta_feasible(satcheck))
      {
        queue.erase(state);
        satcheck.pop_context();
        number_of_dropped_states++;
        continue;
      }
      else
      {
        state->is_branch=false;
      }


        }
    else if(state->is_branch_parent)
    {

      if(next!=queue.end())
      {
        satcheck.pop_context();
      }
      queue.erase(state);
              continue;


    }

        if(drop_state(*state))
        {
          number_of_total_paths=0;
          number_of_dropped_states++;
          if(next!=queue.end())
                {
                  satcheck.pop_context();
                }
          queue.erase(state);
          continue;
        }

        if(!state->is_executable())
        {
          number_of_total_paths=0;
          if(next!=queue.end())
                {
                  satcheck.pop_context();
                }
          queue.erase(state);
          continue;
        }
#endif
        /*
        status() << "Queue " << queue.size()
                 << " thread " << state->get_current_thread()
                 << "/" << state->threads.size()
                 << " PC " << state->pc() << messaget::eom;
        */
        // an error, possibly?
        if(state->get_instruction()->is_assert())
        {
            if(show_vcc) {
                do_show_vcc(*state, ns);
                check_feasibility(*state,ns);
            }
            else
            {
                number_of_feasible_paths++;
#ifdef FULL_INCREMENTAL
                check_assertion(*state, ns,satcheck);
#else
                check_assertion(*state,ns,*satcheck);
#endif

                // all assertions failed?
                if(number_of_failed_properties==property_map.size())
                    break;
            }
        }

        // execute

#ifndef FULL_INCREMENTAL
        path_symex(*state, queue,*satcheck);
#else
        path_symex(*state,queue,satcheck);
#endif
    }
#ifdef SOLVERTIME
    #ifndef FULL_INCREMENTAL
  sat_time+=satcheck->get_solvertime();
#else
  sat_time+=satcheck.get_solvertime();
#endif
#endif
    report_statistics();

    return number_of_failed_properties==0?resultt::SAFE : resultt::UNSAFE;
}

/*******************************************************************\

Function: path_searcht::report_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::report_statistics()
{
    // report a bit
    status() << "Number of dropped states: "
             << number_of_dropped_states << messaget::eom;

    status() << "Generated " << number_of_VCCs << " VCC(s), "
             << number_of_VCCs_after_simplification
             << " remaining after simplification"
             << messaget::eom;

    status() << "Number of SAT queries made: " << number_of_SAT_query
             << messaget::eom;

    status() << "Number of new SAT instances: " << number_of_new_solvers
             << messaget::eom;

    status() << "Number of total paths: " << number_of_total_paths
             << messaget::eom;

    status() << "Number of feasible path: " << number_of_feasible_paths
             << messaget::eom;

    status() << "Number of infeasible path: " << number_of_infeasible_paths
             << messaget::eom;

    time_periodt total_time=current_time()-start_time;
    status() << "Runtime: " << total_time << "s total, "
             << sat_time << "s SAT" << messaget::eom;
}

/*******************************************************************\

Function: path_searcht::pick_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_searcht::queuet::iterator path_searcht::pick_state()
{
    // Picking the first one is a DFS.
    return queue.begin();
}

/*******************************************************************\

Function: path_searcht::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::do_show_vcc(
        statet &state,
        const namespacet &ns)
{
    // keep statistics
    number_of_VCCs++;

    const goto_programt::instructiont &instruction=
            *state.get_instruction();

    mstreamt &out=result();

    if(instruction.source_location.is_not_nil())
        out << instruction.source_location << "\n";

    if(instruction.source_location.get_comment()!="")
        out << instruction.source_location.get_comment() << "\n";

    unsigned count=1;

    std::vector<path_symex_step_reft> steps;
    state.history.build_history(steps);

    for(std::vector<path_symex_step_reft>::const_iterator
                s_it=steps.begin();
        s_it!=steps.end();
        s_it++)
    {
        if((*s_it)->guard.is_not_nil())
        {
            std::string string_value=from_expr(ns, "", (*s_it)->guard);
            out << "{-" << count << "} " << string_value << "\n";
            count++;
        }

        if((*s_it)->ssa_rhs.is_not_nil())
        {
            equal_exprt equality((*s_it)->ssa_lhs, (*s_it)->ssa_rhs);
            std::string string_value=from_expr(ns, "", equality);
            out << "{-" << count << "} " << string_value << "\n";
            count++;
        }
    }

    out << "|--------------------------" << "\n";

    exprt assertion=state.read(instruction.guard);

    out << "{" << 1 << "} "
        << from_expr(ns, "", assertion) << "\n";

    if(!assertion.is_true())
        number_of_VCCs_after_simplification++;

    out << eom;
}

/*******************************************************************\

Function: path_searcht::drop_state

  Inputs:

 Outputs:

 Purpose: decide whether to drop a state

\*******************************************************************/

bool path_searcht::drop_state(const statet &state) const
{
    // depth
    if(depth_limit!=std::numeric_limits<unsigned>::max() && state.get_depth()>depth_limit) return true;

    // context bound
    if(context_bound!=std::numeric_limits<unsigned>::max() && state.get_no_thread_interleavings()) return true;

    // unwinding limit -- loops
    if(unwind_limit!=std::numeric_limits<unsigned>::max() && state.get_instruction()->is_backwards_goto())
    {
        for(path_symex_statet::unwinding_mapt::const_iterator
                    it=state.unwinding_map.begin();
            it!=state.unwinding_map.end();
            it++)
            if(it->second>unwind_limit)
                return true;
    }

    // unwinding limit -- recursion
    if(unwind_limit!=std::numeric_limits<unsigned>::max() && state.get_instruction()->is_function_call())
    {
        for(path_symex_statet::recursion_mapt::const_iterator
                    it=state.recursion_map.begin();
            it!=state.recursion_map.end();
            it++)
            if(it->second>unwind_limit)
                return true;
    }

    return false;
}

/*******************************************************************\

Function: path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::check_assertion(
        statet &state,
        const namespacet &ns)
{
    // keep statistics
    number_of_VCCs++;

    const goto_programt::instructiont &instruction=
            *state.get_instruction();

    irep_idt property_name=instruction.source_location.get_property_id();
    property_entryt &property_entry=property_map[property_name];

    if(property_entry.status==FAIL)
        return; // already failed
    else if(property_entry.status==NOT_REACHED)
        property_entry.status=PASS; // well, for now!

    // the assertion in SSA
    exprt assertion=
            state.read(instruction.guard);

    if(assertion.is_true()) return; // no error, trivially

    // keep statistics
    number_of_VCCs_after_simplification++;

    status() << "Checking property " << property_name << eom;

    // take the time
    absolute_timet sat_start_time=current_time();

    satcheckt satcheck;
    bv_pointerst bv_pointers(ns, satcheck);

    satcheck.set_message_handler(get_message_handler());
    bv_pointers.set_message_handler(get_message_handler());

    if(!state.check_assertion(bv_pointers))
    {
        build_goto_trace(state, bv_pointers, property_entry.error_trace);
        property_entry.status=FAIL;
        number_of_failed_properties++;
    }

    sat_time+=current_time()-sat_start_time;
}
/*******************************************************************\

Function: path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::check_assertion(
        statet &state,
        const namespacet &ns,
        incremental_solvert& decision_procedure)
{
    // keep statistics
    number_of_VCCs++;

    const goto_programt::instructiont &instruction=
            *state.get_instruction();

    irep_idt property_name=instruction.source_location.get_property_id();
    property_entryt &property_entry=property_map[property_name];

    if(property_entry.status==FAIL)
        return; // already failed
    else if(property_entry.status==NOT_REACHED)
        property_entry.status=PASS; // well, for now!

    // the assertion in SSA
    exprt assertion=
            state.read(instruction.guard);

    if(assertion.is_true()) return; // no error, trivially

    // keep statistics
    number_of_VCCs_after_simplification++;

    status() << "Checking property " << property_name << eom;

    // take the time
#ifndef SOLVERTIME
    absolute_timet sat_start_time=current_time();
#endif

    //satcheckt satcheck;
    //bv_pointerst bv_pointers(ns, satcheck);

    //satcheck.set_message_handler(get_message_handler());
    //bv_pointers.set_message_handler(get_message_handler());

    if(!state.delta_check_assertion(decision_procedure))
    {
        build_goto_trace(state, *decision_procedure.solver, property_entry.error_trace);
        property_entry.status=FAIL;
        number_of_failed_properties++;
    }
#ifndef SOLVERTIME
    sat_time+=current_time()-sat_start_time;
#endif
}
/*******************************************************************\

Function: path_searcht::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::initialize_property_map(
        const goto_functionst &goto_functions)
{
    for(goto_functionst::function_mapt::const_iterator
                it=goto_functions.function_map.begin();
        it!=goto_functions.function_map.end();
        it++)
        if(!it->second.is_inlined())
        {
            const goto_programt &goto_program=it->second.body;

            for(goto_programt::instructionst::const_iterator
                        it=goto_program.instructions.begin();
                it!=goto_program.instructions.end();
                it++)
            {
                if(!it->is_assert())
                    continue;

                const source_locationt &source_location=it->source_location;

                irep_idt property_name=source_location.get_property_id();

                property_entryt &property_entry=property_map[property_name];
                property_entry.status=NOT_REACHED;
                property_entry.description=source_location.get_comment();
            }
        }
}


/*******************************************************************\

Function: path_searcht::check_feasibility

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_searcht::check_feasibility(
        statet &state,
        const namespacet &ns)
{
    //number_of_feasible_paths++;
    satcheckt satcheckf;
    bv_pointerst bv_pointersf(ns, satcheckf);
    // ******* My code ******
    if(state.is_feasible(bv_pointersf))
    {
        std::cout<< "Hurray, Feasible Path" << std::endl;
        number_of_feasible_paths++;
        std::cout << "FEASIBLE Path" << number_of_feasible_paths << std::endl;
    }
    else {
        std::cout<< "Yes, Infeasible Path" << std::endl;
        number_of_infeasible_paths++;
        std::cout << "INFEASIBLE Path" << number_of_infeasible_paths << std::endl;
    }
}
