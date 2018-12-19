/*******************************************************************\

Module: Concrete Symbolic Transformer with Early Detection Mechanism

Author: Saurabh Joshi Daniel Kroening Rajdeep Mukherjee

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/expr_util.h>
#include <util/base_type.h>
#include <util/message.h>
#include <util/c_types.h>

#include <pointer-analysis/dereference.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
//#include "path_symex_state_ed.h"
//#include <path-symex/path_symex.h>
//#include <path-symex/path_symex.cpp>

#include "path_symex.h"
#include <iostream>
//#define DEBUG
#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: path_searcht::report_statistics_edt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*void path_symext_edt::report_statistics_edt()
{
  // report a bit
  status() << "Number of dropped states: "
           << number_of_dropped_states << messaget::eom;

  status() << "Number of paths: "
           << number_of_paths << messaget::eom;

  status() << "Generated " << number_of_VCCs << " VCC(s), "
           << number_of_VCCs_after_simplification
           << " remaining after simplification"
           << messaget::eom;

  //time_periodt total_time=current_time()-start_time;
  //status() << "Runtime: " << total_time << "s total, "
  //         << sat_time << "s SAT" << messaget::eom;
}*/

/*******************************************************************\

  Function: path_symex_edt::do_goto

  Inputs: Early detection

  Outputs:

  Purpose:

\*******************************************************************/

void path_symext_edt::do_goto(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states)
{
  const goto_programt::instructiont &instruction=
          *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  const loct &loc=state.locs[state.pc()];
  assert(!loc.branch_target.is_nil());

  exprt guard=state.read(instruction.guard);

  if(guard.is_true()) // branch taken always
  {
    state.record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    state.set_pc(loc.branch_target);
    return; // we are done
  }
#ifdef FULL_INCREMENTAL
  //path_symex_state_edt parent_state=state;
 // state.delta_encode(solver);
#endif
  if(!guard.is_false())
  {
    // branch taken case
    // copy the state into 'furhter_states'
#ifndef FULL_INCREMENTAL
    state.delta_encode(solver); // do only if two branch exist
    further_states.push_back(state);
    further_states.back().record_parent();
    further_states.back().record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    further_states.back().set_pc(loc.branch_target);
    further_states.back().history->guard=guard;
    further_states.back().is_branch=true;
    // further_states.back().inc_branch_depth();
    state.is_branch = true; // do only if two branch exist


#else
    state.delta_encode(solver);
        state.is_branch_parent=true;
        further_states.push_front(state);
        path_symex_state_edt& taken_state = further_states.front();
        taken_state.is_branch_parent=false;
        taken_state.record_parent();
        path_symex_stept* parent = taken_state.get_parent();
        taken_state.record_step();
        state.history->branch=stept::BRANCH_TAKEN;
        taken_state.set_pc(loc.branch_target);
        taken_state.history->guard=guard;
        taken_state.is_branch = true;
        //taken_state.inc_branch_depth();

        exprt negated_guard=not_exprt(guard);
          further_states.push_front(state);
          path_symex_state_edt& not_taken_state=further_states.front();
          not_taken_state.is_branch_parent=false;

           not_taken_state.record_parent(parent);
           not_taken_state.record_step();
           state.history->branch=stept::BRANCH_NOT_TAKEN;
           not_taken_state.next_pc();
           not_taken_state.history->guard=negated_guard;
           not_taken_state.is_branch = true;
           //not_taken_state.inc_branch_depth();
#endif
  }
#ifdef FULL_INCREMENTAL
  else
  {
    exprt negated_guard=not_exprt(guard);
      //state.record_parent();
      state.record_step();
      state.history->branch=stept::BRANCH_NOT_TAKEN;
      state.next_pc();
      state.history->guard=negated_guard;
      //state.is_branch = true;
  }
#endif
#ifndef FULL_INCREMENTAL
  // branch not taken case
  exprt negated_guard=not_exprt(guard);
  if(!guard.is_false())
  {
    state.record_parent(); //only if two branch exist
  }
  state.record_step();
  state.history->branch=stept::BRANCH_NOT_TAKEN;
  state.next_pc();
  state.history->guard=negated_guard;
  // state.inc_branch_depth();
  //state.is_branch = true;

#endif

}

/*******************************************************************\

Function: path_symext_edt::function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext_edt::function_call_rec(
        path_symex_state_edt &state,
        const code_function_callt &call,
        const exprt &function,
        std::list<path_symex_state_edt> &further_states)
{
#ifdef DEBUG
  std::cout << "function_call_rec: " << function.pretty() << std::endl;
#endif

  if(function.id()==ID_symbol)
  {
    const irep_idt &function_identifier=
            to_symbol_expr(function).get_identifier();

    // find the function
    locst::function_mapt::const_iterator f_it=
            state.locs.function_map.find(function_identifier);

    if(f_it==state.locs.function_map.end())
      throw "failed to find `"+id2string(function_identifier)+"' in function_map";

    const locst::function_entryt &function_entry=f_it->second;

    loc_reft function_entry_point=function_entry.first_loc;

    // do we have a body?
    if(function_entry_point==loc_reft())
    {
      // no body, this is a skip
      if(call.lhs().is_not_nil())
        assign(state, call.lhs(), nil_exprt());

      state.next_pc();
      return;
    }

    // push a frame on the call stack
    path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];
    thread.call_stack.push_back(path_symex_statet::framet());
    thread.call_stack.back().current_function=function_identifier;
    thread.call_stack.back().return_location=thread.pc.next_loc();
    thread.call_stack.back().return_lhs=call.lhs();
    //thread.call_stack.back().saved_local_vars=thread.local_vars;

    // update statistics
    state.recursion_map[function_identifier]++;

    const code_typet &code_type=function_entry.type;

    const code_typet::parameterst &function_parameters=code_type.parameters();

    const exprt::operandst &call_arguments=call.arguments();

    // now assign the argument values
    for(unsigned i=0; i<call_arguments.size(); i++)
    {
      if(i<function_parameters.size())
      {
        const code_typet::parametert &function_parameter=function_parameters[i];
        irep_idt identifier=function_parameter.get_identifier();

        if(identifier==irep_idt())
          throw "function_call " + id2string(function_identifier) + " no identifier for function argument";

        symbol_exprt lhs(identifier, function_parameter.type());

        // TODO: need to save+restore

        assign(state, lhs, call_arguments[i]);
      }
    }

    // set the new PC
    thread.pc=function_entry_point;
  }
  else if(function.id()==ID_dereference)
  {
    // should not happen, we read() before
    throw "function_call_rec got dereference";
  }
  else if(function.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(function);
    exprt guard=if_expr.cond();

    // add a 'further state' for the false-case
#ifdef FULL_INCREMENTAL
    path_symex_stept* parent;
#endif
    {
#ifndef FULL_INCREMENTAL
      state.is_branch = true;
      state.delta_encode(solver);
      further_states.push_back(state);
      path_symex_state_edt &false_state=further_states.back();
      false_state.record_parent();
      false_state.record_step();
      false_state.is_branch=true;
      false_state.history->guard=not_exprt(guard);
      function_call_rec(further_states.back(), call, if_expr.false_case(), further_states);
#else
      state.delta_encode(solver);
           state.is_branch_parent = true;
           further_states.push_front(state);
           further_states.front().is_branch_parent=false;
           further_states.front().is_branch=true;
           path_symex_state_edt &false_state=further_states.front();
           false_state.record_parent();
           parent = false_state.get_parent();
           false_state.record_step();
           false_state.history->guard=not_exprt(guard);
           function_call_rec(false_state, call, if_expr.false_case(), further_states);
#endif
    }

    // do the true-case in 'state'
    {
#ifndef FULL_INCREMENTAL
      state.is_branch = true;
      state.record_parent();
      state.record_step();
      state.history->guard=guard;
      function_call_rec(state, call, if_expr.true_case(), further_states);
#else
      state.is_branch_parent = true;
                further_states.push_front(state);
                further_states.front().is_branch_parent=false;
                further_states.front().is_branch=true;
                path_symex_state_edt &true_state=further_states.front();
                true_state.record_parent(parent);
                true_state.record_step();
                true_state.history->guard=guard;
                function_call_rec(true_state, call, if_expr.true_case(), further_states);
#endif
    }
  }
  else
    throw "TODO: function_call "+function.id_string();
}

/*******************************************************************\

Function: path_symext::function_call()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext_edt::function_call(
        path_symex_state_edt &state,
        const code_function_callt &call,
        std::list<path_symex_state_edt> &further_states)
{
  exprt f=state.read(call.function());
  function_call_rec(state, call, f, further_states);
}

/*******************************************************************\

Function: path_symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext_edt::operator()(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states)
{
  const goto_programt::instructiont &instruction=
          *state.get_instruction();

#ifdef DEBUG
  std::cout << "path_symext::operator(): " << instruction.type
            << std::endl;
#endif

  switch(instruction.type)
  {
    case END_FUNCTION:
      // pop the call stack
      state.record_step();
          return_from_function(state);
          break;

    case RETURN:
      // pop the call stack
    {
      state.record_step();
      state.next_pc();
      if(instruction.code.operands().size()==1)
        set_return_value(state, instruction.code.op0());


    }
          break;

    case START_THREAD:
    {
      const loct &loc=state.locs[state.pc()];
      assert(!loc.branch_target.is_nil());

      state.record_step();
      state.next_pc();

      // ordering of the following matters due to vector instability
      path_symex_statet::threadt &new_thread=state.add_thread();
      path_symex_statet::threadt &old_thread=state.threads[state.get_current_thread()];
      new_thread.pc=loc.branch_target;
      new_thread.local_vars=old_thread.local_vars;
    }
          break;

    case END_THREAD:
      state.record_step();
          state.disable_current_thread();
          break;

    case GOTO:
      do_goto(state, further_states);
          break;

    case CATCH:
      // ignore for now
      state.record_step();
          state.next_pc();
          break;

    case THROW:
      state.record_step();
          throw "THROW not yet implemented";

    case ASSUME:
      state.record_step();
          state.next_pc();
          if(instruction.guard.is_false())
            state.disable_current_thread();
          else
          {
            exprt guard=state.read(instruction.guard);
            state.history->guard=guard;
          }
          break;

    case ASSERT:
    case SKIP:
    case LOCATION:
    case DEAD:
      state.record_step();
          state.next_pc();
          break;

    case DECL:
      // assigning an RHS of NIL means 'nondet'
      assign(state, to_code_decl(instruction.code).symbol(), nil_exprt());
          state.next_pc();
          break;

    case ATOMIC_BEGIN:
      if(state.inside_atomic_section)
        throw "nested ATOMIC_BEGIN";

          state.record_step();
          state.next_pc();
          state.inside_atomic_section=true;
          break;

    case ATOMIC_END:
      if(!state.inside_atomic_section)
        throw "ATOMIC_END unmatched";

          state.record_step();
          state.next_pc();
          state.inside_atomic_section=false;
          break;

    case ASSIGN:
      assign(state, to_code_assign(instruction.code));
          state.next_pc();
          break;

    case FUNCTION_CALL:
      state.record_step();
          function_call(state, to_code_function_call(instruction.code), further_states);
          break;

    case OTHER:
      state.record_step();

          {
            const codet &code=instruction.code;
            const irep_idt &statement=code.get_statement();

            if(statement==ID_expression)
            {
              // like SKIP
            }
            else if(statement==ID_printf)
            {
              // ignore for now (should record stuff printed)
            }
            else if(statement==ID_asm)
            {
              // ignore for now
            }
            else if(statement==ID_fence)
            {
              // ignore for SC
            }
            else
              throw "unexpected OTHER statement: "+id2string(statement);
          }

          state.next_pc();
          break;

    default:
      throw "path_symext: unexpected instruction";
  }
}



/*******************************************************************\

  Function: path_symex_edt::do_goto

  Inputs: Early detection

  Outputs:

  Purpose:

\*******************************************************************/

/*void path_symext_edt::do_goto(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();
  //std::cout << "inside edt" << std::endl;
  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  const loct &loc=state.locs[state.pc()];
  assert(!loc.branch_target.is_nil());

  exprt guard=state.read(instruction.guard);


  if(guard.is_true()) // branch taken always
  {
    state.record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    state.set_pc(loc.branch_target);
    return; // we are done
  }

  if(!guard.is_false())
  {
    // branch taken case
    // check if the state is feasible. If feasible,
    // then insert the state into the queue "further state", else drop it
    satcheckt satcheck;
    bv_pointerst bv_pointers(ps.ns, satcheck);
    path_symex_statet tmpstate = state;
    tmpstate.record_step();
    tmpstate.history->branch=stept::BRANCH_TAKEN;
    tmpstate.set_pc(loc.branch_target);
    tmpstate.history->guard=guard;
    if(tmpstate.is_feasible(bv_pointers))
    {
       number_of_feasible_cond++;
       //std::cout << "Feasible Condition in IF: " << number_of_feasible_cond << std::endl;
       further_states.push_back(tmpstate);
    }
    else {
       number_of_infeasible_cond++;
       //std::cout << "Infeasible Condition in IF: " << number_of_infeasible_cond << std::endl;
       //further_states.push_back(tmpstate);
    }
  }

  // branch not taken case
  exprt negated_guard=not_exprt(guard);
  state.record_step();
  state.history->branch=stept::BRANCH_NOT_TAKEN;
  state.next_pc();
  state.history->guard=negated_guard;
  // invoke SAT solver at each conditional branch
  satcheckt satcheck;
  bv_pointerst bv_pointers(ps.ns, satcheck);
  if(state.is_feasible(bv_pointers))
  {
     number_of_feasible_cond++;
     //std::cout << "Feasible Condition in else: " << number_of_feasible_cond << std::endl;
  }
  else {
     ps.queue.erase(state);
     number_of_infeasible_cond++;
     //std::cout << "Infeasible Condition in else: " << number_of_infeasible_cond << std::endl;
  }
  // invoke SAT solver at each conditional branch
  //satcheckt satcheck;
  //bv_pointerst bv_pointers(ns, satcheck);

  //if(state.is_feasible(bv_pointers))
  //{
    //std::cout<< "Hurray, Feasible Path" << std::endl;
  //  number_of_feasible_paths++;
  //  std::cout << "FEASIBLE Path: " << number_of_feasible_paths << std::endl;
  //}
  //else {
  //  number_of_infeasible_paths++;
  //  std::cout << "INFEASIBLE Path: " << number_of_infeasible_paths << std::endl;
  //  return;
  //}
  //if(!state.check_assertion(bv_pointers))
  //{
  //  std::cout << "Failed conditional using SAT" << std::endl;
    //build_goto_trace(state, bv_pointers, property_entry.error_trace);
    ///property_entry.status=FAIL;
    //number_of_failed_properties++;
  //}
} */


/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states,
  const namespacet &ns)
{
  path_symext_edt path_symex_ed(ns);
  path_symex_ed(state, further_states);
}*/

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
#if 0
void path_symex(
  path_symex_state_edt &state,
  std::list<path_symex_state_edt> &further_states,
  decision_proceduret& satcheck)
{
  path_symext_edt path_symex_ed(satcheck);
  path_symex_ed(state, further_states);
}
#endif
void path_symex(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states,
        incremental_solvert& satcheck)
{
  path_symext_edt path_symex_ed(satcheck);
  path_symex_ed(state, further_states);
}


