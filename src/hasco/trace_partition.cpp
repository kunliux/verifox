/*******************************************************************\

Module: Automated Trace Partition

Author: Saurabh Joshi Rajdeep Mukherjee

\*******************************************************************/

#include "trace_partition.h"
#include <path-symex/path_symex.h>
#include <path-symex/path_symex.cpp>
#include "../path-symex-ed/path_symex.h"
#include "path_search.h"
#include "../path-symex-ed/path_symex_state_ed.h"
#include <iostream>
#include <cstdlib>
/*******************************************************************\

Function: cfg_partitiont::set_branch_depth

Inputs:

Outputs:

Purpose: Set branch_depth for cfg based trace partitioning

\*******************************************************************/


void cfg_partitiont::set_branch_depth(unsigned depth)
{
  branch_depth=depth;
}

/**********************************************************************\

Function: cfg_partitiont::get_partition_conditions

Inputs:

Outputs:

Purpose: Return partition conditions for cfg based trace partitioning

\***********************************************************************/


exprst trace_partitiont::get_partition_conditions()
{
  return partition_conditions;
}

/*******************************************************************\

Function: cfg_partitiont::create_partitions

Inputs:

Outputs:

Purpose: do cfg based trace partitioning

\*******************************************************************/


void cfg_partitiont::create_partitions()
{
  // collect path conditions in a list cond
  std::list<exprt> cond;

  locst locs(ns);
  var_mapt var_map(ns);

  locs.build(goto_function);

  // this is the container for the history-forest
  path_symex_historyt history;

  queue.push_back(initial_state(var_map, locs, history));


  while(!queue.empty())
  {
    // Pick a state from the queue,
    // according to some heuristic.
    queuet::iterator state=pick_state();

    // check if this is a branch
    if(state->is_branch)
    {
      unsigned present_depth = state->get_branch_depth();
      // continue along a path as long as present_depth is less than branch_depth
      if(present_depth < branch_depth)
        state->inc_branch_depth();

        // Record the path condition when a state hits the limit for branch_depth
      else if(present_depth == branch_depth) {
        state->get_path_cond(cond);
        // Conjunct over all exprts to obtain a single path condition
        exprt::operandst and_expr;

        for(std::list<exprt>::const_iterator it = cond.begin();
            it != cond.end(); ++it)
          and_expr.push_back(*it);
        exprt conjunct_expr = conjunction(and_expr);

        // copy the conjuncted conditions to partition_conditions
        // partition_conditions would finally contain set of all path constraints up to given depth
        partition_conditions.push_back(conjunct_expr);
        queue.erase(state);
      }
        // Delete the queue here and pick a new state in next iteration
      else {
        queue.erase(state);
      }
    }

    if(drop_state(*state))
    {
      queue.erase(state);
      continue;
    }

    if(!state->is_executable())
    {
      queue.erase(state);
      continue;
    }

    // execute
    path_symex(*state, queue);
  }
}


/*******************************************************************\

Function: initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_state_edt cfg_partitiont::initial_state(
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

Function: path_searcht::pick_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cfg_partitiont::queuet::iterator cfg_partitiont::pick_state()
{
  // Picking the first one is a DFS.
  return queue.begin();
}

/*******************************************************************\

Function: path_searcht::drop_state

  Inputs:

 Outputs:

 Purpose: decide whether to drop a state

\*******************************************************************/

bool cfg_partitiont::drop_state(const statet &state) const
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

Function: path_symex_partitiont::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_partitiont::do_goto(
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

  if(!guard.is_false())
  {
    // branch taken case
    // copy the state into 'furhter_states'
    further_states.push_back(state);
    further_states.back().record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    further_states.back().set_pc(loc.branch_target);
    further_states.back().history->guard=guard;
    // increment branch_depth here
    state.inc_branch_depth();
  }

  // branch not taken case
  exprt negated_guard=not_exprt(guard);
  state.record_step();
  state.history->branch=stept::BRANCH_NOT_TAKEN;
  state.next_pc();
  state.history->guard=negated_guard;
  // increment branch_depth here
  state.inc_branch_depth();
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states)
{
  path_symex_partitiont path_symex;
  path_symex(state, further_states);
}


/*******************************************************************\

Function: path_symex_partitiont::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_partitiont::operator()(
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

Function: path_symex_partitiont::function_call()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_partitiont::function_call(
        path_symex_state_edt &state,
        const code_function_callt &call,
        std::list<path_symex_state_edt> &further_states)
{
  exprt f=state.read(call.function());
  function_call_rec(state, call, f, further_states);
}


/*******************************************************************\

Function: path_symex_partitiont::function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_partitiont::function_call_rec(
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

#if 0
    for(loc_reft l=function_entry_point; ; ++l)
    {
      if(locs[l].target->is_end_function()) break;
      if(locs[l].target->is_decl())
      {
        // make sure we have the local in the var_map
        state.
      }
    }

    // save the locals into the frame
    for(locst::local_variablest::const_iterator
        it=function_entry.local_variables.begin();
        it!=function_entry.local_variables.end();
        it++)
    {
      unsigned nr=state.var_map[*it].number;
      thread.call_stack.back().saved_local_vars[nr]=thread.local_vars[nr];
    }
#endif

    const code_typet &code_type=function_entry.type;

    const code_typet::parameterst &function_parameters=code_type.parameters();

    const exprt::operandst &call_arguments=call.arguments();

    // now assign the argument values to parameters
    for(unsigned i=0; i<call_arguments.size(); i++)
    {
      if(i<function_parameters.size())
      {
        const code_typet::parametert &function_parameter=function_parameters[i];
        irep_idt identifier=function_parameter.get_identifier();

        if(identifier==irep_idt())
          throw "function_call " + id2string(function_identifier) + " no identifier for function parameter";

        symbol_exprt lhs(identifier, function_parameter.type());

        assign(state, lhs, call_arguments[i]);
      }
    }

    // update statistics
    state.recursion_map[function_identifier]++;

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

    {
      further_states.push_back(state);
      path_symex_statet &false_state=further_states.back();
      false_state.record_step();
      false_state.history->guard=not_exprt(guard);
      function_call_rec(further_states.back(), call, if_expr.false_case(), further_states);
    }

    // do the true-case in 'state'
    {
      state.record_step();
      state.history->guard=guard;
      function_call_rec(state, call, if_expr.true_case(), further_states);
    }
  }
  else
    throw "TODO: function_call "+function.id_string();
}

void trace_partitiont::show_partitions() {
  for(std::list<exprt>::const_iterator it = partition_conditions.begin();
      it != partition_conditions.end(); it++){
    if(it->id() == ID_equal) {
      // const equal_exprt& eq = static_cast<const equal_exprt &>(*it);
      equal_exprt equality(it->op1(), it->op2());
      std::string string_value=from_expr(ns, "", equality);
      std::cout << "{-" << string_value << "} " << "\n";
    }
  }
}
