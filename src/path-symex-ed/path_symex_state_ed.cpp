#include "path_symex_state_ed.h"
#include <util/decision_procedure.h>

/*******************************************************************\

Function: path_symex_state_edt::is_feasible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symex_state_edt::is_delta_feasible(
        decision_proceduret &decision_procedure) const
{
#if 0
  // feed path constraint to decision procedure
  path_symex_step_reft src=history;

  while(!src.is_nil() &&
      (branch_parent==NULL || branch_parent != &(*src)))
    {
      src->convert(decision_procedure);
      --src;
    }
#endif
  delta_encode(decision_procedure);

  //decision_procedure << history;

  // check whether SAT
  switch(decision_procedure())
  {
    case decision_proceduret::resultt::D_SATISFIABLE: return true;

    case decision_proceduret::resultt::D_UNSATISFIABLE: return false;

    case decision_proceduret::resultt::D_ERROR: throw "error from decision procedure";
  }

  return true; // not really reachable
}


void path_symex_state_edt::delta_encode(
        decision_proceduret& decision_procedure) const
{
  path_symex_step_reft src=history;

  while(!src.is_nil() &&
        (branch_parent==NULL || branch_parent != &(*src)))
  {
    src->convert(decision_procedure);
    --src;
  }

}

void path_symex_state_edt::delta_encode(
        incremental_solvert& decision_procedure) const
{
  // feed path constraint to decision procedure
  path_symex_step_reft src=history;

  while(!src.is_nil() &&
        (branch_parent==NULL || branch_parent != &(*src)))
  {
    if(src->ssa_rhs.is_not_nil())
      decision_procedure << equal_exprt(src->ssa_lhs, src->ssa_rhs);

    if(src->guard.is_not_nil())
      decision_procedure << src->guard;
    // src->convert(decision_procedure);
    --src;
  }
}

bool path_symex_state_edt::is_delta_feasible(
        incremental_solvert &decision_procedure) const
{
#if 0
  // feed path constraint to decision procedure
  path_symex_step_reft src=history;

  while(!src.is_nil() &&
      (branch_parent==NULL || branch_parent != &(*src)))
    {
    if(src->ssa_rhs.is_not_nil())
       decision_procedure << equal_exprt(src->ssa_lhs, src->ssa_rhs);

     if(src->guard.is_not_nil())
       decision_procedure << src->guard;
     // src->convert(decision_procedure);
      --src;
    }
#endif
  delta_encode(decision_procedure);

  //decision_procedure << history;

  // check whether SAT
  switch(decision_procedure())
  {
    case decision_proceduret::resultt::D_SATISFIABLE: return true;

    case decision_proceduret::resultt::D_UNSATISFIABLE: return false;

    case decision_proceduret::resultt::D_ERROR: throw "error from decision procedure";
  }

  return true; // not really reachable
}

bool path_symex_state_edt::delta_check_assertion(
        incremental_solvert &decision_procedure)
{
  const goto_programt::instructiont &instruction=*get_instruction();

  // assert that this is an assertion
  assert(instruction.is_assert());

  // the assertion in SSA
  exprt assertion=read(instruction.guard);

  // trivial?
  if(assertion.is_true()) return true; // no error

  // the path constraint
  delta_encode(decision_procedure);

  record_parent();//next query should encode constraint only upto here.
  //decision_procedure << history;
  decision_procedure.new_context();
  decision_procedure << not_exprt(assertion);

  // negate the assertion
  //decision_procedure.set_to(assertion, false);

  // check whether SAT
  decision_proceduret::resultt result;
  result=decision_procedure();
  decision_procedure.pop_context();
  switch(result)
  {
    case decision_proceduret::resultt::D_SATISFIABLE:

      return false; // error

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      return true; // no error

    default:
      throw "error from decision procedure";
  }

  return true; // not really reachable
}

/**********************************************************************\

Function: path_symex_state_edt::encode_partition_cond()

Inputs:

Outputs:

Purpose: encode the path condition for this state into cond

\***********************************************************************/

void path_symex_state_edt::get_path_cond(std::list<exprt>& cond) const
{
  path_symex_step_reft src=history;

  while(!src.is_nil())
  {
    if(src->ssa_rhs.is_not_nil())
      cond.push_back(equal_exprt(src->ssa_lhs, src->ssa_rhs));

    if(src->guard.is_not_nil())
      cond.push_back(src->guard);

    //and_exprt and_expr(,);
    --src;
  }
}

