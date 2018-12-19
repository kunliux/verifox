/*******************************************************************\

Module: Incremental Solver Interface

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_INCREMENTAL_SOLVER_H
#define CPROVER_INCREMENTAL_SOLVER_H

#include <map>
#include <iostream>
#include <util/time_stopping.h>
#include <util/options.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2/smt2_dec.h>
#include <memory>
//#include "domain.h"
//#include "util.h"


//#define NON_INCREMENTAL // (experimental)

//#define DISPLAY_FORMULA
//#define DEBUG_FORMULA
//#define DEBUG_OUTPUT

class incremental_solvert : public messaget
{

public:
    typedef std::list<exprt> constraintst;
    typedef std::list<constraintst> contextst;

    explicit incremental_solvert(
            const namespacet &_ns,const optionst& _options) :
    //sat_check(NULL),
            solver(NULL),
            ns(_ns),
            options(_options),
            activation_literal_counter(0),
            //  domain_number(0),
            solver_calls(0)
    {
      allocate_solvers();
      contexts.push_back(constraintst());
    }

    virtual ~incremental_solvert()
    {
      deallocate_solvers();
    }

    virtual void set_message_handler(message_handlert &handler)
    {
      messaget::set_message_handler(handler);
#if 0
      sat_check->set_message_handler(handler);
    solver->set_message_handler(handler);
#endif
    }

    decision_proceduret::resultt operator()()
    {
      solver_calls++;

#ifdef NON_INCREMENTAL
      deallocate_solvers();
    allocate_solvers();
    unsigned context_no = 0;
    for(contextst::const_iterator c_it = contexts.begin();
        c_it != contexts.end(); c_it++, context_no++)
    {
#ifdef DISPLAY_FORMULA
        std::cerr << "context: " << context_no << std::endl;
#endif
      for(incremental_solvert::constraintst::const_iterator it = c_it->begin();
          it != c_it->end(); it++)
      {
#ifdef DISPLAY_FORMULA
        std::cerr << "actual add_to_solver: " << from_expr(ns,"",*it) << std::endl;
#endif
        *solver << *it;
      }
    }
#else
#ifdef DEBUG_FORMULA
      bvt whole_formula = formula;
    whole_formula.insert(whole_formula.end(),activation_literals.begin(),
			 activation_literals.end());
    solver->set_assumptions(whole_formula);
#endif
#endif
#ifdef SOLVERTIME
      absolute_timet start_time = current_time();
  decision_proceduret::resultt result = solver->dec_solve();
absolute_timet end_time = current_time();
sat_time += end_time-start_time;

//std::cout <<"SAT time for this query"<< sat_time << std::endl;
return result;
#else
      return (*solver)();
#endif

    }

    exprt get(const exprt& expr) { return solver->get(expr); }
    tvt l_get(literalt l) { return solver->l_get(l); }
    literalt convert(const exprt& expr) { return solver->convert(expr); }

    unsigned get_number_of_solver_calls() { return solver_calls; }

    //unsigned next_domain_number() { return domain_number++; }

    static incremental_solvert *allocate(const namespacet &_ns,const optionst& _options)
    {
      return new incremental_solvert(_ns,_options);
    }

    //propt* sat_check;
    //std::unique_ptr<prop_convt> solver;
    prop_convt* solver;
    const namespacet &ns;
    const optionst& options;
    void new_context();
    void pop_context();
    void make_context_permanent();

    //for debugging
    bvt formula;
    void debug_add_to_formula(const exprt &expr);

    //context assumption literals
    bvt activation_literals;

    //non-incremental solving
    contextst contexts;
#ifdef SOLVERTIME
    time_periodt get_solvertime(){return sat_time;}
#endif
protected:
#ifdef SOLVERTIME
    time_periodt sat_time;

#endif
    unsigned activation_literal_counter;
    // unsigned domain_number; //ids for each domain instance to make symbols unique

    //statistics
    unsigned solver_calls;

    void allocate_solvers();
#if 0
    {
#ifdef NON_INCREMENTAL
    sat_check = new satcheckt();
#else
    sat_check = new satcheck_minisat_no_simplifiert();
#endif
    solver = std::unique_ptr<bv_pointerst>(new bv_pointerst(ns,*sat_check));
  }
#endif
    smt2_dect::solvert get_smt2_solver_type() const;
    prop_convt* get_smt2(smt2_dect::solvert solver);
    prop_convt* get_minisat2();
    void deallocate_solvers()
    {
      if(solver!=NULL) delete solver;
      // if(sat_check!=NULL) delete sat_check;
    }
};

static inline incremental_solvert & operator << (
        incremental_solvert &dest,
        const exprt &src)
{
#ifdef DISPLAY_FORMULA
  if(!dest.activation_literals.empty())
    std::cerr << "add_to_solver(" << !dest.activation_literals.back() << "): "
	      << from_expr(dest.ns,"",src) << std::endl;
  else
      std::cerr << "add_to_solver: " << from_expr(dest.ns,"",src) << std::endl;
#endif

#ifdef NON_INCREMENTAL
  dest.contexts.back().push_back(src);
#else
#ifndef DEBUG_FORMULA
  if(!dest.activation_literals.empty())
    *dest.solver << or_exprt(src,
                             literal_exprt(!dest.activation_literals.back()));
  else
    *dest.solver << src;
#else
  if(!dest.activation_literals.empty())
    dest.debug_add_to_formula(
      or_exprt(src,literal_exprt(!dest.activation_literals.back())));
  else
    dest.debug_add_to_formula(src);
#endif
#endif
  return dest;
}

static inline incremental_solvert& operator << (
        incremental_solvert &dest,
        const incremental_solvert::constraintst &src)
{
#ifdef NON_INCREMENTAL
  dest.contexts.back().insert(dest.contexts.back().begin()
			      ,src.begin(),src.end());
#else
  for(incremental_solvert::constraintst::const_iterator it = src.begin();
      it != src.end(); it++)
  {
    dest << *it;
  }
#endif
  return dest;
}

#endif
