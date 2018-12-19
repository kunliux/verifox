/*******************************************************************\

Module: Automated Trace Partition

Author: Saurabh Joshi Rajdeep Mukherjee

\*******************************************************************/

#include <cassert>
#include <map>
#include <set>
#include <string>
#include <util/message.h>
#include <util/options.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include "path_search.h"
#include <path-symex/path_symex_class.h>
#include <goto-programs/goto_functions.h>
#include <limits>

/*******************************************************************\

Class:  trace_partitiont

Inputs: Main class file

Outputs:

Purpose:

\*******************************************************************/

typedef std::list<exprt> exprst;
class trace_partitiont: public messaget
{
public:
    explicit trace_partitiont(
            const namespacet& _ns, const goto_functionst& _goto_function)
            : ns(_ns) {
        goto_function.copy_from(_goto_function);
    }

    virtual void create_partitions()=0;
    virtual exprst get_partition_conditions();
protected:
    goto_functionst goto_function;
    const namespacet& ns;

    // list of exprts representing the final path constraints
    exprst partition_conditions;
    void show_partitions();
};

class cfg_partitiont: public trace_partitiont
{
public:

    void set_branch_depth(unsigned depth);
    cfg_partitiont(const namespacet& _ns,
                   const goto_functionst& _gf,unsigned _td):trace_partitiont(_ns,_gf),branch_depth(_td), depth_limit(std::numeric_limits<unsigned>::max()), // no limit
                                                            context_bound(std::numeric_limits<unsigned>::max()),
                                                            unwind_limit(std::numeric_limits<unsigned>::max())
    {}
    cfg_partitiont(const namespacet& _ns,const goto_functionst& _gf):trace_partitiont(_ns,_gf), depth_limit(std::numeric_limits<unsigned>::max()), // no limit
                                                                     context_bound(std::numeric_limits<unsigned>::max()),
                                                                     unwind_limit(std::numeric_limits<unsigned>::max())
    {
        branch_depth=std::numeric_limits<unsigned>::max();
    }




    //unsigned get_branch_depth() {return branch_depth;}
    //void inc_branch_depth() { branch_depth++;}

protected:
    unsigned branch_depth;

    // partition function
    virtual void create_partitions();
    path_symex_state_edt initial_state(var_mapt &var_map, const locst &locs,
                                       path_symex_historyt &path_symex_history);

    typedef path_symex_state_edt statet;

    // State queue. Iterators are stable.
    typedef std::list<statet> queuet;
    queuet queue;
    queuet::iterator pick_state();

    bool drop_state(const statet &state) const;
public:
    unsigned depth_limit;
    unsigned context_bound;
    unsigned unwind_limit;

};

class transaction_partitiont: public trace_partitiont
{
public:
    void set_transaction_depth(unsigned depth)
    {
        //transaction_depth_set=true;
        transaction_depth=depth;
    }
    transaction_partitiont(const namespacet& _ns,
                           const goto_functionst& _goto_functions, unsigned _td):trace_partitiont(_ns,_goto_functions),transaction_depth(_td)
    {}

protected:
    unsigned transaction_depth;
    //bool transaction_depth_set;
};

class path_symex_partitiont: public path_symext
{
public:
    inline path_symex_partitiont()
    {
    }
    void operator()(
            path_symex_state_edt &state,
            std::list<path_symex_state_edt> &further_states);

    typedef path_symex_stept stept;

protected:
    void do_goto(
            path_symex_state_edt &state,
            std::list<path_symex_state_edt> &further_states);

    virtual void function_call_rec(
            path_symex_state_edt &state,
            const code_function_callt &call,
            const exprt &function,
            std::list<path_symex_state_edt> &further_states);

    void function_call(
            path_symex_state_edt &state,
            const code_function_callt &call,
            std::list<path_symex_state_edt> &further_states);
};

// Transform a state by executing a single statement.
// May occasionally yield more than one successor state
// (branches, function calls with trinary operator),
// which are put into "further_states".

void path_symex(
        path_symex_state_edt &state,
        std::list<path_symex_state_edt> &further_states);
