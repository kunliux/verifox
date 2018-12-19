#include <cassert>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <uti/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_types.h>
#include <util/std_expr.h>

/*******************************************************************\

Function: renaming an exprt with a suffix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename(exprt &expr, std::string suffix)
{
    if (expr.id() == ID_symbol) {
        symbol_exprt &symbol_expr = to_symbol_expr(expr);
        irep_idt symbol_name = symbol_expr.get_identifier();
        //const symbolt symbol_name = symbol_expr.get_identifier();
        //irep_idt base_id = symbol_name.base_name;

        irep_idt name = suffix + ":" + id2string(symbol_expr.get_identifier());
        symbol_expr.set_identifier(name);
        return;
    }


    for (exprt::operandst::iterator it = expr.operands().begin();
         it != expr.operands().end(); it++) {
        rename(*it, suffix);
    }
}

/*******************************************************************\

Function: renaming an exprt with a suffix

 Inputs: Input list of exprts and an expression w.r.t. slicing is done

 Outputs: List of exprts after slicing

 Purpose:

\*******************************************************************/

exprt slicing(std::list<exprt> &input_expr, exprt &expr, std::list<exprt> &output_expr)
{
    input_expr.reverse();
    std::list<irep_idt> inter_expr;
    int flag=0;

    // check if the expression w.r.t. which slicing is to be done
    // is a symbol or not, and populate inter_expr
    if (expr.id() == ID_symbol) {
        symbol_exprt &symbol_expr = to_symbol_expr(expr);
        irep_idt slicing_expr_name = symbol_expr.get_identifier();
        inter_expr.push_back(slicing_expr_name);
    }
    else
    {
        // check if the expression w.r.t. which slicing is to be done is actually an expression
        for (exprt::operandst::iterator it = expr.operands().begin();
             it != expr.operands().end(); it++) {
            symbol_exprt &symbol = to_symbol_expr(*it);
            irep_idt name = symbol.get_identifier();
            inter_expr.push_back(name);
        }
    }
    // Now iterate over all input_expr.
    // Note that an input_expr can be of type assignment or ternary operator or implication operator
    for(std::list<exprt>::const_iterator it = input_expr.begin();
        it != input_expr.end(); it++) {
        // check if input_expr is an expression, if so, match this with symbols in inter_expr
        if(it->id() == ID_equal) {
            // extract the lhs of the equality expression and match that to the existing inter_expr to see
            // if the slicing affects this statement
            exprt lhs = it->op0();
            symbol_exprt &symbol_lhs = to_symbol_expr(lhs);
            irep_idt lhs_expr_name = symbol_lhs.get_identifier();
            // Now check if this symbols already appears in the inter_expr
            for(std::list<irep_idt>::const_iterator it1 = inter_expr.begin();
                it1 != inter_expr.end(); it1++) {
                if(*it1 == lhs_expr_name) flag = 1;
                else flag = 0;
            }
            // If flag==1, this new expression is not part of slicing and insert the new rhs symbol to the inter_expr
            if(flag == 1) {
                // insert all the rhs symbol to the inter_expr
                for (exprt::operandst::iterator it2 = it->operands().begin();
                     it2 != it->operands().end(); it2++) {
                    symbol_exprt &rhs_symbol = to_symbol_expr(*it2);
                    irep_idt rhs_name = rhs_symbol.get_identifier();
                    inter_expr.push_back(rhs_name);
                }
                // finally push the full expression to the output_expr as this is not affected due to slicing
                output_expr.push_back(*it);
            }
        }
    }
    return output_expr;
}
