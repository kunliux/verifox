/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERIFOX_SOLVERS_H
#define VERIFOX_SOLVERS_H


#include <cbmc/cbmc_solvers.h>


/*******************************************************************\

Solver factory

\*******************************************************************/

class verifox_solverst:public cbmc_solverst
{
public:
	verifox_solverst(
			const optionst &_options,
			const symbol_tablet &_symbol_table,
			message_handlert &_message_handler):
			cbmc_solverst(_options,_symbol_table,
						  _message_handler)
	{

	}


};


#endif
