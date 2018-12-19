/*******************************************************************\

Module: Symex Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/unicode.h>
#include "../util/version.h"
#include "hasco_parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void print_banner()
{
	std::cout << "####################################################################" << std::endl;
	std::cout << "              VerifOx " << VERIFOX_VERSION << std::endl;
	std::cout << "                by Saurabh Joshi and Rajdeep Mukherjee" << std::endl;
	std::cout << "                based on CPROVER framework by Daniel Kroening and Edmund Clarke" << std::endl;
	std::cout << "                 Indian Institute of Technology Guwahati, India" << std::endl;
	std::cout << "                  University of Oxford, United Kingdom" << std::endl;
	std::cout << "####################################################################" << std::endl;
}

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  symex_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#else
int main(int argc, const char **argv)
{
	hasco_parseoptionst parseoptions(argc, argv);
	return parseoptions.main();
}
#endif
