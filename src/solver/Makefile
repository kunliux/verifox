include ../config.inc
SRC = incremental_solver.cpp
CBMCSRC=$(CBMC)/src
OBJ += $(CBMCSRC)/solvers/solvers$(LIBEXT) \
       $(CBMCSRC)/util/util$(LIBEXT) 
       


INCLUDES= -I $(CBMCSRC)

include $(CBMCSRC)/config.inc
include $(CBMCSRC)/common

CLEANFILES = solver$(LIBEXT)

CXXFLAGS += $(HASCOFLAGS)
all: solver$(LIBEXT)

###############################################################################

solver$(LIBEXT): $(OBJ)
	$(LINKLIB)
