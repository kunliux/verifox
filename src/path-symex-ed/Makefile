include ../config.inc
SRC = path_symex.cpp path_symex_state_ed.cpp
CBMCSRC=$(CBMC)/src
INCLUDES= -I $(CBMCSRC)

include $(CBMCSRC)/config.inc
include $(CBMCSRC)/common

CLEANFILES = path-symex$(LIBEXT)

CXXFLAGS += $(HASCOFLAGS)
all: path-symex$(LIBEXT)

###############################################################################

path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)
