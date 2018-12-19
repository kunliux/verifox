include ../config.inc
TOOLNAME=verifox
SRC = hasco_main.cpp hasco_parseoptions.cpp path_search.cpp trace_partition.cpp
CBMCSRC=$(CBMC)/src
OBJ += $(CBMCSRC)/ansi-c/ansi-c$(LIBEXT) \
       $(CBMCSRC)/linking/linking$(LIBEXT) \
       $(CBMCSRC)/big-int/big-int$(LIBEXT) \
       $(CBMCSRC)/goto-programs/goto-programs$(LIBEXT) \
       $(CBMCSRC)/analyses/analyses$(LIBEXT) \
       $(CBMCSRC)/langapi/langapi$(LIBEXT) \
       $(CBMCSRC)/xmllang/xmllang$(LIBEXT) \
       $(CBMCSRC)/assembler/assembler$(LIBEXT) \
       $(CBMCSRC)/solvers/solvers$(LIBEXT) \
       $(CBMCSRC)/util/util$(LIBEXT) \
       $(CBMCSRC)/goto-symex/adjust_float_expressions$(OBJEXT) \
       $(CBMCSRC)/goto-symex/rewrite_union$(OBJEXT) \
       $(CBMCSRC)/pointer-analysis/dereference$(OBJEXT) \
       $(CBMCSRC)/path-symex/path-symex$(LIBEXT)

DELTA_OBJ= ../path-symex-ed/path_symex$(OBJEXT) \
			../path-symex-ed/path_symex_state_ed$(OBJEXT) \
			../solver/incremental_solver$(OBJEXT)
OBJ+=$(DELTA_OBJ)
INCLUDES= -I $(CBMCSRC)

LIBS =


include $(CBMCSRC)/config.inc
include $(CBMCSRC)/common

CXXFLAGS += $(HASCOFLAGS)
CLEANFILES = $(TOOLNAME)$(EXEEXT)

all:	$(TOOLNAME)-pi$(EXEEXT) $(TOOLNAME)-fi$(EXEEXT)
	

#all: hasco$(EXEEXT)

ifneq ($(wildcard $(CBMCSRC)/bv_refinement/Makefile),)
  OBJ += $(CBMCSRC)/bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard $(CBMCSRC)/cpp/Makefile),)
  OBJ += $(CBMCSRC)/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMCSRC)/java_bytecode/Makefile),)
  OBJ += $(CBMCSRC)/java_bytecode/java_bytecode$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA_BYTECODE
endif

ifneq ($(wildcard $(CBMCSRC)/specc/Makefile),)
  OBJ += $(CBMCSRC)/specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard $(CBMCSRC)/php/Makefile),)
  OBJ += $(CBMCSRC)/php/php$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

$(TOOLNAME)-pi$(EXEEXT): $(OBJ)
ifeq (,$(findstring FULL_INCREMENTAL,$(HASCOFLAGS)))
	$(LINKBIN)
endif

$(TOOLNAME)-fi$(EXEEXT):	$(OBJ)
ifneq (,$(findstring FULL_INCREMENTAL,$(HASCOFLAGS)))
	$(LINKBIN)
endif

.PHONY: symex-mac-signed

symex-mac-signed: cbmc$(EXEEXT)
	strip symex$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) symex$(EXEEXT)

