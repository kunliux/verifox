SUBDIRS = hasco path-symex-ed solver
TOOLNAME= verifox
#all: $(SUBDIRS)
#deltagit

all:	
	$(MAKE) clean
	$(MAKE)	$(TOOLNAME)-pi
	$(MAKE)	clean
	$(MAKE)	$(TOOLNAME)-fi

.PHONY: $(SUBDIRS)
.PHONY: clean $(TOOLNAME)-fi $(TOOLNAME)-pi FORCE cleanall cleanexec

$(TOOLNAME)-fi	:	export HASCOFLAGS += -DFULL_INCREMENTAL
$(TOOLNAME)-fi	:	$(SUBDIRS)
	@echo "Making $(TOONAME)-fi"
$(TOOLNAME)-pi	:	$(SUBDIRS)
	@echo "Making $(TOOLNAME)-pi"


$(SUBDIRS):	FORCE
	$(MAKE) -C $@

# Dependencies

hasco	:	path-symex-ed solver

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

cleanall:	clean cleanexec
	

cleanexec:	
		[ -e hasco/$(TOOLNAME)-fi ] && rm -f hasco/$(TOOLNAME)-fi 
		[ -e hasco/$(TOOLNAME)-pi ] && rm -f hasco/$(TOOLNAME)-pi 
