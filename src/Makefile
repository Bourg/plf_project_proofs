COQC_COMMAND=coqc
MODULE_NAME=""
FLAGS=-Q . $(MODULE_NAME)

COQC=$(COQC_COMMAND) $(FLAGS)

all: SystemT.vo

clean:
	rm -f *.vo
	rm -f *.glob

SystemT.vo: SystemT.v Aux.vo Maps.vo
	$(COQC) SystemT.v

Aux.vo: Aux.v Maps.vo
	$(COQC) Aux.v

Maps.vo: Maps.v
	$(COQC) Maps.v
