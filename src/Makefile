COQC_COMMAND=coqc
MODULE_NAME=PFPL
FLAGS=-Q . $(MODULE_NAME)

COQC=$(COQC_COMMAND) $(FLAGS)

all: SystemT.vo

clean:
	rm -f *.vo
	rm -f *.glob

SystemT.vo: Aux.vo Maps.vo
	$(COQC) SystemT.v

Aux.vo: Maps.vo
	$(COQC) Aux.v

Maps.vo:
	$(COQC) Maps.v
