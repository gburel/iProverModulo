OCAMLDIR=/home/guillaume/projets/iProverModulo/ocaml-4.02.1
EDIR=E

all:
	make -C $(OCAMLDIR) world opt opt.opt
	make -C $(EDIR)
	make -C iprover_v0.7_patched
	make -C autotheo
	make -C launcher

install:
	make -C $(OCAMLDIR) install
	make -C $(EDIR) install
	make -C iprover_v0.7_patched install
	make -C autotheo install
	make -C launcher install
