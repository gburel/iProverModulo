prefix= /home/guillaume/tmp
exec_prefix = ${prefix}
bindir= ${exec_prefix}/bin
OCAMLC=/home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/ocamlc -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/stdlib -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/unix -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/str -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/dynlink -annot -g
OCAMLOPT=/home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/ocamlopt.opt -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/stdlib -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/unix -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/str -I /home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/otherlibs/dynlink
OCAMLLEX=/home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/lex/ocamllex.opt
OCAMLYACC=/home/guillaume/projets/Bware_iprover_modulo/iProverModulo/ocaml-4.00.1/yacc/ocamlyacc
MKDIR_P=/bin/mkdir -p
INSTALL=/usr/bin/install -c

LIBS=unix.cma

all: autotheo

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLOPT) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml: %.mly
	$(OCAMLYACC) $<

%.mli: %.mly
	$(OCAMLYACC) $<

OBJS=debug lib globals parser_types parser_tptp lexer_tptp parse_files cnf \
 saturate rules main

autotheo.byte: $(OBJS:%=%.cmo)
	$(OCAMLC) $(LIBS) -o $@ $^

autotheo: $(OBJS:%=%.cmx)
	$(OCAMLOPT) $(LIBS:%.cma=%.cmxa) -o $@ $^

.depend: *.ml *.mli
	ocamldep *.mli *.ml > .depend

parser_tptp.cmo: parser_tptp.cmi
parser_tptp.cmx: parser_tptp.cmi

include .depend

install:
	$(MKDIR_P) $(bindir)
	$(INSTALL) autotheo $(bindir)

clean:
	-rm *.cmo *.cmi *.cmx *.annot autotheo autotheo.byte
