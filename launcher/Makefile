prefix= /home/guillaume/tmp
exec_prefix = ${prefix}
bindir = ${exec_prefix}/bin
OCAMLOPT= /home/guillaume/projets/iProverModulo/ocaml-4.02.1/ocamlopt.opt -I /home/guillaume/projets/iProverModulo/ocaml-4.02.1/stdlib -I /home/guillaume/projets/iProverModulo/ocaml-4.02.1/otherlibs/unix -I /home/guillaume/projets/iProverModulo/ocaml-4.02.1/otherlibs/str -I /home/guillaume/projets/iProverModulo/ocaml-4.02.1/otherlibs/dynlink
MKDIR_P=/bin/mkdir -p
INSTALL=/usr/bin/install -c
TARGET=iprover_modulo_launcher

$(TARGET): id_encoding.cmx main.cmx
	$(OCAMLOPT) -o $@ $^ 

%.cmx: %.ml
	$(OCAMLOPT) -c $<

%.cmi: %.mli
	$(OCAMLOPT) -c $<

main.cmx: id_encoding.cmi
id_encoding.cmx: id_encoding.cmi

install: 
	$(MKDIR_P) $(bindir)
	$(INSTALL) $(TARGET) $(bindir)
	$(INSTALL) $(TARGET).sh $(bindir)

clean: 
	rm *.cmx $(TARGET)
