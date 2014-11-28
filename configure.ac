AC_PREREQ(2.59)
AC_INIT(iProverModulo, 0.7+0.2, guillaume.burel@ensiie.fr)

AC_PROG_CC

DATADIR="${prefix}/share/iprovermodulo/"
AC_SUBST(DATADIR, $DATADIR)
echo "External programs installed in $DATADIR/bin"

echo "Recursively configuring ocaml sources"
OCAMLDIR=$PWD/ocaml-4.02.1
cd $OCAMLDIR
if ./configure -prefix $DATADIR
then echo "ocaml sources configured."
else exit 1
fi
cd -
AC_SUBST(OCAMLDIR, $OCAMLDIR)

echo "Recursively configuring E sources"
EDIR=E
cd $EDIR
if ./configure --prefix=$DATADIR
then echo "E sources configured."
else exit 1
fi
cd -
AC_SUBST(EDIR, $EDIR)

OCAMLOPT_LOCAL="$OCAMLDIR/ocamlopt.opt -I $OCAMLDIR/stdlib -I $OCAMLDIR/otherlibs/unix -I $OCAMLDIR/otherlibs/str -I $OCAMLDIR/otherlibs/dynlink"
AC_SUBST(OCAMLOPT_LOCAL, $OCAMLOPT_LOCAL)

OCAMLOPT=$DATADIR/bin/ocamlopt.opt
AC_SUBST(OCAMLOPT, $OCAMLOPT)
OCAMLC="${OCAMLDIR}/ocamlc -I $OCAMLDIR/stdlib -I $OCAMLDIR/otherlibs/unix -I $OCAMLDIR/otherlibs/str -I $OCAMLDIR/otherlibs/dynlink"
AC_SUBST(OCAMLC, $OCAMLC)
OCAMLLEX=${OCAMLDIR}/lex/ocamllex.opt
AC_SUBST(OCAMLLEX, $OCAMLLEX)
OCAMLYACC=${OCAMLDIR}/yacc/ocamlyacc
AC_SUBST(OCAMLYACC, $OCAMLYACC)

ocamllib=$DATADIR/lib/ocaml
AC_SUBST(OCAMLLIB, $ocamllib) 

AC_PROG_INSTALL
AC_PROG_MKDIR_P

AC_CONFIG_FILES([Makefile iprover_v0.7_patched/Makefile iprover_v0.7_patched/src/config.ml autotheo/Makefile autotheo/globals.ml launcher/Makefile launcher/iprover_modulo_launcher.sh])
AC_OUTPUT
		