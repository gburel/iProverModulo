AC_PREREQ(2.59)
AC_INIT(iProverModulo, 0.7-0.3, guillaume.burel@ensiie.fr)

AC_PROG_CC

DATADIR="${prefix}/share/iprovermodulo/"
AC_SUBST(DATADIR, $DATADIR)



AC_ARG_WITH([externdir],
  [AS_HELP_STRING([--with-externdir=DIR], [installation directory of external programs])],
  [externdir=$withval],
  [externdir="\${DATADIR}"])
AC_SUBST([externdir], [$externdir])

echo "External programs installed in ${externdir}/bin"

AC_ARG_WITH([runningpath],
  [AS_HELP_STRING([--with-runningpath=DIR], [execution path])],
  [runningpath=$withval],
  [runningpath="\${externdir}/bin"])
AC_SUBST([runningpath], [$runningpath])

DYNSHAREDIR=${DATADIR}
if test "${runningpath}" != "\${DATADIR}/bin" 
then
  DYNSHAREDIR="${runningpath}/../share/iprovermodulo"
fi
AC_SUBST([DYNSHAREDIR], [$DYNSHAREDIR])

echo "Recursively configuring ocaml sources"
OCAMLDIR=$PWD/ocaml-4.02.1
cd $OCAMLDIR
if ./configure -prefix $externdir
then echo "ocaml sources configured."
else exit 1
fi
cd -
AC_SUBST(OCAMLDIR, $OCAMLDIR)

echo "Recursively configuring E sources"
EDIR=E
cd $EDIR
if ./configure --prefix=$externdir
then echo "E sources configured."
else exit 1
fi
cd -
AC_SUBST(EDIR, $EDIR)

OCAMLOPT_LOCAL="$OCAMLDIR/ocamlopt.opt -I $OCAMLDIR/stdlib -I $OCAMLDIR/otherlibs/unix -I $OCAMLDIR/otherlibs/str -I $OCAMLDIR/otherlibs/dynlink"
AC_SUBST(OCAMLOPT_LOCAL, $OCAMLOPT_LOCAL)

OCAMLOPT="${runningpath}/ocamlopt.opt -I ${running_path}/../lib/ocaml/"
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

AC_CONFIG_FILES([Makefile iprover_v0.7_patched/Makefile iprover_v0.7_patched/src/config.ml autotheo/Makefile autotheo/globals.ml launcher/Makefile launcher/iprover_modulo_launcher.sh launcher/main.ml])
AC_OUTPUT
