# iProver Modulo 0.7+0.3

## Installation

To configure, compile and install iProver Modulo, use the following
commands: 

```
./configure [options]
make
make install
```

The following options are actually used by the configure script :

```
--prefix=PREFIX         install files in PREFIX [default /usr/local]
--with-externdir=DIR    installation directory of external programs
                        ocaml and e-prover are installed here
		        usefull if one does not want to overwrite existing
		        installations
		        [default ${prefix}/share/iprovermodulo/]
--with-runningpath=DIR 	execution path
			path to eprover during execution
			[default ${externdir}/bin]
--help                  print some help
```

Note that values passed to `--datadir` or `--datarootdir` options are not taken
into account.

You may need superuser rights to perform the installation.

Recommended usage of `./configure`:

```
./configure --prefix=$HOME/tmp/ --with-externdir=$HOME/tmp --with-runningpath=$HOME/tmp/bin
```


## Requirements

For compiling, iProver modulo needs a C compiler. A version of the
OCaml compiler is included in this package, it is installed with the
prover and is needed at runtime to compile rewriting rules. Similarly,
a version of eprover is included.

At runtime, iProver modulo needs `eprover` to transform clauses into CNF
(only version 1.4 was tested, but others should work as well), and
`ocamlopt.opt` to compile rewrite rules.


## Execution

iProverModulo can be launched using the following command, where `%s`
has to be replaced by the problem file name and `%d` by the time limit:

```
iprover_modulo_launcher.sh %s %d
```

This executable calls the programs autotheo and iprover_moduloopt,
which themselves call eprover and ocamlopt.opt. The PATH is modified to
access the executables installed with the prover.


## Solutions

Solutions are given following the SZS ontology. For instance

```
% SZS status Theorem
```

or 

```
% SZS status GaveUp
```

When a proof is given, it is enclosed within the following
delimiters:

```
% SZS output start CNFRefutation
% Axioms transformation by autotheo
[...]
%-------------------------------------------------------------
% Dedukti proof by iprover
[...]
% SZS output end CNFRefutation
```

First, a proof of the transformation of the axioms into rewriting rules,
and of the transformation of other formules into clausal normal form, is given
in TSTP format.

Second, the proof found by iProverModulo is given in [Dedukti](https://deducteam.github.io/)'s format.

Options:
```
--dedukti_out_proof <bool>
    Outputs the proof in dedukti format, if it is found by resolution

--dedukti_prefix <string>
    Prefix of the files containing the dedukti proof (default: printed on s
tandard output)
    Output in <string>_sig.dk and <string>_prf.dk

--dedukti_tempfile <string>
    Unique temporary file containing the dedukti proof (default: printed on
 standard output)
```


