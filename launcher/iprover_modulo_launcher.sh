#!/bin/sh

prefix=/home/guillaume/tmp
exec_prefix=${prefix}
bindir=${exec_prefix}/bin
PATH=$bindir:$PATH
iprover_modulo_launcher $@
