#!/bin/sh
INPUT=$1
BASE=`basename $1`
mv $INPUT $INPUT.delink
cat <<EOF > $INPUT
export LD_LIBRARY_PATH=\${PWD}
exec ./ld.so ./$BASE.delink \$@
EOF
chmod 755 $INPUT
