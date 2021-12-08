#!/bin/sh

SPEC_ROOT=aws-encryption-sdk-specification

# As we make the duvet framework more robust this logic around extracting and rebuilding
# will probably change. For now, do something simple to unblock ourselves. 
REBUILD=false

if [ ! -z $1 ] && [ $1 == "rebuild" ] ; then
  echo "Re-extracting spec because it was explicitly requested"
  REBUILD=true
fi

if [ ! -d $SPEC_ROOT/compliance ] ; then 
  echo "Compliance directory missing, extracting spec"
  REBUILD=true
fi

if [ $REBUILD == "true" ] ; then
  cd aws-encryption-sdk-specification
  ./util/specification_extract.sh
  cd ..
fi

$SPEC_ROOT/util/report.js $(find src -name '*.dfy') $(find test -name '*.dfy')
