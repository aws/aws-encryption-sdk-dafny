#!/bin/bash

# A simple script for using our Polymorph package to generate
# all relevant code

if [ $# != 1 ] ; then
    echo "Please provide root directory of polymorph"
    exit 1
fi

pushd .

export POLYMORPH_ROOT=$1
export DAFNY_ROOT=`pwd`
export DOTNET_ROOT=$DAFNY_ROOT/aws-encryption-sdk-net-formally-verified
export MODEL_ROOT=$DAFNY_ROOT/model

cd "$POLYMORPH_ROOT"

# Generate code for material providers
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Crypto \
    --output-dafny $DAFNY_ROOT/src/Generated \
    -m $MODEL_ROOT -s aws.crypto#AwsCryptographicMaterialProviders"

# Generate code for ESDK
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Esdk \
    --output-dafny $DAFNY_ROOT/src/Generated \
     -m $MODEL_ROOT -s aws.esdk#AwsEncryptionSdk"


popd
