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
export DOTNET_ROOT=$DAFNY_ROOT/aws-encryption-sdk-net

export ESDK_ROOT=$DAFNY_ROOT/src/SDK
export MaterialProviders_ROOT=$DAFNY_ROOT/AwsCryptographicMaterialProviders
export AwsCryptographyPrimitives_ROOT=$DAFNY_ROOT/AwsCryptographyPrimitives
export ComAmazonawsKms_ROOT=$DAFNY_ROOT/ComAmazonawsKms
export ComAmazonawsDynamodb_ROOT=$DAFNY_ROOT/ComAmazonawsDynamodb


cd "$POLYMORPH_ROOT"

# Generate code for the AWS KMS SDK
./gradlew run --args="\
    --output-dafny \
    --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
    --output-dotnet $ComAmazonawsKms_ROOT/runtimes/net/Generated/ \
    --output-java $ComAmazonawsKms_ROOT/runtimes/java/src/main/smithy-generated \
    --model $ComAmazonawsKms_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace com.amazonaws.kms \
    --aws-sdk"

# Generate code from AWS DDB SDK
# TODO generate .NET code
# TODO the generated Dafny code requires some manual updates,
# Documented at ComAmazonawsDynamodb/README.md
#
# ./gradlew run --args="\
#     --output-dafny \
#     --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
#     --model $ComAmazonawsDynamodb_ROOT/Model \
#     --dependent-model $DAFNY_ROOT/model \
#     --namespace com.amazonaws.dynamodb \
#     --aws-sdk"

# Generate code for cryptographic primitives
./gradlew run --args="\
    --output-dafny \
    --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
    --output-dotnet $AwsCryptographyPrimitives_ROOT/runtimes/net/Generated/ \
    --output-java $AwsCryptographyPrimitives_ROOT/runtimes/java/src/main/smithy-generated \
    --model $AwsCryptographyPrimitives_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace aws.cryptography.primitives"

# Generate code for material providers
./gradlew run --args="\
    --output-dafny \
    --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
    --output-dotnet $MaterialProviders_ROOT/runtimes/net/Generated/ \
    --output-java $MaterialProviders_ROOT/runtimes/java/src/main/smithy-generated \
    --model $MaterialProviders_ROOT/Model \
    --dependent-model $ComAmazonawsKms_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --dependent-model $AwsCryptographyPrimitives_ROOT/Model \
    --namespace aws.cryptography.materialProviders"

# # Generate code for ESDK
# ./gradlew run --args="\
#     --output-dotnet $ESDK_ROOT/runtimes/net/Generated/ \
#     --model $ESDK_ROOT/Model \
#     --dependent-model $MaterialProviders_ROOT/Model \
#     --dependent-model $DAFNY_ROOT/model \
#     --dependent-model $ComAmazonawsKms_ROOT/Model \
#     --dependent-model $AwsCryptographyPrimitives_ROOT/Model \
#     --namespace aws.encryptionSdk"

popd
