# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefileV2.mk

DIR_STRUCTURE_V2=V2

PROJECT_SERVICES := \
	ESDK \

SMITHY_MODEL_ROOT := $(PROJECT_ROOT)/AwsEncryptionSDK/dafny/AwsEncryptionSdk/Model
OUTPUT_LOCAL_SERVICE_ESDK := --local-service-test

SERVICE_NAMESPACE_ESDK=aws.cryptography.encryptionSdk

MAX_RESOURCE_COUNT=10000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	mpl/AwsCryptographyPrimitives \
	mpl/ComAmazonawsKms \
	mpl/ComAmazonawsDynamodb \
	mpl/AwsCryptographicMaterialProviders \
	mpl/TestVectorsAwsCryptographicMaterialProviders \
	AwsEncryptionSDK \

# Since we are packaging projects differently, we cannot make assumptions
# about where the files are located. 
# This is here to get unblocked but should be removed once we have migrated packages
# to the new packaging format.
PROJECT_INDEX := \
	mpl/AwsCryptographyPrimitives/src/Index.dfy \
	mpl/ComAmazonawsKms/src/Index.dfy \
	mpl/ComAmazonawsDynamodb/src/Index.dfy \
	mpl/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/Index.dfy \
	mpl/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/src/Index.dfy \
	mpl/TestVectorsAwsCryptographicMaterialProviders/dafny/KeyVectors/src/Index.dfy \
	mpl/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/Index.dfy \
	AwsEncryptionSDK/dafny/AwsEncryptionSdk/src/Index.dfy \

STD_LIBRARY=mpl/StandardLibrary
SMITHY_DEPS=mpl/model


# Dependencies for each local service
SERVICE_DEPS_ESDK := \
	mpl/AwsCryptographyPrimitives \
	mpl/ComAmazonawsKms \
	mpl/ComAmazonawsDynamodb \
	mpl/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders \
	mpl/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore \
	AwsEncryptionSDK/dafny/AwsEncryptionSdk \
	mpl/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders \


format_net:
	pushd runtimes/net && dotnet format && popd
