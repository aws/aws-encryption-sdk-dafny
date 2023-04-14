# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefileV2.mk

PROJECT_SERVICES := \
	TestVectorsAwsCryptographicMaterialProviders \

SMITHY_MODEL_ROOT := $(PROJECT_ROOT)/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/Model
OUTPUT_LOCAL_SERVICE := --local-service-test

SERVICE_NAMESPACE_TestVectorsAwsCryptographicMaterialProviders=aws.cryptography.materialProviders

MAX_RESOURCE_COUNT=10000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	AwsCryptographyPrimitives \
	ComAmazonawsKms \
	ComAmazonawsDynamodb \
	AwsCryptographicMaterialProviders

# Since we are packaging projects differently, we cannot make assumptions
# about where the files are located. 
# This is here to get unblocked but should be removed once we have migrated packages
# to the new packaging format.
PROJECT_INDEX := \
	AwsCryptographyPrimitives/src/Index.dfy \
	ComAmazonawsKms/src/Index.dfy \
	ComAmazonawsDynamodb/src/Index.dfy \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/Index.dfy \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/src/Index.dfy \

STD_LIBRARY=StandardLibrary
SMITHY_DEPS=model

# LIBRARY_MODEL := \
# 	AwsCryptographyPrimitives/Model \
# 	ComAmazonawsKms/Model \
# 	ComAmazonawsDynamodb/Model \
# 	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/Model

format_net:
	pushd runtimes/net && dotnet format && popd
