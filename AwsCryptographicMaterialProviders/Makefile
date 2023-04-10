# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefileV2.mk

PROJECT_SERVICES := \
	AwsCryptographicMaterialProviders \
	AwsCryptographyKeyStore \

SERVICE_NAMESPACE_AwsCryptographicMaterialProviders=aws.cryptography.materialProviders
SERVICE_NAMESPACE_AwsCryptographyKeyStore=aws.cryptography.keyStore

MAX_RESOURCE_COUNT=50000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	AwsCryptographyPrimitives \
	ComAmazonawsKms \
	ComAmazonawsDynamodb

PROJECT_INDEX := \
	AwsCryptographyPrimitives/src/Index.dfy \
	ComAmazonawsKms/src/Index.dfy \
	ComAmazonawsDynamodb/src/Index.dfy

STD_LIBRARY=StandardLibrary
SMITHY_DEPS=model

# Dependencies for each local service
SERVICE_DEPS_AwsCryptographicMaterialProviders := \
	AwsCryptographyPrimitives \
	ComAmazonawsKms \
	ComAmazonawsDynamodb \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore \

SERVICE_DEPS_AwsCryptographyKeyStore := \
	AwsCryptographyPrimitives \
	ComAmazonawsKms \
	ComAmazonawsDynamodb \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders \

format_net:
	pushd runtimes/net && dotnet format && popd
