# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

SMITHY_MODEL_ROOT := $(PROJECT_ROOT)/AwsCryptographicMaterialProviders/Model
OUTPUT_LOCAL_SERVICE := --local-service-test

SMITHY_NAMESPACE=aws.cryptography.materialProviders
MAX_RESOURCE_COUNT=10000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
LIBRARIES := \
	AwsCryptographyPrimitives \
	ComAmazonawsKms \
	ComAmazonawsDynamodb \
	AwsCryptographicMaterialProviders

format_net:
	pushd runtimes/net && dotnet format && popd
