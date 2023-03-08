# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
CORES=2

include ../SharedMakefile.mk

SMITHY_NAMESPACE=aws.encryptionSdk
MAX_RESOURCE_COUNT=200000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
LIBRARIES := \
	StandardLibrary \
	AwsCryptographyPrimitives \
	AwsCryptographicMaterialProviders \
	ComAmazonawsKms \
	ComAmazonawsDynamodb
