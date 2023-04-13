# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
CORES=2

include ../SharedMakefile.mk

SMITHY_NAMESPACE=aws.encryptionSdk
MAX_RESOURCE_COUNT=100000000
# Order is important
# In java they MUST be built
# in the order they depend on each other
LIBRARIES := \
	AwsCryptographyPrimitives \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders \
	ComAmazonawsKms \
	ComAmazonawsDynamodb

# Since we are packaging projects differently, we cannot make assumptions
# about where the files are located. 
# This is here to get unblocked but should be removed once we have migrated packages
# to the new packaging format.
LIBRARIES_INDEX := \
	AwsCryptographyPrimitives/src/Index.dfy \
	ComAmazonawsKms/src/Index.dfy \
	ComAmazonawsDynamodb/src/Index.dfy \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/Index.dfy \

LIBRARY_MODEL := \
	AwsCryptographyPrimitives/Model \
	ComAmazonawsKms/Model \
	ComAmazonawsDynamodb/Model \
	AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/Model
