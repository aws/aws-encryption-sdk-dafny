# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

verify:
	$(MAKE) -C AwsEncryptionSDK verify CORES=4

dafny-reportgenerator:
	$(MAKE) -C AwsEncryptionSDK dafny-reportgenerator

duvet: | duvet_extract duvet_report

duvet_extract:
	rm -rf compliance
	$(foreach file, $(shell find aws-encryption-sdk-specification/framework -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/client-apis -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/data-format -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)

# TODO add these arguments to duvet_report as the work completes
#		--ci \
#		--require-citations true \
#		--require-tests true \

duvet_report:
	duvet \
		report \
		--spec-pattern "compliance/**/*.toml" \
		--source-pattern "AwsCryptographicMaterialProviders/dafny/**/src/**/*.dfy" \
		--source-pattern "AwsCryptographicMaterialProviders/dafny/**/Model/**/*.smithy" \
		--source-pattern "AwsCryptographicMaterialProviders/compliance_exceptions/**/*.txt" \
		--source-pattern "(# //=,# //#).github/workflows/duvet.yaml" \
		--html specification_compliance_report.html
