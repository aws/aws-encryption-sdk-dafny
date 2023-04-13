

verify:
	$(MAKE) -C StandardLibrary verify CORES=4
	$(MAKE) -C AwsCryptographyPrimitives verify CORES=4
	$(MAKE) -C ComAmazonawsKms verify CORES=4
	$(MAKE) -C ComAmazonawsDynamodb verify CORES=4
	$(MAKE) -C AwsCryptographicMaterialProviders verify CORES=4
	$(MAKE) -C AwsEncryptionSDK verify CORES=4

dafny-reportgenerator:
	$(MAKE) -C StandardLibrary dafny-reportgenerator
	$(MAKE) -C AwsCryptographyPrimitives dafny-reportgenerator
	$(MAKE) -C ComAmazonawsKms dafny-reportgenerator
	$(MAKE) -C ComAmazonawsDynamodb dafny-reportgenerator
	$(MAKE) -C AwsCryptographicMaterialProviders dafny-reportgenerator
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
		--source-pattern "AwsCryptographicMaterialProviders/src/**/*.dfy" \
		--source-pattern "AwsCryptographicMaterialProviders/Model/**/*.smithy" \
		--source-pattern "AwsCryptographicMaterialProviders/compliance_exceptions/**/*.txt" \
		--source-pattern "(# //=,# //#).github/workflows/duvet.yaml" \
		--html specification_compliance_report.html
