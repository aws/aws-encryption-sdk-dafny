

verify:
	CORES=4 $(MAKE) -C AwsCryptographyPrimitives verify
	CORES=4 $(MAKE) -C ComAmazonawsKms verify
	CORES=4 $(MAKE) -C AwsCryptographicMaterialProviders verify

duvet: | duvet_extract duvet_report

duvet_extract:
	rm -rf compliance
	$(foreach file, $(shell find aws-encryption-sdk-specification/framework -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/client-apis -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/data-format -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)

duvet_report:
	duvet \
		report \
		--ci \
		--require-citations true \
		--require-tests true \
		--spec-pattern "compliance/**/*.toml" \
		--source-pattern "AwsCryptographicMaterialProviders/src/**/*.dfy" \
		--source-pattern "AwsCryptographicMaterialProviders/Model/**/*.smithy" \
		--html specification_compliance_report.html
