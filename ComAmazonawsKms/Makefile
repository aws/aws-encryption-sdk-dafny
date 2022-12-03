# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-verificationLogger:csv \
		-timeLimit:300 \
		-trace \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count 10000000 \
		TestResults/*.csv

compile_net: | compile_implementation_net compile_test_net compile_net_dependencies

compile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy \
		-library:../StandardLibrary/src/Index.dfy

compile_test_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/tests/TestsFromDafny \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

compile_net_dependencies:
	$(MAKE) -C ../StandardLibrary compile_implementation_net

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/

compile_java: | compile_implementation_java compile_test_java compile_java_dependencies

compile_implementation_java: | _clean_implementation_java _compile_implementation_java _mv_implementation_java

_clean_implementation_java:
	rm -rf runtimes/java/temp/ComAmazonawsKms-java/* && rm -rf runtimes/java/src/main/dafny-generated/*

_compile_implementation_java:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:java \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/java/temp/ComAmazonawsKms \
		./src/Index.dfy \
		-library:../StandardLibrary/src/Index.dfy

_mv_implementation_java:
	./runtimes/java/makefile_helper.sh implementation

compile_test_java: | _clean_test_java _compile_test_java _mv_test_java

_clean_test_java:
	rm -rf runtimes/java/temp-tests/ComAmazonawsKmsTests-java/* && rm -rf runtimes/java/src/test/dafny-generated/*

_compile_test_java:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:java \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/java/temp-tests/ComAmazonawsKmsTests \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

_mv_test_java:
	./runtimes/java/makefile_helper.sh test

compile_java_dependencies:
	$(MAKE) -C ../StandardLibrary mvn_local_deploy

test_java:
	gradle -p runtimes/java runTests
