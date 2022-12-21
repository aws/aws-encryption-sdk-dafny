# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
POLYMORPH_ROOT="../../polymorph/smithy-polymorph"

verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-verificationLogger:csv \
		-timeLimit:300 \
		-trace \
		-verifyAllModules \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count 50000000 \
		TestResults/*.csv

transpile_net: | transpile_implementation_net transpile_test_net

transpile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy

transpile_test_net:
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

transpile_java: transpile_implementation_java transpile_test_java

transpile_implementation_java: | _clean_implementation_java _transpile_implementation_java _mv_implementation_java

_clean_implementation_java:
	rm -rf runtimes/java/temp/StandardLibrary-java/* && \
	rm -rf runtimes/java/src/main/dafny-generated/*

_transpile_implementation_java:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:java \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/java/temp/StandardLibrary \
		./src/Index.dfy

_mv_implementation_java:
	./runtimes/java/makefile_helper.sh implementation

transpile_test_java: | _clean_test_java _transpile_test_java _mv_test_java

_clean_test_java:
	rm -rf runtimes/java/temp-tests/StandardLibraryTests-java/* && rm -rf runtimes/java/src/test/dafny-generated/*

_transpile_test_java:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:java \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/java/temp-tests/StandardLibraryTests \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

_mv_test_java:
	./runtimes/java/makefile_helper.sh test

setup_java:
	gradle -p runtimes/java assemble

build_java: transpile_java
	gradle -p runtimes/java build

mvn_local_deploy: transpile_java
	gradle -p runtimes/java publishToMavenLocal

test_java:
	gradle -p runtimes/java runTests
