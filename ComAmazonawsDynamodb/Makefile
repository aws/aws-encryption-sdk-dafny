# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
DEPS_DIR:=$(ROOT_DIR)/..
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

transpile_net: | transpile_implementation_net transpile_net_dependencies

transpile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-optimizeErasableDatatypeWrapper:0 \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy \
		-library:$(DEPS_DIR)/StandardLibrary/src/Index.dfy

transpile_net_dependencies:
	$(MAKE) -C $(DEPS_DIR)/StandardLibrary transpile_implementation_net

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

transpile_java: | transpile_implementation_java

transpile_implementation_java: | _clean_implementation_java _transpile_implementation_java _mv_implementation_java

_clean_implementation_java:
	rm -rf runtimes/java/temp/ComAmazonawsDynamodb-java/* && rm -rf runtimes/java/src/main/dafny-generated/*

_transpile_implementation_java:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:java \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-optimizeErasableDatatypeWrapper:0 \
		-out runtimes/java/temp/ComAmazonawsDynamodb \
		./src/Index.dfy \
		-library:$(DEPS_DIR)/StandardLibrary/src/Index.dfy

_mv_implementation_java:
	./runtimes/java/makefile_helper.sh implementation

build_java_dependencies:
	$(MAKE) -C $(DEPS_DIR)/StandardLibrary mvn_local_deploy

mvn_local_deploy: transpile_java
	gradle -p runtimes/java publishToMavenLocal

build_java: transpile_java build_java_dependencies
	gradle -p runtimes/java build
