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

compile_net: | compile_implementation_net

compile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy

setup_net:
	dotnet restore runtimes/net/

compile_java: compile_implementation_java

compile_implementation_java: | _clean_implementation_java _compile_implementation_java _mv_implementation_java

_clean_implementation_java:
	rm -rf runtimes/java/temp/StandardLibrary-java/* && \
	rm -rf runtimes/java/src/main/dafny-generated/*

_compile_implementation_java:
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

setup_java:
	gradle -p runtimes/java assemble

mvn_local_deploy: compile_java
	gradle -p runtimes/java publishToMavenLocal
