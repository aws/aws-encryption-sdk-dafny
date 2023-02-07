# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These make targets that are shared
# between all the Dafny projects
# in this repo.
# They will only function if executed inside a project directory.

# There are serveral variables that are used here.
# The expectation is to define these variables
# inside each project.

# Variables:
# MAX_RESOURCE_COUNT -- The Dafny report generator max resource count.
# 	This is is per project because the verification variability can differ.
# LIBRARIES -- List of dependencies for the project.
# 	It should be the list of top leve directory names
# SMITHY_NAMESPACE -- The smithy namespace to use for code generation. 
# AWS_SDK_CMD -- the `--aws-sdk` command to generate AWS SDK style interfaces

# This evaluates to the local path _of this file_
ESDK_ROOT := $(realpath $(dir $(realpath $(lastword $(MAKEFILE_LIST)))))
# This evaluates to the path of the current working directory
PROJECT_ROOT = $(PWD)

########################## Dafny targets

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
		--max-resource-count $(MAX_RESOURCE_COUNT) \
		TestResults/*.csv

# Dafny helper targets

# In windows `patsubst` is unhappy with $(VAR)%
# So rather than use $(ESDK_ROOT)% we use $(PROJECT_ROOT)/../%
# 
# The `$(OUT)` and $(TARGET) variables are problematic.
# Idealy they are different for every target call.
# However the way make evaluates variables
# having a target specific variable is hard.
# This all comes up because a project
# will need to also transpile its dependencies.
# This is worked around for now,
# by the fact that the `TARGET`
# for all these transpile calls will be the same.
# For `OUT` this is solved by makeing the paths realative.
# So that the runtime is express once
# and can be the same for all such runtimes.
# Since such targets are all shared,
# this is tractable.
transpile_implementation:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-useRuntimeLib \
		-out $(OUT) \
		./src/Index.dfy \
		$(patsubst %, -library:$(PROJECT_ROOT)/../%/src/Index.dfy, $(LIBRARIES))

transpile_test:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-useRuntimeLib \
		-out $(OUT) \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

# In windows `patsubst` is unhappy with $(VAR)%
# So rather than use $(ESDK_ROOT)% we use $(PROJECT_ROOT)/../%
transpile_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/../% transpile_implementation_$(LANG);, $(LIBRARIES))

########################## Code-Gen targets

polymorph_code_gen :
	cd $(POLYMORPH_ROOT); \
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(ESDK_ROOT)/StandardLibrary/src/Index.dfy \
	--output-dotnet $(PROJECT_ROOT)/runtimes/net/Generated/ \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(ESDK_ROOT)/model \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/../%/Model, $(LIBRARIES)) \
	--namespace $(SMITHY_NAMESPACE)
	$(AWS_SDK_CMD)";

########################## .NET targets

transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: transpile_implementation

transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: transpile_test

transpile_dependencies_net: LANG=net
transpile_dependencies_net: transpile_dependencies

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_brew:
	DYLD_LIBRARY_PATH="$(brew --prefix)/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/

########################## Java targets

build_java: transpile_java mvn_local_deploy_dependencies 
	gradle -p runtimes/java build

transpile_java: | transpile_implementation_java transpile_test_java transpile_dependencies_java

transpile_implementation_java: TARGET=java
transpile_implementation_java: OUT=runtimes/java/ImplementationFromDafny
transpile_implementation_java: transpile_implementation _mv_implementation_java

transpile_test_java: TARGET=java
transpile_test_java: OUT=runtimes/java/TestsFromDafny
transpile_test_java: transpile_test _mv_test_java

# Currently Dafny compiles to Java by changing the directory name.
# Java puts things under a `java` directory.
# To avoid `java/implementation-java` the code is generated and then moved.
_mv_implementation_java:
	rm -rf runtimes/java/src/main/dafny-generated
	mv runtimes/java/ImplementationFromDafny-java runtimes/java/src/main/dafny-generated
_mv_test_java:
	rm -rf runtimes/java/src/test/dafny-generated
	mkdir -p runtimes/java/src/test
	mv runtimes/java/TestsFromDafny-java runtimes/java/src/test/dafny-generated

transpile_dependencies_java: LANG=java
transpile_dependencies_java: transpile_dependencies

# In windows `patsubst` is unhappy with $(VAR)%
# So rather than use $(ESDK_ROOT)% we use $(PROJECT_ROOT)/../%
mvn_local_deploy_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/../% mvn_local_deploy;, $(LIBRARIES))

# The Java MUST all exist already through the transpile step.
mvn_local_deploy:
	gradle -p runtimes/java publishToMavenLocal

test_java:
	gradle -p runtimes/java runTests
