# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These make targets that are shared
# between all the projects in this repo.
# They will only function if executed inside a project directory.

# There are several variables that are used here.
# The expectation is to define these variables
# inside each project.

# Variables:
# MAX_RESOURCE_COUNT -- The Dafny report generator max resource count.
# 	This is is per project because the verification variability can differ.
# PROJECT_DEPENDENCIES -- List of dependencies for the project.
# 	It should be the list of top level directory names
# PROJECT_SERVICES -- List of names of each local service in the project
# SERVICE_NAMESPACE_<service> -- for each service in PROJECT_SERVICES,
#   the list of dependencies for that smithy namespace. It should be a list
#   of Model directories
# SERVICE_DEPS_<service> -- for each service in PROJECT_SERVICES,
#   the list of dependencies for that smithy namespace. It should be a list
#   of Model directories
# AWS_SDK_CMD -- the `--aws-sdk` command to generate AWS SDK style interfaces.
# STD_LIBRARY -- path from this file to the StandardLibrary Dafny project.
# SMITHY_DEPS -- path from this file to smithy dependencies, such as custom traits.

# This evaluates to the local path _of this file_.
# This means that these are the project roots
# that are shared by all libraries in this repo.
PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
# This evaluates to the path of the current working directory.
# i.e. The specific library under consideration.
LIBRARY_ROOT := $(PWD)
# Smithy Dafny code gen needs to know
# where the smithy model is.
# This is generally in the same directory as the library.
# However in the case of a wrapped library,
# such as the test vectors
# the implementation MAY be in a different library
# than the model.
# By having two related variables
# test vector projects can point to
# the specific model they need
# but still build everything in their local library directory.
SMITHY_MODEL_ROOT := $(LIBRARY_ROOT)/Model

########################## Dafny targets

# Verify the entire project
verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:100 \
		-trace \
		`find . -name *.dfy`

# Verify single file FILE with text logger.
# This is useful for debugging resource count usage within a file.
# Use PROC to further scope the verification
verify_single:
	@: $(if ${CORES},,CORES=2);
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:text \
		-timeLimit:100 \
		-trace \
		$(if ${PROC},-proc:*$(PROC)*,) \
		$(FILE)

#Verify only a specific namespace at env var $(SERVICE)
verify_service:
	@: $(if ${SERVICE},,$(error You must pass the SERVICE to generate for));
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:100 \
		-trace \
		`find ./dafny/$(SERVICE) -name '*.dfy'` \

format:
	dafny format \
		--function-syntax 3 \
		--quantifier-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

format-check:
	dafny format \
		--check \
		--function-syntax 3 \
		--quantifier-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count $(MAX_RESOURCE_COUNT) \
		TestResults/*.csv

# Dafny helper targets

# Transpile the entire project's impl
_transpile_implementation_all: TRANSPILE_TARGETS=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, ./dafny/%/src/Index.dfy, $(PROJECT_SERVICES)), src/Index.dfy)
_transpile_implementation_all: TRANSPILE_DEPENDENCIES=$(patsubst %, -library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX))
_transpile_implementation_all: transpile_implementation

# The `$(OUT)` and $(TARGET) variables are problematic.
# Ideally they are different for every target call.
# However the way make evaluates variables
# having a target specific variable is hard.
# This all comes up because a project
# will need to also transpile its dependencies.
# This is worked around for now,
# by the fact that the `TARGET`
# for all these transpile calls will be the same.
# For `OUT` this is solved by making the paths relative.
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
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		$(TRANSPILE_TARGETS) \
		$(if $(strip $(STD_LIBRARY)) , -library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSPILE_DEPENDENCIES)

# Transpile the entire project's tests
_transpile_test_all: TRANSPILE_TARGETS=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, `find ./dafny/%/test -name '*.dfy'`, $(PROJECT_SERVICES)), `find ./test -name '*.dfy'`)
_transpile_test_all: TRANSPILE_DEPENDENCIES=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, -library:dafny/%/src/Index.dfy, $(PROJECT_SERVICES)), -library:src/Index.dfy)
_transpile_test_all: transpile_test

transpile_test:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		$(TRANSPILE_TARGETS) \
		$(if $(strip $(STD_LIBRARY)) , -library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSPILE_DEPENDENCIES)


# If we are not the StandardLibrary, transpile the StandardLibrary.
# Transpile all other dependencies
transpile_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) transpile_implementation_$(LANG), )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_implementation_$(LANG);, $(PROJECT_DEPENDENCIES))

########################## Code-Gen targets

# StandardLibrary is filtered out from dependent-model patsubst list;
#   Its model is contained in $(LIBRARY_ROOT)/model, not $(LIBRARY_ROOT)/../StandardLibrary/Model.

# The OUTPUT variables are created this way
# so that it is possible to run _parts_ of polymorph.
# Otherwise it is difficult to run/test only a Dafny change.
# Since they are defined per target
# a single target can decide what parts it wants to build.

_polymorph:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/[path]/[to]/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	$(OUTPUT_DAFNY) \
	$(OUTPUT_JAVA) \
	--model $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(SMITHY_MODEL_ROOT)) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(AWS_SDK_CMD) \
	$(OUTPUT_LOCAL_SERVICE_$(SERVICE)) \
	";

# Generates all target runtime code for all namespaces in this project.
.PHONY: polymorph_code_gen
polymorph_code_gen:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_code_gen || exit 1; \
	done

_polymorph_code_gen: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_code_gen: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_code_gen: _polymorph

# Generates dafny code for all namespaces in this project
.PHONY: polymorph_dafny
polymorph_dafny:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny || exit 1; \
	done

_polymorph_dafny: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dafny: _polymorph

# Generates dotnet code for all namespaces in this project
.PHONY: polymorph_dotnet
polymorph_dotnet:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dotnet || exit 1; \
	done

_polymorph_dotnet: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_dotnet: _polymorph

# Generates java code for all namespaces in this project
.PHONY: polymorph_java
polymorph_java:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_java || exit 1; \
	done

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph

########################## .NET targets

transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: _transpile_implementation_all

transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: _transpile_test_all

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
	DYLD_LIBRARY_PATH="$(shell brew --prefix)/opt/openssl@1.1/lib/" dotnet run \
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
transpile_implementation_java: _transpile_implementation_all _mv_implementation_java

transpile_test_java: TARGET=java
transpile_test_java: OUT=runtimes/java/TestsFromDafny
transpile_test_java: _transpile_test_all _mv_test_java

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

# If we are not StandardLibrary, locally deploy the StandardLibrary.
# Locally deploy all other dependencies 
mvn_local_deploy_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) mvn_local_deploy, )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% mvn_local_deploy;, $(PROJECT_DEPENDENCIES))

# The Java MUST all exist already through the transpile step.
mvn_local_deploy:
	gradle -p runtimes/java publishToMavenLocal

test_java:
    # run Dafny generated tests
	gradle -p runtimes/java runTests

########################## local testing targets

# These targets are added as a convenience for local development.
# If you experience weird behavior using these targets,
# fall back to the regular `build` or `test` targets.
# These targets MUST only be used for local testing,
# and MUST NOT be used in CI.

# Targets to transpile single local service for convenience.
# Specify the local service to build by passing a SERVICE env var.
# Note that this does not generate identical files as `transpile_implementation_java`

local_transpile_impl_java_single: TARGET=java
local_transpile_impl_java_single: OUT=runtimes/java/ImplementationFromDafny
local_transpile_impl_java_single: local_transpile_impl_single
	cp -R runtimes/java/ImplementationFromDafny-java/* runtimes/java/src/main/dafny-generated
	rm -rf runtimes/java/ImplementationFromDafny-java/

local_transpile_impl_net_single: TARGET=cs
local_transpile_impl_net_single: OUT=runtimes/net/ImplementationFromDafny
local_transpile_impl_net_single: local_transpile_impl_single

local_transpile_impl_single: deps_var=SERVICE_DEPS_$(SERVICE)
local_transpile_impl_single: TRANSPILE_TARGETS=./dafny/$(SERVICE)/src/$(FILE)
local_transpile_impl_single: TRANSPILE_DEPENDENCIES= \
		$(patsubst %, -library:$(PROJECT_ROOT)/%/src/Index.dfy, $($(deps_var))) \
		$(patsubst %, -library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX)) \
		-library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
local_transpile_impl_single: transpile_implementation

# Targets to transpile single local service for convenience.
# Specify the local service to build by passing a SERVICE env var.
# Note that this does not generate identical files as `transpile_test_java`,
# and will clobber tests generated by other services.

local_transpile_test_java_single: TARGET=java
local_transpile_test_java_single: OUT=runtimes/java/TestsFromDafny
local_transpile_test_java_single: local_transpile_test_single
	cp -R runtimes/java/TestsFromDafny-java/* runtimes/java/src/test/dafny-generated
	rm -rf runtimes/java/TestsFromDafny-java

local_transpile_test_net_single: TARGET=cs
local_transpile_test_net_single: OUT=runtimes/net/tests/TestsFromDafny
local_transpile_test_net_single: local_transpile_test_single

local_transpile_test_single: TRANSPILE_TARGETS=./dafny/$(SERVICE)/test/$(FILE)
local_transpile_test_single: TRANSPILE_DEPENDENCIES= \
		$(patsubst %, -library:dafny/%/src/Index.dfy, $(PROJECT_SERVICES)) \
		$(patsubst %, -library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX)) \
		-library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
local_transpile_test_single: transpile_test
