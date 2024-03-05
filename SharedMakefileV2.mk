# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These are make targets that can be shared between all projects
# that use a common layout.
# They will only function if executed inside a project directory.
# See https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/TestModels
# for examples.

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
# GRADLEW -- the gradlew to use when building Java runtimes.
#   defaults to $(SMITHY_DAFNY_ROOT)/codegen/gradlew

MAX_RESOURCE_COUNT := 10000000

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

CODEGEN_CLI_ROOT := $(SMITHY_DAFNY_ROOT)/codegen/smithy-dafny-codegen-cli
GRADLEW := $(SMITHY_DAFNY_ROOT)/codegen/gradlew

########################## Dafny targets

# TODO: This target will not work for projects that use `replaceable` 
#       module syntax with multiple language targets.
# It will fail with error:
# Error: modules 'A' and 'B' both have CompileName 'same.extern.name'
# We need to come up with some way to verify files per-language.
# Rewrite this as part of Java implementation of LanguageSpecificLogic TestModel.

# Proof of correctness for the math below
#  function Z3_PROCESSES(cpus:nat): nat
#  { if cpus >= 3 then 2 else 1 }

#  function DAFNY_PROCESSES(cpus: nat): nat
#   requires 0 < cpus // 0 cpus would do no work!
#  { (cpus - 1 )/Z3_PROCESSES(cpus) }

#  lemma Correct(cpus:nat)
#    ensures DAFNY_PROCESSES(cpus) * Z3_PROCESSES(cpus) <= cpus
#  {}

# Verify the entire project
verify:Z3_PROCESSES=$(shell echo $$(( $(CORES) >= 3 ? 2 : 1 )))
verify:DAFNY_PROCESSES=$(shell echo $$(( ($(CORES) - 1 ) / ($(CORES) >= 3 ? 2 : 1))))
verify:
	find . -name '*.dfy' | xargs -n 1 -P $(DAFNY_PROCESSES) -I % dafny \
		-vcsCores:$(Z3_PROCESSES) \
		-compile:0 \
		-definiteAssignment:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:100 \
		-trace \
		%

# Verify single file FILE with text logger.
# This is useful for debugging resource count usage within a file.
# Use PROC to further scope the verification
verify_single:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
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
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:100 \
		-trace \
		`find ./dafny/$(SERVICE) -name '*.dfy'` \

format_dafny:
	dafny format \
		--function-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

format_dafny-check:
	dafny format \
		--check \
		--function-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count $(MAX_RESOURCE_COUNT) \
		TestResults/*.csv

clean-dafny-report:
	rm TestResults/*.csv

# Dafny helper targets

# Transpile the entire project's impl
# For each index file listed in the project Makefile's PROJECT_INDEX variable,
#   append a `-library:TestModels/$(PROJECT_INDEX) to the transpiliation target
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

# If the project under transpilation uses `replaceable` modules,
#   it MUST define a SRC_INDEX variable per language.
# SRC_INDEX points to the folder containing the `Index.dfy` file for a particular language
#   that `include`s all of that language's `replaces` modules.
# This variable's value might look like (ex.) `src/replaces/net` or `src/replaces/java`.
# If this variable is not provided, assume the project does not have `replaceable` modules,
#   and look for `Index.dfy` in the `src/` directory.
transpile_implementation: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
# At this time it is *significatly* faster
# to give Dafny a single file
# that includes everything
# than it is to pass each file to the CLI.
# ~2m vs ~10s for our large projects.
# Also the expectation is that verification happens in the `verify` target
# `find` looks for `Index.dfy` files in either V1 or V2-styled project directories (single vs. multiple model files).
transpile_implementation:
	find ./dafny/**/$(SRC_INDEX_TRANSPILE)/ ./$(SRC_INDEX_TRANSPILE)/ -name 'Index.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		-stdin \
		-noVerify \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:1 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		$(if $(strip $(STD_LIBRARY)) , -library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSPILE_DEPENDENCIES)

# If the project under transpilation uses `replaceable` modules,
#   it MUST define a SRC_INDEX variable per language.
# The purpose and usage of this is described in the `transpile_implementation` comments.
_transpile_test_all: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
# If the project under transpilation uses `replaceable` modules in its tests
#   it MUST define a TEST_INDEX variable per language.
# TEST_INDEX points to the folder containing all test files for a particular language.
# These files should use Dafny `include`s to include the generic test files as well.
# This variable's value might look like (ex.) `test/replaces/net` or `test/replaces/java`.
# If this variable is not provided, assume the project does not have `replaceable` modules,
#   and look for test files in the `test/` directory.
_transpile_test_all: TEST_INDEX_TRANSPILE=$(if $(TEST_INDEX),$(TEST_INDEX),test)
# If the Makefile defines DIR_STRUCTURE_V2 (i.e. multiple models/subprojects/services in project), then:
#   For each of this project's services defined in PROJECT_SERVICES:
#     append `-library:/path/to/Index.dfy` to the transpile target
# Else: (i.e. single model/service in project), then:
#   append `-library:/path/to/Index.dfy` to the transpile target
_transpile_test_all: TRANSPILE_DEPENDENCIES=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, -library:dafny/%/$(SRC_INDEX_TRANSPILE)/Index.dfy, $(PROJECT_SERVICES)), -library:$(SRC_INDEX_TRANSPILE)/Index.dfy)
# Transpile the entire project's tests
_transpile_test_all: transpile_test

# `find` looks for tests in either V1 or V2-styled project directories (single vs. multiple model files).
transpile_test:
	find ./dafny/**/$(TEST_INDEX_TRANSPILE) ./$(TEST_INDEX_TRANSPILE) -name "*.dfy" -name '*.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		-stdin \
		-noVerify \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:1 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		$(if $(strip $(STD_LIBRARY)) , -library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSPILE_DEPENDENCIES) \

# If we are not the StandardLibrary, transpile the StandardLibrary.
# Transpile all other dependencies
transpile_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) transpile_implementation_$(LANG), )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_implementation_$(LANG);, $(PROJECT_DEPENDENCIES))

########################## Code-Gen targets

# The OUTPUT variables are created this way
# so that it is possible to run _parts_ of polymorph.
# Otherwise it is difficult to run/test only a Dafny change.
# Since they are defined per target
# a single target can decide what parts it wants to build.

# Pass in CODEGEN_CLI_ROOT in command line, e.g.
#   make polymorph_code_gen CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli
# StandardLibrary is filtered out from dependent-model patsubst list;
#   Its model is contained in $(LIBRARY_ROOT)/model, not $(LIBRARY_ROOT)/../StandardLibrary/Model.
_polymorph:
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	--patch-files-dir $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/codegen-patches/$(SERVICE),$(LIBRARY_ROOT)/codegen-patches) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(INPUT_DAFNY) \
	$(OUTPUT_DAFNY) \
	$(OUTPUT_JAVA) \
	$(OUTPUT_DOTNET) \
	$(OUTPUT_JAVA) \
	--model $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(SMITHY_MODEL_ROOT)) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(OUTPUT_LOCAL_SERVICE_$(SERVICE)) \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS) \
	";

_polymorph_wrapped:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(OUTPUT_DAFNY_WRAPPED) \
	$(OUTPUT_DOTNET_WRAPPED) \
	$(OUTPUT_JAVA_WRAPPED) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	--local-service-test \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS)";

_polymorph_dependencies:
	@$(foreach dependency, \
		$(PROJECT_DEPENDENCIES), \
		$(MAKE) -C $(PROJECT_ROOT)/$(dependency) polymorph_$(POLYMORPH_LANGUAGE_TARGET); \
	)

# Generates all target runtime code for all namespaces in this project.
.PHONY: polymorph_code_gen
polymorph_code_gen: POLYMORPH_LANGUAGE_TARGET=code_gen
polymorph_code_gen: _polymorph_dependencies
polymorph_code_gen:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_code_gen ; \
	done

_polymorph_code_gen: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_code_gen: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_code_gen: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_code_gen: _polymorph

check_polymorph_diff:
	git diff --exit-code $(LIBRARY_ROOT) || (echo "ERROR: polymorph-generated code does not match the committed code - see above for diff. Either commit the changes or regenerate with 'POLYMORPH_OPTIONS=--update-patch-files'." && exit 1)

# Generates dafny code for all namespaces in this project
.PHONY: polymorph_dafny
polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
polymorph_dafny: _polymorph_dependencies
polymorph_dafny:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny ; \
	done

_polymorph_dafny: OUTPUT_DAFNY=\
		--output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_dafny: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dafny: _polymorph

# Generates dotnet code for all namespaces in this project
.PHONY: polymorph_dotnet
polymorph_dotnet: POLYMORPH_LANGUAGE_TARGET=dotnet
polymorph_dotnet: _polymorph_dependencies
polymorph_dotnet:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dotnet ; \
	done

_polymorph_dotnet: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_dotnet: _polymorph

# Generates java code for all namespaces in this project
.PHONY: polymorph_java
polymorph_java: POLYMORPH_LANGUAGE_TARGET=java
polymorph_java: _polymorph_dependencies
polymorph_java:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_java ; \
	done

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph

# Dependency for formatting generating Java code
setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5

########################## .NET targets

transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_implementation_net: _transpile_implementation_all

transpile_test_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_test_net: TEST_INDEX=$(NET_TEST_INDEX)
transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: _transpile_test_all

transpile_dependencies_net: LANG=net
transpile_dependencies_net: transpile_dependencies

test_net: FRAMEWORK=net6.0
test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

test_net_mac_intel: FRAMEWORK=net6.0
test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

test_net_mac_brew: FRAMEWORK=net6.0
test_net_mac_brew:
	DYLD_LIBRARY_PATH="$(shell brew --prefix)/opt/openssl@1.1/lib/" dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

setup_net:
	dotnet restore runtimes/net/

format_net:
	dotnet format runtimes/net/*.csproj

format_net-check:
	dotnet format runtimes/net/*.csproj --verify-no-changes

########################## Java targets

build_java: transpile_java mvn_local_deploy_dependencies
	$(GRADLEW) -p runtimes/java build

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
	$(GRADLEW) -p runtimes/java publishMavenLocalPublicationToMavenLocal

# The Java MUST all exsist if we want to publish to CodeArtifact
mvn_ca_deploy:
	$(GRADLEW) -p runtimes/java publishMavenPublicationToPublishToCodeArtifactCIRepository

mvn_staging_deploy:
	$(GRADLEW) -p runtimes/java publishMavenPublicationToPublishToCodeArtifactStagingRepository

test_java:
	$(GRADLEW) -p runtimes/java runTests

_clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj

clean: _clean

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
