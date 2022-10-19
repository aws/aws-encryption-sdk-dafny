# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-verificationLogger:trx \
		-timeLimit:300 \
		-trace \
		./src/*.dfy ./src/**/*.dfy \
		./test/*.dfy

compile_net: | compile_implementation_net compile_test_net

compile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/*.dfy

compile_test_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/tests/TestsFromDafny \
		./test/*.dfy \
		-library:src/Index.dfy

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/
