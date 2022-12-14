# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
DEPS_DIR:=$(ROOT_DIR)/..
CORES=2

transpile_net: | transpile_implementation_net transpile_net_dependencies

transpile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy \
		-library:$(DEPS_DIR)/StandardLibrary/src/Index.dfy

transpile_net_dependencies:
	$(MAKE) -C $(DEPS_DIR)/StandardLibrary transpile_implementation_net

setup_net:
	dotnet restore runtimes/net/
