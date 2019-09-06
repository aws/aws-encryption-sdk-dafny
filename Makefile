ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif

# TODO: Temporary subset of files to build and verify.
# Add to this as more files can be verified.
# Eventually this can be something like:
# SRCS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.dfy))
SRCS = src/SDK/AlgorithmSuite.dfy \
	   src/SDK/Common.dfy \
	   src/SDK/Keyring/Defs.dfy \
	   src/StandardLibrary/StandardLibrary.dfy \
	   src/StandardLibrary/UInt.dfy \

SRCV = $(patsubst src/%.dfy, build/%.dfy.verified, $(SRCS))

BCDLL = lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

DEPS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.cs)) \
	$(BCDLL)

.PHONY: all hkdf test noverif clean-build clean

all: build test

build: build/Main.exe

verify: clean-build $(SRCV)

build/%.dfy.verified: src/%.dfy
	$(DAFNY) $(patsubst build/%.dfy.verified, src/%.dfy, $@) /compile:0 /compileVerbose:1 && mkdir -p $(dir $@) && touch $@

build/Main.exe: verify $(DEPS) 
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes /compileVerbose:1 && cp $(BCDLL) build/

# TODO: HKDF.dfy cannot be verified yet.
# Once it can, re-add:
#
# OTHERSRCS = $(filter-out src/Crypto/HKDF/HKDF.dfy,$(SRCS))
# build/HKDF.dll: $(SRCV) $(DEPS) 
# 	$(DAFNY) /out:build/HKDF src/Crypto/HKDF/HKDF.dfy $(OTHERSRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/
#
# hkdf: build/HKDF.dll

lib/%.dll:
	nuget install

test:
	lit test -q -v

noverif: $(DEPS)
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes /compileVerbose:1 && cp $(BCDLL) build/

clean-build:
	rm -r build/*

clean: clean-build
	rm -r lib/*
