ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif

# TODO: Temporary subset of files to build and verify.
# Add to this as more files can be verified.
# Eventually this can be something like:
# SRCS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.dfy))
SRCS = \
	   src/Crypto/AESEncryption.dfy \
	   src/Crypto/Cipher.dfy \
	   src/Crypto/Digests.dfy \
	   src/Crypto/GenBytes.dfy \
	   src/Crypto/RSAEncryption.dfy \
	   src/Crypto/Signature.dfy \
	   src/Main.dfy \
	   src/SDK/AlgorithmSuite.dfy \
	   src/SDK/CMM/DefaultCMM.dfy \
	   src/SDK/CMM/Defs.dfy \
	   src/SDK/Keyring/AESKeyring.dfy \
	   src/SDK/Keyring/Defs.dfy \
	   src/SDK/Keyring/RSAKeyring.dfy \
	   src/SDK/Materials.dfy \
	   src/SDK/ToyClient.dfy \
	   src/StandardLibrary/Base64.dfy \
	   src/StandardLibrary/StandardLibrary.dfy \
	   src/StandardLibrary/UInt.dfy \

SRCV = $(patsubst src/%.dfy, build/%.dfy.verified, $(SRCS))

BCDLL = lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

SRCDIRS = $(dir $(SRCS))

DEPS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.cs)) \
	$(BCDLL)

.PHONY: all hkdf test noverif clean-build clean

all: verify build test

release: all

build: build/Main.exe

verify: clean-build $(SRCV)

build/%.dfy.verified: src/%.dfy
	$(DAFNY) $(patsubst build/%.dfy.verified, src/%.dfy, $@) /compile:0 && mkdir -p $(dir $@) && touch $@

build/Main.exe: $(SRCS) $(DEPS)
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/

# TODO: HKDF.dfy hasn't been reviewed yet.
# Once it is, re-add:
#
# OTHERSRCS = $(filter-out src/Crypto/HKDF/HKDF.dfy,$(SRCS))
# build/HKDF.dll: $(SRCV) $(DEPS)
# 	$(DAFNY) /out:build/HKDF src/Crypto/HKDF/HKDF.dfy $(OTHERSRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/
#
# hkdf: build/HKDF.dll

lib/%.dll:
	nuget install

test: $(DEPS)
	lit test -q -v

noverif: $(DEPS)
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/

clean-build:
	$(RM) -r build/*

clean: clean-build
	$(RM) -r lib/*
