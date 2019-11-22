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
	   src/Crypto/EncryptionSuites.dfy \
	   src/Crypto/Digests.dfy \
	   src/Crypto/HKDF/CryptoMac.dfy \
	   src/Crypto/HKDF/HKDF.dfy \
	   src/Crypto/HKDF/HKDFSpec.dfy \
	   src/Crypto/Random.dfy \
	   src/Crypto/RSAEncryption.dfy \
	   src/Crypto/Signature.dfy \
	   src/KMS/KMSUtils.dfy \
	   src/Main.dfy \
	   src/SDK/AlgorithmSuite.dfy \
	   src/SDK/Client.dfy \
	   src/SDK/CMM/DefaultCMM.dfy \
	   src/SDK/CMM/Defs.dfy \
	   src/SDK/Deserialize.dfy \
	   src/SDK/Keyring/Defs.dfy \
	   src/SDK/Keyring/KMSKeyring.dfy \
	   src/SDK/Keyring/MultiKeyring.dfy \
	   src/SDK/Keyring/RawAESKeyring.dfy \
	   src/SDK/Keyring/RawRSAKeyring.dfy \
	   src/SDK/Materials.dfy \
	   src/SDK/MessageBody.dfy \
	   src/SDK/MessageHeader.dfy \
	   src/SDK/Serialize.dfy \
	   src/SDK/ToyClient.dfy \
	   src/StandardLibrary/Base64.dfy \
	   src/StandardLibrary/StandardLibrary.dfy \
	   src/StandardLibrary/UInt.dfy \
	   src/Util/Arrays.dfy \
	   src/Util/Streams.dfy \
	   src/Util/UTF8.dfy \

SRCV = $(patsubst src/%.dfy, build/%.dfy.verified, $(SRCS))

DEPS_CS = $(wildcard src/extern/dotnet/*.cs)

BCDLL = lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

AWSDLLS = lib/AWSSDK.KeyManagementService.3.3.101.83/lib/net45/AWSSDK.KeyManagementService.dll \
		  lib/AWSSDK.Core.3.3.103.62/lib/net45/AWSSDK.Core.dll

DEPS = $(DEPS_CS) $(BCDLL) $(AWSDLLS)

.PHONY: all release build verify buildcs hkdf test clean-test clean-build clean

all: verify build test

release: all

build: build/Main.exe

verify: clean-build $(SRCV)

build/%.dfy.verified: src/%.dfy
	$(DAFNY) $(patsubst build/%.dfy.verified, src/%.dfy, $@) /timeLimit:30 /compile:0 && mkdir -p $(dir $@) && touch $@

build/Main.exe: $(SRCS) $(DEPS)
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(DEPS) build/

buildjs: $(SRCS)
	$(DAFNY) /out:build/Main $(SRCS) /compile:2 /noVerify /noIncludes /compileTarget:js /spillTargetCode:1

buildcs: build/Main.cs
	csc /r:System.Numerics.dll /r:$(BCDLL) /target:exe /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 build/Main.cs $(DEPS_CS) /out:build/Main.exe

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

test: $(DEPS) clean-test
	lit test -q -v

clean-test:
	$(RM) test/**/Output/*

clean-build:
	$(RM) -r build/*

clean: clean-build clean-test
	$(RM) -r lib/*
