ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif

# TODO: Temporary subset of files to build and verify.
# Add to this as more files can be verified.
# Eventually this can be something like:
# SRCS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.dfy))
LIBSRCS = \
	   src/Crypto/AESEncryption.dfy \
	   src/Crypto/EncryptionSuites.dfy \
	   src/Crypto/Digests.dfy \
	   src/Crypto/HKDF/CryptoMac.dfy \
	   src/Crypto/HKDF/HKDF.dfy \
	   src/Crypto/HKDF/HKDFSpec.dfy \
	   src/Crypto/Random.dfy \
	   src/Crypto/RSAEncryption.dfy \
	   src/Crypto/Signature.dfy \
	   src/SDK/AlgorithmSuite.dfy \
	   src/SDK/Client.dfy \
	   src/SDK/CMM/DefaultCMM.dfy \
	   src/SDK/CMM/Defs.dfy \
	   src/SDK/Deserialize.dfy \
	   src/SDK/Keyring/RawAESKeyring.dfy \
	   src/SDK/Keyring/Defs.dfy \
	   src/SDK/Keyring/MultiKeyring.dfy \
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

BENCHSRCS = $(LIBSRCS) \
			src/Bench.dfy


build/java/src/bench/bench.java: $(BENCHSRCS)
	$(DAFNY) /out:build/java/src/bench $(BENCHSRCS) /compile:0 /noVerify /noIncludes /spillTargetCode:3 /compileTarget:java

build/java/bench.jar: $(BENCHSRCS) build/java/src/bench/bench.java
	mvn -f bench.pom.xml package
	cp build/java/aws-encryption-sdk-dafny-benchmarks-1.0-SNAPSHOT-jar-with-dependencies.jar build/java/bench.jar

