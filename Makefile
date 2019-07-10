ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif


SRCDIRS = src/Crypto \
		  src/Crypto/HKDF \
		  src/Util \
		  src/StandardLibrary \
		  src/Tests \
		  src/SDK \
		  src/SDK/MessageHeader \
		  src

SRCS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.dfy))
SRCV = $(patsubst src/%.dfy, build/%.dfy.verified, $(SRCS))

.PHONY: all hkdf clean

all: build/Main.exe
	
build/%.dfy.verified: src/%.dfy
	$(DAFNY) $(patsubst build/%.dfy.verified, src/%.dfy, $@) /compile:0 && mkdir -p $(dir $@) && touch $@

BCDLL = lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

DEPS = $(foreach dir, $(SRCDIRS), $(wildcard $(dir)/*.cs)) \
	$(BCDLL)

build/Main.exe: $(SRCV) $(DEPS) 
	$(DAFNY) /out:build/Main $(SRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/

OTHERSRCS = $(filter-out src/Crypto/HKDF/HKDF.dfy,$(SRCS))
build/HKDF.dll: $(SRCV) $(DEPS) 
	$(DAFNY) /out:build/HKDF src/Crypto/HKDF/HKDF.dfy $(OTHERSRCS) $(DEPS) /compile:2 /noVerify /noIncludes && cp $(BCDLL) build/

hkdf: build/HKDF.dll

lib/%.dll:
	nuget install

clean: 
	rm -r build/*
	rm -r lib/*