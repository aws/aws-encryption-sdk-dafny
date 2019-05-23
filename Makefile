ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif
SRCDIR   = src
BUILDDIR = build

# Copied from previous one
_SRC = \
  StandardLibrary.dfy \
	ByteOrder.dfy \
	AwsCrypto.dfy \
	ByteBuf.dfy \
	KeyringTrace.dfy \
	EDK.dfy \
	Cipher.dfy \
	Frame.dfy \
	Materials.dfy \
	DefaultCMM.dfy \
	Session.dfy
SRC  = $(patsubst %,$(SRCDIR)/%,$(_SRC))
SRCV = $(patsubst %, %.verified, $(SRC))

DEPS     = src/HKDF-extern.cs\
			lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

DLL      = HKDF.dll
_OBJ     = $(DLL) HKDF.cs HKDF.pdb
OBJ      = $(patsubst %,$(BUILDDIR)/%,$(_OBJ))

DPARAMS  = /out:$(BUILDDIR)/HKDF

SRCOBJ   = $(patsubst %,$(SRCDIR)/%,$(_OBJ))

.PHONY: clean deps all hkdf test help lit

all: hkdf

# Verify each file separately
$(SRCDIR)/%.dfy.verified: $(SRCDIR)/%.dfy
	$(DAFNY) $^ /compile:0 && touch $@

_HKDFSRC = HKDF.dfy StandardLibrary.dfy Arrays.dfy CryptoLibrary.dfy CryptoMac.dfy
HKDFSRC  = $(patsubst %,$(SRCDIR)/%,$(_HKDFSRC))
HKDFSRCV = $(patsubst %, %.verified, $(HKDFSRC))

# Compile output without verification, we already have verified each file
$(OBJ): $(HKDFSRCV) $(SRCDIR)/HKDF-extern.cs $(DEPS)
	$(DAFNY) $(DPARAMS) $(HKDFSRC) $(DEPS) /compile:2 /noVerify /noIncludes

hkdf: deps $(BUILDDIR)/$(DLL)

lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll:
	nuget install

lit:
	pip install lit

test: 
	lit test

deps: lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll lit

# Copied from previous one
run: EncryptDecryptString.exe
	mono EncryptDecryptString.exe

# Copied from previous one
EncryptDecryptString.exe: $(SOURCES)
	$(DAFNY) $(DPARAMS)/"$@" $^

clean:
	rm $(BUILDDIR)/*
	rm $(SRCV)
	rm -rf lib/*

help:
	@echo "Usage: make {all, hkdf, deps, lit, clean, help}"
