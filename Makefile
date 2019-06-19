ifeq ($(OS),Windows_NT)
  DAFNY = Dafny.exe
else
  DAFNY = dafny
endif

SRCDIR   = src
BUILDDIR = build
LIBDIR   = lib

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
	Session.dfy \
	HKDF.dfy \
	Arrays.dfy \
	HKDFSpec.dfy \
	CryptoMac.dfy
SRC  = $(patsubst %,$(SRCDIR)/%,$(_SRC))
SRCV = $(patsubst %, %.verified, $(SRC))

DEPS = $(LIBDIR)/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

_HKDFOBJ = HKDF.dll HKDF.cs HKDF.pdb
HKDFOBJ  = $(patsubst %,$(BUILDDIR)/%,$(_HKDFOBJ))

.PHONY: clean deps all hkdf test help lit

all: hkdf

# Verify each file separately
$(SRCDIR)/%.dfy.verified: $(SRCDIR)/%.dfy
	$(DAFNY) $^ /compile:0 && touch $@

_HKDFSRC = HKDF.dfy StandardLibrary.dfy Arrays.dfy HKDFSpec.dfy CryptoMac.dfy
HKDFSRC  = $(patsubst %,$(SRCDIR)/%,$(_HKDFSRC))
HKDFSRCV = $(patsubst %, %.verified, $(HKDFSRC))

# Compile output without verification, we already have verified each file
$(HKDFOBJ): $(HKDFSRCV) $(SRCDIR)/HKDF-extern.cs $(DEPS)
	$(DAFNY) /out:$(BUILDDIR)/HKDF $(HKDFSRC) $(SRCDIR)/HKDF-extern.cs $(DEPS) /compile:2 /noVerify /noIncludes

hkdf: deps $(BUILDDIR)/HKDF.dll

$(LIBDIR)/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll:
	nuget install

lit:
	pip install lit

test: 
	lit test

deps: $(LIBDIR)/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll

clean:
	rm -f $(BUILDDIR)/*
	rm -rf $(LIBDIR)/*
	rm -f $(SRCV)

help:
	@echo "Usage: make {all, hkdf, deps, lit, clean, help}"
