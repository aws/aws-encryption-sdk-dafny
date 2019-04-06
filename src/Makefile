DAFNY = mono ../../dafny/Binaries/Dafny.exe

SOURCES = \
  StandardLibrary.dfy \
	AwsCrypto.dfy \
	ByteBuf.dfy \
	KeyringTrace.dfy \
	EDK.dfy \
	Cipher.dfy \
	Materials.dfy \
	DefaultCMM.dfy \
	Session.dfy

ADDITIONAL_SOURCES = \
	EncryptDecryptString.dfy

all: run

run: EncryptDecryptString.exe
	mono EncryptDecryptString.exe

EncryptDecryptString.exe: $(SOURCES)
	$(DAFNY) /out:"$@" $^

clean:
	rm -f EncryptDecryptString.exe EncryptDecryptString.exe.mdb
