// RUN: %dafny /out:Output/Integration.exe "./Integration.dfy" ../../src/extern/dotnet/KMS.cs ../../src/extern/dotnet/UTF8.cs ../../src/extern/dotnet/Arrays-extern.cs ../../src/extern/dotnet/HKDF-extern.cs ../../src/extern/dotnet/AESEncryption.cs ../../src/extern/dotnet/Random.cs ../../src/extern/dotnet/Signature.cs "%kmslib" "%awslib" "%bclib" /compile:2
// RUN: cp %awslib %kmslib %bclib Output/
// RUN: %mono ./Output/Integration.exe > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"

module IntegTestKMS {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import DefaultCMMDef
  import KMSUtils
  import KMSKeyring
  import Materials
  import Client = ESDKClient
  import Msg = MessageHeader
  import UTF8
  import Base64

  method EncryptDecryptTest(cmm: CMMDefs.CMM, message: string) returns (res: Result<string>)
    requires cmm.Valid()
  {
    var encodedMsg: seq<uint8>;
    var encodeResult := UTF8.Encode(message);
    if encodeResult.Success? {
      encodedMsg := encodeResult.value;
    }
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    assert Msg.ValidAAD(encryptionContext) by {
      // To proving ValidAAD, we need to reveal the definition of ValidAAD:
      reveal Msg.ValidAAD();
      // We also need to help the verifier with proving the AADLength is small:
      calc {
        Msg.AADLength(encryptionContext);
        2 + Msg.KVPairsLength(encryptionContext, 0, 1);
        2 + 2 + |keyA| + 2 + |valA|;
      }
      assert Msg.AADLength(encryptionContext) < UINT16_LIMIT;
    }
    var e := Client.Encrypt(encodedMsg, cmm, encryptionContext);
    if e.Failure? {
      return Failure("Bad encryption :( " + e.error + "\n");
    }

    var d := Client.Decrypt(e.value, cmm);
    if d.Failure? {
      return Failure("bad decryption: " + d.error + "\n");
    }
    if UTF8.ValidUTF8Seq(d.value) {
      return UTF8.Decode(d.value);
    } else {
      return Failure("Could not decode Encryption output");
    }
  }

  method Main() {
    var namespace := UTF8.Encode("namespace");
    var name := UTF8.Encode("MyKeyring");
    if name.Failure? || namespace.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    }

    var generator := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
    var clientSupplier := new KMSUtils.DefaultClientSupplier();
    var keyring := new KMSKeyring.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var message := "Hello, World!";

    var result := EncryptDecryptTest(cmm, message);

    if result.Success? && result.value == message {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }
}
