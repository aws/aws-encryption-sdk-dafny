include "SDK/Keyring/KMSKeyring.dfy"
include "SDK/Materials.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "StandardLibrary/UInt.dfy"
include "SDK/CMM/Defs.dfy"
include "SDK/CMM/DefaultCMM.dfy"
include "SDK/Client.dfy"
include "SDK/MessageHeader.dfy"
include "KMS/KMSUtils.dfy"
include "Util/UTF8.dfy"
include "StandardLibrary/Base64.dfy"

module Main {
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

  method EncryptDecryptTest(cmm: CMMDefs.CMM)
    requires cmm.Valid()
  {
    var msg := UTF8.Encode("hello").value;
    print "Original plaintext: ", msg, "\n";

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
    var e := Client.Encrypt(msg, cmm, encryptionContext);
    if e.Failure? {
      print "Bad encryption :( ", e.error, "\n";
      return;
    }
    print "Encrypted message: ", Base64.Encode(e.value), "\n";

    var d := Client.Decrypt(e.value, cmm);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }
    print "Plaintext from the deserialized and decrypted message: ", d.value, "\n";
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

    EncryptDecryptTest(cmm);
  }
}
