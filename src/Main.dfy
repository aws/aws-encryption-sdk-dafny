include "SDK/Keyring/RawRSAKeyring.dfy"
include "SDK/Materials.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "StandardLibrary/UInt.dfy"
include "SDK/CMM/Defs.dfy"
include "SDK/CMM/DefaultCMM.dfy"
include "SDK/Client.dfy"
include "SDK/MessageHeader.dfy"
include "Crypto/RSAEncryption.dfy"
include "Util/UTF8.dfy"
include "StandardLibrary/Base64.dfy"

module Main {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import DefaultCMMDef
  import RSAEncryption
  import RawRSAKeyringDef
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

    var encryptionContext := [];
    assert Msg.ValidAAD(encryptionContext) by {
      reveal Msg.ValidAAD();
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

    var ek, dk := RSAEncryption.RSA.RSAKeygen(2048, RSAEncryption.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace.value, name.value, RSAEncryption.RSAPaddingMode.PKCS1, 2048, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    EncryptDecryptTest(cmm);
  }
}
