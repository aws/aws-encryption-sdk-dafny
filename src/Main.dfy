include "SDK/ToyClient.dfy"
include "SDK/Keyring/RawRSAKeyring.dfy"
include "SDK/Materials.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "StandardLibrary/UInt.dfy"
include "SDK/CMM/DefaultCMM.dfy"
include "SDK/Client.dfy"
include "SDK/MessageHeader.dfy"
include "Crypto/RSAEncryption.dfy"
include "Util/UTF8.dfy"

module Main {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import DefaultCMMDef
  import Client = ToyClientDef
  import RSAEncryption
  import RawRSAKeyringDef
  import Materials
  import ESDKClient
  import Msg = MessageHeader
  import UTF8

  method EncryptDecryptTest(client: Client.Client)
    requires client.Valid()
  {
    var msg := UTF8.Encode("hello");
    if msg.Failure? {
      print "Failure: hardcoded plaintext cannot be utf8 encoded\n";
      return;
    }
    print "Message: ", msg.value, "\n";
    var keyA := UTF8.Encode("keyA");
    var valA := UTF8.Encode("valA");
    if keyA.Failure? || valA.Failure? {
      print "Failure: hardcoded key/value cannot be utf8 encoded\n";
      return;
    }

    var e := client.Encrypt(msg.value, Materials.EncCtxOfStrings([(keyA.value, valA.value)]));
    if e.Failure? {
      print "Bad encryption :( ", e.error, "\n";
      return;
    }
    var d := client.Decrypt(e.value);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }
    print "Produced ", |e.value.edks|, " EDKs \n";
    print "Decrypted to: ", d.value, "\n";
    var aad := UTF8.Decode(Materials.FlattenSortEncCtx(e.value.ec));
    if aad.Failure? {
      print "Failure: encryption context cannot be utf8 decoded after serialization\n";
      return;
    }
    print "AAD: ", aad.value, "\n";
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
    var client := new Client.Client.OfCMM(cmm);
    EncryptDecryptTest(client);
  }
}
