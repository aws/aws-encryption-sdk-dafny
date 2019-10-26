include "SDK/ToyClient.dfy"
include "SDK/Keyring/RawRSAKeyring.dfy"
include "SDK/Materials.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "StandardLibrary/UInt.dfy"
include "SDK/CMM/DefaultCMM.dfy"
include "SDK/Client.dfy"
include "SDK/MessageHeader.dfy"
include "Crypto/RSAEncryption.dfy"

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

  method EncryptDecryptTest(client: Client.Client)
    requires client.Valid()
  {
    var msg := StringToByteSeq("hello");
    print "Message: ", msg, "\n";
    var e := client.Encrypt(msg, Materials.enc_ctx_of_strings([("keyA", "valA")]));
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
    print "AAD: ", ByteSeqToString(Materials.FlattenSortEncCtx(e.value.ec)), "\n";
  }

  method Main() {
    var namespace := "namespace";
    var name := StringToByteSeq("MyKeyring");
    var ek, dk := RSAEncryption.RSA.RSAKeygen(2048, RSAEncryption.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace, name, RSAEncryption.RSAPaddingMode.PKCS1, 2048, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    assert Msg.ValidAAD([]) by {
      reveal Msg.ValidAAD();
    }
    var result := ESDKClient.Encrypt(StringToByteSeq("the message I want to encrypt"), cmm, []);
    match result {
      case Failure(err) =>
        print "Encryption Error: ", err, "\n";
      case Success(bytes) =>
        print "Encryption Success:\n";
        print bytes, "\n";
    }
  }
}
