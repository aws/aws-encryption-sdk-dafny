include "SDK/ToyClient.dfy"
//include "SDK/Keyring/AESKeyring.dfy"
include "SDK/Keyring/RSAKeyring.dfy"
//include "SDK/Keyring/MultiKeyring.dfy"
//include "SDK/Keyring/Defs.dfy"
include "SDK/Materials.dfy"
//include "Crypto/AESEncryption.dfy"
//include "Crypto/RSAEncryption.dfy"
//include "Crypto/Signature.dfy"
//include "Crypto/Cipher.dfy"
//include "StandardLibrary/StandardLibrary.dfy"
include "SDK/CMM/DefaultCMM.dfy"

module Main {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import DefaultCMMDef
  import Client = ToyClientDef
  import RSA = RSAEncryption
  import RSAKeyringDef
  import Materials
  //import AES = AESEncryption
  //import opened Cipher
  //import opened AESKeyringDef
  //import K = KeyringDefs
  //import opened MultiKeyringDef
  //import opened SDKDefs
  //import opened DefaultCMMDef
  //import S = Signature

  /*
  method RunToyClient() {
    var ek, dk := RSA.RSA.RSAKeygen(2048, RSA.PKCS1);
    var rsa_kr := new RSAKeyring(byteseq_of_string("namespace"), byteseq_of_string("name"), RSA.PKCS1, 2048, Some(ek), Some(dk));
    var k2 := AES.AES.AESKeygen(AES_GCM_256);
    var aes_kr := new AESKeyring(byteseq_of_string("namespace"), byteseq_of_string("name2"), k2, AES_GCM_256);
    var kr_children := new K.Keyring[1](_ => rsa_kr);
    var kr := new MultiKeyring(aes_kr, kr_children);
    var cmm := new DefaultCMM.OfKeyring(kr);
    var client := new ToyClient.OfCMM(cmm);

    var msg := byteseq_of_string("hello");
    print "Message: ", msg, "\n";
    var e := client.Enc(byteseq_of_string("hello"), enc_ctx_of_strings([("keyA", "valA")]));
    // datatype Encryption = Encryption(ec : EncCtx, edks : seq<EDK>, ciphertext : seq<uint8>)
    if e.Err? {
      print "Bad encryption :( ", e.err, "\n";
      return;
    }
    var d := client.Dec(e.get);
    if d.Err? {
      print "bad decryption: ", d.err, "\n";
      return;
    }
    print "Produced ", |e.get.edks|, " EDKs \n";
    print "Decrypted to: ", d.get, "\n";
    print "AAD: ", string_of_byteseq(FlattenSortEncCtx(e.get.ec)), "\n";
  }
  */

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
    var name := "MyKeyring";
    var ek, dk := RSA.RSA.RSAKeygen(2048, RSA.PKCS1);
    var keyring := new RSAKeyringDef.RSAKeyring(StringToByteSeq(namespace), StringToByteSeq(name), RSA.RSAPaddingMode.PKCS1, 2048, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    var client := new Client.Client.OfCMM(cmm);

    EncryptDecryptTest(client);
  }
}
