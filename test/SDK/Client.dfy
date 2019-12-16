include "../../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/Crypto/RSAEncryption.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"

module {:extern "TestClient"} TestClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import DefaultCMMDef
  import RSAEncryption
  import RawRSAKeyring
  import Materials
  import Client = ESDKClient
  import Msg = MessageHeader
  import UTF8
  import Base64

  method EncryptDecryptTest(cmm: CMMDefs.CMM) returns (r: Result<()>)
    requires cmm.Valid()
  {
    var msg := UTF8.Encode("hello").value;

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
    var e :- Client.Encrypt(msg, cmm, encryptionContext);

    var d :- Client.Decrypt(e, cmm);

    r := RequireEqual(msg, d);
  }

  method {:test} HappyPath() returns (r: Result<()>) {
    var namespace :- UTF8.Encode("namespace");
    var name :- UTF8.Encode("MyKeyring");

    var ek, dk := RSAEncryption.GenerateKeyPair(2048, RSAEncryption.PKCS1);
    var keyring := new RawRSAKeyring.RawRSAKeyring(namespace, name, RSAEncryption.PaddingMode.PKCS1, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    r := EncryptDecryptTest(cmm);
  }
}
