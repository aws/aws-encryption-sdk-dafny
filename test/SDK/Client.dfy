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
include "../Util/TestUtils.dfy"

module {:extern "TestClient"} TestClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import DefaultCMMDef
  import RSA = RSAEncryption
  import RawRSAKeyringDef
  import Materials
  import Client = ESDKClient
  import Base64
  import UTF8

  import TestUtils
    
  module Helpers {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import CMMDefs
    import DefaultCMMDef
    import Msg = MessageHeader
    import UTF8
    import Client = ESDKClient
  
    method EncryptDecryptTest(cmm: CMMDefs.CMM)
      requires cmm.Valid()
      modifies cmm.Repr
      ensures cmm.Valid() && fresh(cmm.Repr - old(cmm.Repr))
    {
      var msg :- expect UTF8.Encode("hello");
      var keyA :- expect UTF8.Encode("keyA");
      var valA :- expect UTF8.Encode("valA");
      var encryptionContext := map[keyA := valA];
      assert Msg.ValidAAD(encryptionContext) by {
        // To prove ValidAAD, we need to reveal the definition of ValidAAD:
        reveal Msg.ValidAAD();
        // We also need to help the verifier with proving the KVPairsLength is small:
        calc {
          Msg.KVPairsLength(encryptionContext);
          var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
          var kvPairsSeq := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
          2 + Msg.KVPairEntriesLength(kvPairsSeq, 0, |kvPairsSeq|); // 2 bytes for the kvPairsCount field
          2 + 2 + |keyA| + 2 + |valA|; // 2 bytes required for keyLength and valueLength fields
        }
        assert Msg.KVPairsLength(encryptionContext) < UINT16_LIMIT;
      }

      var encryptRequest := new Client.EncryptRequest.WithCMM(msg, cmm);
      encryptRequest.SetEncryptionContext(encryptionContext);
      var e :- expect Client.Encrypt(encryptRequest);

      var decryptRequest := new Client.DecryptRequest.WithCMM(e, cmm);
      var d :- expect Client.Decrypt(decryptRequest);

      expect msg == d;
    }
  }

  method {:test} HappyPath() {
    var namespace :- expect UTF8.Encode("namespace");
    var name :- expect UTF8.Encode("MyKeyring");

    var ek, dk := RSA.GenerateKeyPair(2048, RSA.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace, name, RSA.PaddingMode.PKCS1, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    Helpers.EncryptDecryptTest(cmm);
  }

  method {:test} EncryptCMMKeyringOverload() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(kr);
    var badRequest := new Client.EncryptRequest.WithCMM([0], cmm);
    badRequest.keyring := kr;

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both).";
  }

  method {:test} EncryptInvalidAlgID() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var badRequest := new Client.EncryptRequest.WithKeyring([0], kr);
    badRequest.SetAlgorithmSuiteID(0);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "Invalid algorithmSuiteID.";
  }

  method {:test} EncryptFrameLengthZero() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var badRequest := new Client.EncryptRequest.WithKeyring([0], kr);
    badRequest.SetFrameLength(0);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "Request frameLength must be > 0";
  }

  method {:test} EncryptInvalidEncryptionContextKeys() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var badRequest := new Client.EncryptRequest.WithKeyring([0], kr);
    badRequest.SetEncryptionContext(map[Materials.EC_PUBLIC_KEY_FIELD := [0]]);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "Invalid encryption context keys.";
  }

  // TODO: Test invalid EncCtx

  method {:test} DecryptCMMKeyringOverload() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(kr);
    var badRequest := new Client.DecryptRequest.WithCMM([0], cmm);
    badRequest.keyring := kr;

    var result := Client.Decrypt(badRequest);

    expect result.Failure?;
    expect result.error == "DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).";
  }
}
