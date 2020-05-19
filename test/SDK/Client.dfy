// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/EncryptionContext.dfy"
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
    import EncryptionContext
    import UTF8
    import Client = ESDKClient
    import TestUtils

    method EncryptDecryptTest(cmm: CMMDefs.CMM)
      requires cmm.Valid()
      modifies cmm.Repr
      ensures cmm.Valid() && fresh(cmm.Repr - old(cmm.Repr))
    {
      var msg :- expect UTF8.Encode("hello");
      var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

      var encryptRequest := Client.EncryptRequest.WithCMM(msg, cmm).SetEncryptionContext(encryptionContext);
      var e :- expect Client.Encrypt(encryptRequest);

      var decryptRequest := Client.DecryptRequest.WithCMM(e, cmm);
      var d :- expect Client.Decrypt(decryptRequest);

      expect msg == d;
    }
  }

  method {:test} HappyPath() {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var ek, dk := RSA.GenerateKeyPair(2048, RSA.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace, name, RSA.PaddingMode.PKCS1, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    Helpers.EncryptDecryptTest(cmm);
  }

  method {:test} EncryptCMMKeyringOverload() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(kr);
    var badRequest := Client.EncryptRequest.WithCMM([0], cmm).(keyring := kr);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both).";
  }

  method {:test} EncryptInvalidAlgID() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var badRequest := Client.EncryptRequest.WithKeyring([0], kr).SetAlgorithmSuiteID(0);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "Invalid algorithmSuiteID.";
  }

  method {:test} EncryptFrameLengthZero() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var badRequest := Client.EncryptRequest.WithKeyring([0], kr).SetFrameLength(0);

    var result := Client.Encrypt(badRequest);

    expect result.Failure?;
    expect result.error == "Request frameLength must be > 0";
  }

  method {:test} DecryptCMMKeyringOverload() {
    var kr :- expect TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(kr);
    var badRequest := Client.DecryptRequest.WithCMM([0], cmm).(keyring := kr);

    var result := Client.Decrypt(badRequest);

    expect result.Failure?;
    expect result.error == "DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).";
  }
}
