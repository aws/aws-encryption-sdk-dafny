// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"
include "../Util/UTF8.dfy"
include "EncryptionContext.dfy"

module {:extern "Materials"} Materials {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import AlgorithmSuite
  import EncryptionContext

  // UTF-8 encoded "aws-crypto-public-key"
  const EC_PUBLIC_KEY_FIELD: UTF8.ValidUTF8Bytes :=
    var s :=
      [0x61, 0x77, 0x73, 0x2D, 0x63, 0x72, 0x79, 0x70, 0x74, 0x6F, 0x2D, 0x70,
      0x75, 0x62, 0x6C, 0x69, 0x63, 0x2D, 0x6B, 0x65, 0x79];
    assert UTF8.ValidUTF8Range(s, 0, 21);
    s
  const RESERVED_KEY_VALUES := { EC_PUBLIC_KEY_FIELD }

  // TODO If one removes anything below this comment (since it is either unused or defined in the Polymorph generated files)
  // Deserialize's verification hangs. Need to stabilize Deserialize's verification.

  datatype EncryptedDataKey = EncryptedDataKey(providerID: UTF8.ValidUTF8Bytes,
                                               providerInfo: seq<uint8>,
                                               ciphertext: seq<uint8>)
  {
    predicate Valid() {
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }

    static function method ValidWitness(): EncryptedDataKey {
      EncryptedDataKey([], [], [])
    }
  }

  type ValidEncryptedDataKey = i : EncryptedDataKey | i.Valid() witness EncryptedDataKey.ValidWitness()

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext.Map,
                                                     algorithmSuiteID: AlgorithmSuite.ID,
                                                     plaintextDataKey: Option<seq<uint8>>,
                                                     encryptedDataKeys: seq<ValidEncryptedDataKey>,
                                                     signingKey: Option<seq<uint8>>)
  {
    predicate Valid() {
      && (algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?)
      && (plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value))
      && (plaintextDataKey.None? ==> |encryptedDataKeys| == 0)
    }

    predicate Serializable() {
      && |encryptedDataKeys| > 0
      && EncryptionContext.Serializable(encryptionContext)
    }

    static function method ValidWitness(): EncryptionMaterials {
      EncryptionMaterials(map[], AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, None, [], Some(seq(32, i => 0)))
    }

    static function method WithoutDataKeys(encryptionContext: EncryptionContext.Map,
                                           algorithmSuiteID: AlgorithmSuite.ID,
                                           signingKey: Option<seq<uint8>>): ValidEncryptionMaterials
      requires algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?
    {
      var m := EncryptionMaterials(encryptionContext, algorithmSuiteID, None, [], signingKey);
      assert m.Valid();
      m
    }

    function method WithKeys(newPlaintextDataKey: Option<seq<uint8>>,
                             newEncryptedDataKeys: seq<ValidEncryptedDataKey>): (res: ValidEncryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.Some? ==> newPlaintextDataKey == this.plaintextDataKey
      requires newPlaintextDataKey.Some? ==> this.algorithmSuiteID.ValidPlaintextDataKey(newPlaintextDataKey.value)
      requires newPlaintextDataKey.None? ==> |newEncryptedDataKeys| == 0
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID
      ensures newPlaintextDataKey == res.plaintextDataKey
      ensures this.encryptedDataKeys + newEncryptedDataKeys == res.encryptedDataKeys
      ensures this.signingKey == res.signingKey
    {
        var r := this.(plaintextDataKey := newPlaintextDataKey,
                       encryptedDataKeys := encryptedDataKeys + newEncryptedDataKeys);
        assert r.Valid();
        r
    }
  }

  type ValidEncryptionMaterials = i: EncryptionMaterials | i.Valid() witness EncryptionMaterials.ValidWitness()

  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                                     encryptionContext: EncryptionContext.Map,
                                                     plaintextDataKey: Option<seq<uint8>>,
                                                     verificationKey: Option<seq<uint8>>)
  {
    predicate Valid() {
      && (plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value))
      && (algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?)
    }

    static function method ValidWitness(): DecryptionMaterials {
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                          map[], Some(seq(32, i => 0)), Some(seq(32, i => 0)))
    }

    static function method WithoutPlaintextDataKey(encryptionContext: EncryptionContext.Map,
                                                   algorithmSuiteID: AlgorithmSuite.ID,
                                                   verificationKey: Option<seq<uint8>>): ValidDecryptionMaterials
      requires algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?
    {
      var m := DecryptionMaterials(algorithmSuiteID, encryptionContext, None, verificationKey);
      assert m.Valid();
      m
    }

    function method WithPlaintextDataKey(plaintextDataKey: seq<uint8>): (res: ValidDecryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.None?
      requires algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID
      ensures res.plaintextDataKey.Some?
      ensures this.verificationKey == res.verificationKey
    {
      var m := this.(plaintextDataKey := Some(plaintextDataKey));
      assert m.Valid();
      m
    }
  }

  type ValidDecryptionMaterials = i: DecryptionMaterials | i.Valid() witness DecryptionMaterials.ValidWitness()

  datatype EncryptionMaterialsRequest = EncryptionMaterialsRequest(encryptionContext: EncryptionContext.Map,
                                                                   algorithmSuiteID: Option<AlgorithmSuite.ID>,
                                                                   plaintextLength: Option<nat>)

  datatype DecryptionMaterialsRequest = DecryptionMaterialsRequest(algorithmSuiteID: AlgorithmSuite.ID,
                                                                   encryptedDataKeys: seq<ValidEncryptedDataKey>,
                                                                   encryptionContext: EncryptionContext.Map)
  {
    predicate Valid() {
      |encryptedDataKeys| > 0
    }

    static function method ValidWitness(): DecryptionMaterialsRequest {
      DecryptionMaterialsRequest(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                                 [EncryptedDataKey.ValidWitness()],
                                 map[])
    }
  }

  type ValidDecryptionMaterialsRequest = i: DecryptionMaterialsRequest | i.Valid() witness DecryptionMaterialsRequest.ValidWitness()
}
