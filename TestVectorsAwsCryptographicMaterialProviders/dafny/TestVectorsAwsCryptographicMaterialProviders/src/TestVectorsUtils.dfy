// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"

module TestVectorsUtils {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  // This is cheating,
  // I know that this MUST be here
  // because this is required for MPL
  import Aws.Cryptography.Primitives
  import Crypto = AwsCryptographyPrimitivesTypes


  import AlgorithmSuites


  const SHARED_TEST_KEY_ARN := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

  const ACCOUNT_IDS := ["658956600833"];

  const PARTITION := "aws";
  
  // TODO correctly verify UTF8 validity of long sequences
  // This axiom should only be used by tests to skip UTF8 verification of long sequences
  // long to be serialized in 16 bytes, in order to avoid a false negative for from verification.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1000
    ensures UTF8.ValidUTF8Seq(s)

  method GenerateInvalidEncryptionContext() returns (encCtx: Types.EncryptionContext)
  {
    var validUTF8char: UTF8.ValidUTF8Bytes :- expect UTF8.Encode("a");
    var key: UTF8.ValidUTF8Bytes := [];
    while |key| < UINT16_LIMIT {
      UTF8.ValidUTF8Concat(key, validUTF8char);
      key := key + validUTF8char;
    }
    encCtx := map[key := [0]];
  }

  // Generates a large encryption context that approaches the upper bounds of
  // what is able to be serialized in the message format.
  // Building a map item by item is slow in dafny, so this method should be used sparingly.
  method GenerateLargeValidEncryptionContext() returns (r: Types.EncryptionContext)
  {
    // KVPairsMaxSize - KVPairsLenLen / KVPairLen ==>
    // (2^16 - 1 - 2) / (2 + 2 + 2 + 1) ==> (2^16 - 3) / 7 ==> 9361
    // which is close to the max number of pairs you can stuff into a valid AAD.
    // We look for 9361 valid 2 byte UTF8 sequences (sticking to 2 bytes for simplicity).
    assert (0x1_0000 - 1 - 2) / (2 + 2 + 2 + 1) == (0x1_0000 - 3) / 7 == 9361;
    var numMaxPairs := 9361;
    var val :- expect UTF8.Encode("a");
    var encCtx: map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes> := map[];

    // Instead of proving termination for looking for Valid UTF8 sequences,
    // provide an upper bound to while loop
    var i := 0;
    while |encCtx| < numMaxPairs && i < 0x1_0000
      invariant forall k :: k in encCtx ==> |k| + |encCtx[k]| == 3
      decreases 0x1_0000 - i
    {
      var key := UInt16ToSeq(i as uint16);
      if UTF8.ValidUTF8Seq(key) {
        encCtx := encCtx[key := val];
      }
      i := i + 1;
    }
    // // Check that we actually built a encCtx of the correct size
    // expect SerializableTypes.IsESDKEncryptionContext(encCtx);

    return encCtx;
  }

  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

  method SmallEncryptionContext(v: SmallEncryptionContextVariation)
    returns (encryptionContext: Types.EncryptionContext)
  {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    match v {
      case Empty =>
        encryptionContext := map[];
      case A =>
        encryptionContext := map[keyA := valA];
      case AB =>
        encryptionContext := map[keyA := valA, keyB := valB];
      case BA =>
        // this is really the same as AB; this lets us test that this is also true at run time
        encryptionContext := map[keyB := valB, keyA := valA];
    }
    // ValidSmallEncryptionContext(encryptionContext);
  }

  method GenerateMockEncryptedDataKey(
    keyProviderId: string,
    keyProviderInfo: string
  ) returns (edk: Types.EncryptedDataKey)
  {
    var encodedkeyProviderId :- expect UTF8.Encode(keyProviderId);
    var encodedKeyProviderInfo :- expect UTF8.Encode(keyProviderInfo);
    var fakeCiphertext :- expect UTF8.Encode("fakeCiphertext");
    return Types.EncryptedDataKey(
      keyProviderId := encodedkeyProviderId,
      keyProviderInfo := encodedKeyProviderInfo,
      ciphertext := fakeCiphertext
    );
  }
    
  method NamespaceAndName(n: nat) returns (namespace: string, name: string)
    requires 0 <= n < 10
    ensures |namespace| < UINT16_LIMIT
    ensures |name| < UINT16_LIMIT
  {
    var s := "child" + [n as char + '0'];
    namespace := s + " Namespace";
    name := s + " Name";
  }


  method GetEncryptionMaterials(
    mpl: Types.IAwsCryptographicMaterialProvidersClient,
    algorithmSuiteId: Types.AlgorithmSuiteId,
    encryptionContext: Types.EncryptionContext
  )
    returns (encryptionMaterials: Types.EncryptionMaterials)
  {

    // This is copied from the Default CMM
    var crypto :- expect Primitives.AtomicPrimitives();
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var signingKey: Option<seq<uint8>>;
    var verificationKey: Option<seq<uint8>>;
    if suite.signature.ECDSA? {
      var pair :- expect crypto.GenerateECDSASignatureKey(
        Crypto.GenerateECDSASignatureKeyInput(
          signatureAlgorithm := suite.signature.ECDSA.curve
        )
      );
      signingKey := Some(pair.signingKey);
      verificationKey := Some(pair.verificationKey);
    } else {
      assert  suite.signature.None?;
      signingKey := None;
      verificationKey := None;
    }

    encryptionMaterials :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := [],
        signingKey := signingKey,
        verificationKey := verificationKey
      )
    );
  }

}
