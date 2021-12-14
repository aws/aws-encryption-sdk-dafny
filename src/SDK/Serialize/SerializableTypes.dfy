// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Util/UTF8.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/Sets.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

module SerializableTypes {
  import StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened UTF8
  import opened Aws.Crypto
  import Sets
  import Seq

  type ShortUTF8Seq = s: ValidUTF8Bytes | HasUint16Len(s)
  // To make verification and working with iterating through the encryption context
  // simpler, here we define a specific type to represent a sequence of key-value tuples.
  datatype Pair<K, V> = Pair(key: K, value: V)
  type Linear<K, V> = seq<Pair<K,V>>

  predicate method IsESDKEncryptedDataKey(edk: EncryptedDataKey) {
    && HasUint16Len(edk.keyProviderId)
    && ValidUTF8Seq(edk.keyProviderId)
    && HasUint16Len(edk.keyProviderInfo)
    && HasUint16Len(edk.ciphertext)
  }

  type ESDKEncryptedDataKey = e: EncryptedDataKey | IsESDKEncryptedDataKey(e) witness *
  type ESDKEncryptedDataKeys = seq16<ESDKEncryptedDataKey>

  predicate method IsESDKEncryptionContext(ec: Crypto.EncryptionContext) {
    && |ec| < UINT16_LIMIT
    && Length(ec) < UINT16_LIMIT
    && forall element
    | element in (multiset(ec.Keys) + multiset(ec.Values))
    ::
      && HasUint16Len(element)
      && ValidUTF8Seq(element)
  }

  type ESDKEncryptionContext = ec: Crypto.EncryptionContext
  | IsESDKEncryptionContext(ec)
  witness *

  const VALID_IDS: set<uint16> := {0x0578, 0x0478, 0x0378, 0x0346, 0x0214, 0x0178, 0x0146, 0x0114, 0x0078, 0x0046, 0x0014};
  
  type ESDKAlgorithmSuiteId = id: uint16 | id in VALID_IDS witness *

  const SupportedAlgorithmSuites: map<Crypto.AlgorithmSuiteId, ESDKAlgorithmSuiteId> := map[
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF := 0x0014,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF := 0x0046,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF := 0x0078,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 := 0x0114,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 := 0x0146,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 := 0x0178,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := 0x0214,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := 0x0346,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := 0x0378,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY := 0x0478,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 := 0x0578
  ]

  function method GetESDKAlgorithmSuiteId(
    suiteId: Crypto.AlgorithmSuiteId
  ):
    (res: ESDKAlgorithmSuiteId)
    ensures GetAlgorithmSuiteId(res) == suiteId
  {
    LemmaSupportedAlgorithmSuitesIsComplete(suiteId);
    SupportedAlgorithmSuites[suiteId]
  }

  function method GetAlgorithmSuiteId(
    esdkId: ESDKAlgorithmSuiteId
  ):
    (res: Crypto.AlgorithmSuiteId)
  {
    var suiteId
    :|
      && suiteId in SupportedAlgorithmSuites
      && SupportedAlgorithmSuites[suiteId] == esdkId;
    suiteId
  }

  lemma LemmaSupportedAlgorithmSuitesIsComplete(id:Crypto.AlgorithmSuiteId)
    ensures id in SupportedAlgorithmSuites
  {}

  /*
   * Length properties of the Encryption Context.
   * The Encryption Context has a complex relationship with length.
   * Each key or value MUST be less than Uint16,
   * However the entire thing MUST all so serialize to less than Uint16.
   * In practice, this means than the longest value,
   * given a key of 1 bytes is Uint16-2-2-1.
   * e.g.
   * 2 for the key length
   * 1 for the key data
   * 2 for the value length
   * Uint16-2-2-1 for the value data
   */
  function method Length(encryptionContext: Crypto.EncryptionContext): nat
  {
    if |encryptionContext| == 0 then 0 else
      // Defining and reasoning about order at this level is simplified by using a sequence of
      // key value pairs instead of a map.
      var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence2<uint8>(encryptionContext.Keys, UInt.UInt8Less);
      var pairs := seq(|keys|, i requires 0 <= i < |keys| => Pair(keys[i], encryptionContext[keys[i]]));
      2 + LinearLength(pairs)
  }

  function method {:tailrecursion} LinearLength(
    pairs: Linear<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  ):
    (ret: nat)
    ensures |pairs| == 0 ==> ret == 0
  {
    if |pairs| == 0 then 0
    else
      LinearLength(Seq.DropLast(pairs)) + PairLength(Seq.Last(pairs))
  }

  function method PairLength(
    pair: Pair<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
  ):
    (ret: nat)
  {
    2 + |pair.key| + 2 + |pair.value|
  }
}
