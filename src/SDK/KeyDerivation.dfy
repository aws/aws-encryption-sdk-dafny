// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/HKDF/HMAC.dfy"

include "Serialize/HeaderTypes.dfy"
include "Serialize/SerializableTypes.dfy"

module {:extern "KeyDerivation"} KeyDerivation {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import MaterialProviders.Client
  import HeaderTypes
  import SerializableTypes
  import HKDF
  import HMAC

  // Convenience container to hold both a data key and an optional commitment key
  // to support algorithm suites that provide commitment and those that do not
  datatype ExpandedKeyMaterial = ExpandedKeyMaterial(
    nameonly dataKey: seq<uint8>,
    nameonly commitmentKey: Option<seq<uint8>>
  )

  /*
   * Derives a single data key from an input plaintext data key, using "v1"-style
   * key derivation (that is, no key commitment).
   */
  method DeriveKey(
    messageId: HeaderTypes.MessageId,
    plaintextDataKey: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  ) 
    returns (res: Result<ExpandedKeyMaterial, string>)

    // This should only be used for v1 algorithms
    requires suite.messageVersion == 1
    requires |plaintextDataKey| == suite.encrypt.keyLength as int

    ensures res.Success? ==> |res.value.dataKey| == suite.encrypt.keyLength as int
    ensures res.Success? ==> IsDerivedKey(res.value.dataKey)
    ensures res.Success? ==> res.value.commitmentKey.None?
  {
    if suite.kdf.IDENTITY? {
      assert IsDerivedKey(plaintextDataKey) by {
        reveal IsDerivedKey();
      }
      return Success(ExpandedKeyMaterial(dataKey:=plaintextDataKey, commitmentKey:=None()));
    }

    var algorithmSuiteID := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageId;
    var len := suite.kdf.inputKeyLength as int;
    var derivedKey := HKDF.Hkdf(suite.kdf.hmac, None, plaintextDataKey, infoSeq, len);
    assert IsDerivedKey(derivedKey) by {
      reveal IsDerivedKey();
    }
      return Success(ExpandedKeyMaterial(dataKey:=derivedKey, commitmentKey:=None()));
  }

  predicate {:opaque} IsDerivedKey(derivedDataKey: seq<uint8>)
  {
    true
  }

  /*
   * Derives keys from an input plaintext data key, using "v2"-style
   * key derivation (that is, including key commitment).
   */
  method ExpandKeyMaterial(
    messageId: HeaderTypes.MessageId,
    plaintextKey: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuiteInfo
  )
    returns (res: Result<ExpandedKeyMaterial, string>)

    // This should only be used for v2 algorithms
    requires suite.messageVersion == 2

    requires |messageId| != 0
    requires |plaintextKey| == suite.encrypt.keyLength as int
    // TODO: seems like the below pre-condition should follow from the above
    // pre-condition (|key| == keyLength), but apparently we don't prove/require
    // anywhere that keys be small.
    requires |plaintextKey| < INT32_MAX_LIMIT

    ensures
      && res.Success?
    ==>
      res.value.commitmentKey.Some?
  {
    var KEY_LABEL :- UTF8.Encode("DERIVEKEY");
    var COMMIT_LABEL :- UTF8.Encode("COMMITKEY");

    var digest := suite.commitment.hmac;
    var esdkId := UInt.UInt16ToSeq(SerializableTypes.GetESDKAlgorithmSuiteId(suite.id));
    var info := esdkId + KEY_LABEL;

    var hmac := new HMAC.HMac(digest);
    hmac.Init(messageId);

    var pseudoRandomKey := HKDF.Extract(hmac, messageId, plaintextKey, hmac.GetDigest());

    var Ke := Expand(digest, pseudoRandomKey, info, suite.encrypt.keyLength as int, messageId);
    var Kc := Expand(digest, pseudoRandomKey, COMMIT_LABEL, suite.encrypt.keyLength as int, messageId);

    return Success(ExpandedKeyMaterial(dataKey:=Ke, commitmentKey:=Some(Kc)));
  }

  /*
   * Primarily a wrapper around HKDF.Expand. Saves us a little bit of duplication since
   * we need to expand multiple keys.
   */
  method Expand(
    digest: HMAC.Digests,
    pseudoRandomKey: seq<uint8>,
    info: seq<uint8>,
    length: int,
    messageId: seq<uint8>
  ) returns (res: seq<uint8>)
  {
    var hmac := new HMAC.HMac(digest);
    hmac.Init(messageId);

    var key, _ := HKDF.Expand(hmac, pseudoRandomKey, info, length, digest, messageId);
    return key;
  }

  /*
   * Derives key material for encryption/decryption. Delegates out to specific methods
   * based on the input algorithm suite.
   */
  method DeriveKeys(
    messageId: HeaderTypes.MessageId,
    plaintextKey: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    returns (res: Result<ExpandedKeyMaterial, string>)

    requires |messageId| != 0
    requires |plaintextKey| == suite.encrypt.keyLength as int
    requires |plaintextKey| < INT32_MAX_LIMIT

    ensures
      && res.Success?
      && suite.messageVersion == 1
    ==>
      res.value.commitmentKey.None?

    ensures
      && res.Success?
      && suite.messageVersion == 2
    ==>
      res.value.commitmentKey.Some?
  {
    var keys : ExpandedKeyMaterial;
    if (suite.messageVersion == 2) {
      keys :- ExpandKeyMaterial(messageId, plaintextKey, suite);
    } else if (suite.messageVersion == 1) {
      keys :- DeriveKey(messageId, plaintextKey, suite);
    } else {
      return Failure("Unknown message version");
    }

    return Success(keys);
  }
}
