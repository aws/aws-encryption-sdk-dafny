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
    requires suite.commitment.None?

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
    requires suite.commitment.HKDF?

    requires |messageId| != 0
    requires |plaintextKey| == suite.encrypt.keyLength as int
    // TODO: seems like the below pre-condition should follow from the above
    // pre-condition (|key| == keyLength), but apparently we don't prove/require
    // anywhere that keys be small.
    requires |plaintextKey| < INT32_MAX_LIMIT

    ensures res.Success? ==>
      && res.value.commitmentKey.Some?
      && |res.value.commitmentKey.value| == suite.commitment.outputKeyLength as int

    ensures res.Success? ==> |res.value.dataKey| == suite.encrypt.keyLength as int

  {
    var KEY_LABEL :- UTF8.Encode("DERIVEKEY");
    var COMMIT_LABEL :- UTF8.Encode("COMMITKEY");

    var digest := suite.commitment.hmac;
    var esdkId := UInt.UInt16ToSeq(SerializableTypes.GetESDKAlgorithmSuiteId(suite.id));
    var info := esdkId + KEY_LABEL;

    var hmac := new HMAC.HMac(digest);
    hmac.Init(messageId);

    var pseudoRandomKey := HKDF.Extract(hmac, messageId, plaintextKey, hmac.GetDigest());

    // TODO: Ideally we would just use the same hmac instance for all of these; however,
    // verification is currently failing if we attempt to re-use hmacs between `Expand`
    // calls. This likely requires some fixing of pre-/post-conditions on the HKDF methods
    var hmac_ke := new HMAC.HMac(digest);
    hmac_ke.Init(messageId);
    var Ke, _ := HKDF.Expand(hmac_ke, pseudoRandomKey, info, suite.encrypt.keyLength as int, digest, messageId);

    var hmac_kc := new HMAC.HMac(digest);
    hmac_kc.Init(messageId);
    var Kc, _ := HKDF.Expand(hmac_kc, pseudoRandomKey, COMMIT_LABEL, suite.commitment.outputKeyLength as int, digest, messageId);

    return Success(ExpandedKeyMaterial(dataKey:=Ke, commitmentKey:=Some(Kc)));
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

    ensures res.Success? ==>
      |res.value.dataKey| == suite.encrypt.keyLength as nat

    ensures
      && res.Success?
      && suite.commitment.None?
    ==>
      res.value.commitmentKey.None?

    ensures
      && res.Success?
      && suite.commitment.HKDF?
    ==>
      && res.value.commitmentKey.Some?
      && |res.value.commitmentKey.value| == suite.commitment.outputKeyLength as int
  {
    var keys : ExpandedKeyMaterial;
    if (suite.messageVersion == 2) {
      :- Need(suite.commitment.HKDF?, "Suites with message version 2 must have commitment");
      keys :- ExpandKeyMaterial(messageId, plaintextKey, suite);
    } else if (suite.messageVersion == 1) {
      :- Need(suite.commitment.None?, "Suites with message version 1 must not have commitment");
      keys :- DeriveKey(messageId, plaintextKey, suite);
    } else {
      return Failure("Unknown message version");
    }

    return Success(keys);
  }
}
