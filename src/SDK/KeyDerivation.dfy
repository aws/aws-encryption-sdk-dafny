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

  // Convenience container to hold both K_e and K_c necessary
  // for encryption with key commitment
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

    // This should only be used for algorithms with commitment
    requires suite.messageVersion == 2

    requires |messageId| != 0
    requires |plaintextKey| == suite.encrypt.keyLength as int
    // TODO: seems like this should follow from the fact that |key| == keyLength,
    // but apparently we don't prove/require any where that keys be small.
    requires |plaintextKey| < INT32_MAX_LIMIT

    // Make sure we return a commitment key
    ensures
      && res.Success?
    ==>
      res.value.commitmentKey.Some?
  {
    var KEY_LABEL :- UTF8.Encode("DERIVEKEY");
    var COMMIT_LABEL :- UTF8.Encode("COMMITKEY");

    //var digest := suite.commitment.hmac;
    var digest := HMAC.Digests.SHA_512; // TODO: why?
    var esdkId := UInt.UInt16ToSeq(SerializableTypes.GetESDKAlgorithmSuiteId(suite.id));
    var info := esdkId + KEY_LABEL;

    var hmac1 := new HMAC.HMac(digest);
    hmac1.Init(messageId);

    var PRK := HKDF.Extract(hmac1, messageId, plaintextKey, hmac1.GetDigest());

    var Ke, _ := HKDF.Expand(hmac1, PRK, info, suite.encrypt.keyLength as int, digest, messageId);

    var hmac2 := new HMAC.HMac(digest);
    hmac2.Init(messageId);

    var Kc, _ := HKDF.Expand(hmac2, PRK, COMMIT_LABEL, suite.encrypt.keyLength as int, digest, messageId);

    return Success(ExpandedKeyMaterial(dataKey:=Ke, commitmentKey:=Some(Kc)));
  }

  predicate {:opaque} IsDerivedKey(derivedDataKey: seq<uint8>)
  {
    true
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
