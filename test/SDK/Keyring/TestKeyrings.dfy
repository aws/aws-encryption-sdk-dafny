// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


include "../../../src/SDK/Materials.dfy"
include "../../../src/SDK/Keyring/Defs.dfy"

module TestKeyrings {
  import opened StandardLibrary
  import opened KeyringDefs
  import Materials

  class NoOpKeyring extends Keyring {

    constructor() {}

    predicate Valid() reads this, Repr { true }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
    {
      return Success(materials);
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && res.value.verificationKey == materials.verificationKey
    {
      return Success(materials);
    }
  }

  class AlwaysFailingKeyring extends Keyring {

    constructor() {}

    predicate Valid() reads this, Repr { true }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
    {
      return Failure("Surprise, AlwaysFailingKeyring always fails!");
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && res.value.verificationKey == materials.verificationKey
    {
      if |encryptedDataKeys| == 0 || materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      return Failure("Surprise, AlwaysFailingKeyring always fails!");
    }
  }

}
