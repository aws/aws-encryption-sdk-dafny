// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

module {:extern "KeyringDefs"} KeyringDefs {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened Seq
  import Materials
  import AlgorithmSuite

  trait {:termination false} Keyring {
    ghost var Repr: set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
  }

  predicate OnEncryptPure(
    materials: Materials.ValidEncryptionMaterials,
    res: Result<Materials.ValidEncryptionMaterials, string>
  )
  {
    res.Success? ==>
      && materials.encryptionContext == res.value.encryptionContext
      && materials.algorithmSuiteID == res.value.algorithmSuiteID
      && materials.encryptedDataKeys <= res.value.encryptedDataKeys
      && materials.signingKey == res.value.signingKey
      && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
  }

  predicate OnDecryptPure(
    materials: Materials.ValidDecryptionMaterials,
    // encryptedDataKeys: seq<Materials.EncryptedDataKey>,
    res: Result<Materials.ValidDecryptionMaterials, string>
  )
  {
    && (
        && res.Success?
        && materials.plaintextDataKey.Some?
      ==>
        && materials == res.value)
    && (
        && res.Success?
        && materials.plaintextDataKey.None?
      ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && materials.verificationKey == res.value.verificationKey
        && res.value.plaintextDataKey.Some?
      )

  }

  trait {:termination false} BetterKeyring {
    method OnEncrypt(
      materials: Materials.ValidEncryptionMaterials
    ) returns (res: Result<Materials.ValidEncryptionMaterials, string>)

    method OnDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKeys: seq<Materials.EncryptedDataKey>
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
  }

}
