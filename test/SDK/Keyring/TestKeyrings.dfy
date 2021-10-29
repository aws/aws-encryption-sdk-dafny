// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


include "../../../src/SDK/Materials.dfy"
include "../../../src/SDK/Keyring/Defs.dfy"

module TestKeyrings {
  import opened Wrappers
  import opened KeyringDefs
  import Materials

  class NoOpKeyring extends Keyring {

    constructor() {
      Repr := {};
    }

    predicate Valid() reads this, Repr { true }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
    {
      return Success(materials);
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
    {
      if materials.plaintextDataKey.None? {
        return Failure("No data key");
      }
      return Success(materials);
    }
  }

  class AlwaysFailingKeyring extends Keyring {

    constructor() {
      Repr := {};
    }

    predicate Valid() reads this, Repr { true }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
    {
      return Failure("Surprise, AlwaysFailingKeyring always fails!");
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
    {
      if materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      return Failure("Surprise, AlwaysFailingKeyring always fails!");
    }
  }

}
