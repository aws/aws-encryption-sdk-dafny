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
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && res.value.verificationKey == materials.verificationKey
  }

  trait {:termination false} UnwrapSingleEncryptedDataKey {
    method Decrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKey: Materials.EncryptedDataKey
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)

    method FirstSuccessufulDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKeys: seq<Materials.EncryptedDataKey>,
      emptyError: string,
      initError: string
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>) {

      var errors := [];
      for i := 0 to |encryptedDataKeys| {
        var thisResult := this.Decrypt(materials, encryptedDataKeys[i]);
        if thisResult.Success? {
          return Success(thisResult.value);
        } else {
          errors := errors + [thisResult.error];
        }
      }

      if |errors| == 0 {
        return Failure(emptyError);
      } else {
        var concatString := (s, a) => a + "\n" + s;
        var error := FoldRight(
          concatString,
          errors,
          initError
        );
        return Failure(error);
      }
    }
  }
}
