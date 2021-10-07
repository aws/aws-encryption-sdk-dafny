// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../Crypto/Signature.dfy"
include "../EncryptionContext.dfy"

module {:extern "CMMDefs"} CMMDefs {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import Signature
  import EncryptionContext

  trait {:termination false} CMM {
    ghost var Repr: set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method GetEncryptionMaterials(materialsRequest: Materials.EncryptionMaterialsRequest)
                                  returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures res.Success? ==> EncryptionMaterialsSignature(res.value)
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.Serializable()
      ensures Valid() && fresh(Repr - old(Repr))

    // The following predicate is a synonym for Encryption.Serializable and provides a workaround for a translation bug
    // of "fuel" in trait-override checks in Dafny. https://github.com/dafny-lang/dafny/issues/422
    static predicate ValidAAD(encryptionContext: EncryptionContext.Map) {
      EncryptionContext.Serializable(encryptionContext)
    }

    method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                            returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
  }

  // Predicate works arround a known error in Dafny: https://github.com/dafny-lang/dafny/issues/422
  predicate EncryptionMaterialsSignature(validEncryptionMaterials: Materials.ValidEncryptionMaterials) {
    EncryptionMaterialsSignatureOpaque(validEncryptionMaterials)
  }

  predicate {:opaque } EncryptionMaterialsSignatureOpaque(validEncryptionMaterials: Materials.ValidEncryptionMaterials)
  {
    true
  }


}