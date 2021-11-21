// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "Materials.dfy"

module 
  {:extern "Dafny.Aws.Crypto.MaterialProviders.Keyring"}
  MaterialProviders.Keyring
{
  import opened Wrappers
  import Aws.Crypto
  import Materials

  export
    provides
      VerifiableInterface

  trait {:termination false} VerifiableInterface
    extends Crypto.IKeyring
  {
    method OnEncrypt(input: Crypto.OnEncryptInput) 
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

    method OnDecrypt(input: Crypto.OnDecryptInput)
      returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )
  }
}
