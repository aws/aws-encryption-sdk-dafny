// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsRsaKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Keyring
  import Materials
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = ComAmazonawsKmsTypes

  class AwsKmsRsaKeyring
    extends Keyring.VerifiableInterface
  {

    predicate ValidState()
    ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    constructor (
      publicKey: Option<seq<uint8>>,
      kmsKeyId: string,
      encryptionAlgorithm: KMS.EncryptionAlgorithmSpec,
      client: Option<KMS.IKeyManagementServiceClient>,
      grantTokens: KMS.GrantTokenList
    )
      ensures ValidState() && fresh(this) && fresh(History)
        && fresh(Modifies - (if client.Some? then client.value.Modifies else {}))
    {
      // TODO set up keyring

      History := new Types.IKeyringCallHistory();
      Modifies := {History};
      if client.Some? {
        Modifies := Modifies + client.value.Modifies;
      }
    }

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}
    
    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History) 
      ensures res.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          res.value.materials
        )
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(message := "Unimplemented"));
    }

     predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}
    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials)
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(message := "Unimplemented"));
    }
  }
}
