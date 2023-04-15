// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateAwsKmsMultiKeyrings {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import TestVectorsUtils
  import opened TestVectorConstants

  method CreateAllAwsKmsMultiKeyring(input: EncryptDecryptKeyrings)
    returns (allAwsKmsMrkMult: seq<Types.IKeyring>)
    requires input.AwsKmsMultiKeyring?
    ensures forall keyring | keyring in allAwsKmsMrkMult
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    allAwsKmsMrkMult := [];

    for i := 0 to |AllAwsKMSKeys|
      invariant forall keyring | keyring in allAwsKmsMrkMult
        ::
          && keyring.ValidState()
          && fresh(keyring)
          && fresh(keyring.Modifies)
    {
      var (kmsKeyId, _) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsMultiKeyring(Some(kmsKeyId), None);
      allAwsKmsMrkMult := allAwsKmsMrkMult + [keyring];
    }
  }

  method CreateAwsKmsMultiKeyring(
    kmsKeyId: Option<Types.KmsKeyId>,
    kmsKeyIds: Option<Types.KmsKeyIdList>
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    print "\n CreateAwsKmsMultiKeyring: ", kmsKeyId, " ", kmsKeyIds;

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    keyring :- expect mpl.CreateAwsKmsMultiKeyring(Types.CreateAwsKmsMultiKeyringInput(
      generator := kmsKeyId,
      kmsKeyIds := kmsKeyIds,
      clientSupplier := None,
      grantTokens := None
    ));

  }

}