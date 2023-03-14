// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateAwsKmsMrkMultiKeyrings {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import TestVectorsUtils
  import opened TestVectorConstants

  method CreateAllAwsKmsMrkMultiKeyring(input: EncryptDecryptKeyrings)
    returns (allAwsKmsMrkMult: seq<Types.IKeyring>)
    requires input.AwsKmsMrkMultiKeyring?
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
      var keyring := CreateAwsKmsMrkMultiKeyring(Some(kmsKeyId), None);
      allAwsKmsMrkMult := allAwsKmsMrkMult + [keyring];
    }
  }

  method CreateAwsKmsMrkMultiKeyring(
    kmsKeyId: Option<Types.KmsKeyId>,
    kmsKeyIds: Option<Types.KmsKeyIdList>
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    print "\n CreateAwsKmsMrkMultiKeyring: ", kmsKeyId, " ", kmsKeyIds;

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    keyring :- expect mpl.CreateAwsKmsMrkMultiKeyring(Types.CreateAwsKmsMrkMultiKeyringInput(
      generator := kmsKeyId,
      kmsKeyIds := kmsKeyIds,
      clientSupplier := None,
      grantTokens := None
    ));

  }

}