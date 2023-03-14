// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateAwsKmsKeyrings {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import TestVectorsUtils
  import opened TestVectorConstants

  method CreateAllAwsKmsKeyring(input: EncryptDecryptKeyrings)
    returns (allAwsKms: seq<Types.IKeyring>)
    requires input.AwsKmsKeyring?
    ensures forall keyring | keyring in allAwsKms
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    allAwsKms := [];

    for i := 0 to |AllAwsKMSKeys|
      invariant forall keyring | keyring in allAwsKms
        ::
          && keyring.ValidState()
          && fresh(keyring)
          && fresh(keyring.Modifies)
    {
      var (kmsKeyId, region) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsKeyring(kmsKeyId, region);
      allAwsKms := allAwsKms + [keyring];
    }
  }

  method CreateAwsKmsKeyring(
    kmsKeyId: string,
    region: string
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    print "\n CreateAwsKmsKeyring: ", kmsKeyId, " ", region;

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput);
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput( region := region ));

    keyring :- expect mpl.CreateAwsKmsKeyring(Types.CreateAwsKmsKeyringInput(
      kmsKeyId := kmsKeyId,
      kmsClient := kmsClient,
      grantTokens := None
    ));

  }

}