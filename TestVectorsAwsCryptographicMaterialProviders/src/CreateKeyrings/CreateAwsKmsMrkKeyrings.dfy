// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateAwsKmsMrkKeyrings {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import TestVectorsUtils
  import opened TestVectorConstants

  method CreateAllAwsKmsMrkKeyring(input: EncryptDecryptKeyrings)
    returns (allAwsKmsMrk: seq<Types.IKeyring>)
    requires input.AwsKmsMrkKeyring?
    ensures forall keyring | keyring in allAwsKmsMrk
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    allAwsKmsMrk := [];

    for i := 0 to |AllAwsKMSKeys|
      invariant forall keyring | keyring in allAwsKmsMrk
        ::
          && keyring.ValidState()
          && fresh(keyring)
          && fresh(keyring.Modifies)
    {
      var (kmsKeyId, region) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsMrkKeyring(kmsKeyId, region);
      allAwsKmsMrk := allAwsKmsMrk + [keyring];
    }
  }

  method CreateAwsKmsMrkKeyring(
    kmsKeyId: string,
    region: string
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    print "\n CreateAwsKmsMrkKeyring: ", kmsKeyId, " ", region;

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput);
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput( region := region ));

    keyring :- expect mpl.CreateAwsKmsMrkKeyring(Types.CreateAwsKmsMrkKeyringInput(
      kmsKeyId := kmsKeyId,
      kmsClient := kmsClient,
      grantTokens := None
    ));
  }
}