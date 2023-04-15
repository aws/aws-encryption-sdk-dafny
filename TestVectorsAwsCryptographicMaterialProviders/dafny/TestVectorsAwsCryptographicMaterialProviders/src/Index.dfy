// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "KeyringExpectations.dfy"
include "CreateKeyrings.dfy"

module WrappedMaterialProvidersMain {
  import WrappedMaterialProviders
  import KeyringExpectations
  import CreateKeyrings

  // Currently this is chekcing
  // that keyrings can encrypt and decrypt encrypted data keys.
  // The Scope of testing can be seen in TestVectorConstants.dfy
  method CheckKeyrings() {

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var all := CreateKeyrings.CreateAllEncryptDecryptKeyrings();

    for i := 0 to |all|
    {
      var keyring := all[i];
      KeyringExpectations.ExpectAlgorithmSuiteKeyringSuccess(
        mpl,
        keyring
      );
    }
  }
}
