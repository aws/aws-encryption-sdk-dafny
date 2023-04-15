// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "TestVectorsUtils.dfy"
include "TestVectorConstants.dfy"

module KeyringExpectations {
  import opened Wrappers
  import WrappedMaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes
  
  import opened TestVectorConstants
  import TestVectorsUtils

  datatype Materials =
  | Materials(
    encryptionMaterials: Types.EncryptionMaterials,
    decryptionMaterials: Types.DecryptionMaterials
  )

  // This method tests that a keyring can create an encrypted data key
  // and then decrypt that encrypted data key
  // for every algorithm suite listed in `AllAlgorithmSuiteIds`.
  method ExpectAlgorithmSuiteKeyringSuccess(
    mpl: Types.IAwsCryptographicMaterialProvidersClient,
    keyring: Types.IKeyring
  )
    requires keyring.ValidState() && mpl.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState() && mpl.ValidState()
  {
    var encryptionContext := TestVectorsUtils.SmallEncryptionContext(TestVectorsUtils.SmallEncryptionContextVariation.A);

    for i := 0 to |AllAlgorithmSuiteIds|
    {
      var algorithmSuiteId := AllAlgorithmSuiteIds[i];

      var encryptionMaterials := TestVectorsUtils.GetEncryptionMaterials(
        mpl,
        algorithmSuiteId,
        encryptionContext
      );
      // I don't need the results at this time
      var _ := ExpectKeyringSuccess(mpl, keyring, encryptionMaterials);
    }
  }

  method ExpectKeyringSuccess(
    mpl: Types.IAwsCryptographicMaterialProvidersClient,
    keyring: Types.IKeyring,
    encryptionMaterialsIn: Types.EncryptionMaterials
  )
    returns (results: Materials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()

    ensures results.encryptionMaterials.plaintextDataKey == results.decryptionMaterials.plaintextDataKey;
    // More?
  {

    print "\n ExpectKeyringSuccess:\n", encryptionMaterialsIn.algorithmSuite.id;

    var encryptionMaterials := ExpectOnEncryptSuccess(mpl, keyring, encryptionMaterialsIn);

    // Revers the operation
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := encryptionMaterials.algorithmSuite.id,
        requiredEncryptionContextKeys := [],
        // NOTE to support signatures, we MUST use the returned EC
        encryptionContext := encryptionMaterials.encryptionContext
      )
    );

    var decryptionMaterials := ExpectOnDecryptSuccess(
      mpl,
      keyring,
      decryptionMaterialsIn,
      encryptionMaterials.encryptedDataKeys
    );

    // We got back what we put in
    expect encryptionMaterials.plaintextDataKey == decryptionMaterials.plaintextDataKey;

    results := Materials(encryptionMaterials, decryptionMaterials);
  }

  method ExpectOnEncryptSuccess(
    mpl: Types.IAwsCryptographicMaterialProvidersClient,
    keyring: Types.IKeyring,
    encryptionMaterialsIn: Types.EncryptionMaterials
  )
    returns (encryptionMaterials: Types.EncryptionMaterials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()

    ensures mpl.ValidEncryptionMaterialsTransition(
      Types.ValidEncryptionMaterialsTransitionInput(
        start := encryptionMaterialsIn,
        stop := encryptionMaterials
      ) 
    ).Success?
    ensures mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterials).Success?
  {

    // Run the test
    var encryptionMaterialsOut :- expect keyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );

    encryptionMaterials := encryptionMaterialsOut.materials;

    // Only the right things changed 
    var _ :- expect mpl.ValidEncryptionMaterialsTransition(
      Types.ValidEncryptionMaterialsTransitionInput(
        start := encryptionMaterialsIn,
        stop := encryptionMaterials
      ) 
    );

    // The resultant materials is valid
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterials);

    // This is Ensured by the above
    expect 1 <= |encryptionMaterialsOut.materials.encryptedDataKeys|;
  }

  method ExpectOnDecryptSuccess(
    mpl: Types.IAwsCryptographicMaterialProvidersClient,
    keyring: Types.IKeyring,
    decryptionMaterialsIn: Types.DecryptionMaterials,
    encryptedDataKeys: Types.EncryptedDataKeyList
  )
    returns (decryptionMaterials: Types.DecryptionMaterials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()

    ensures mpl.ValidDecryptionMaterialsTransition(
      Types.ValidDecryptionMaterialsTransitionInput(
        start := decryptionMaterialsIn,
        stop := decryptionMaterials
      )
    ).Success?
    ensures mpl.DecryptionMaterialsWithPlaintextDataKey(decryptionMaterials).Success?
  {

    // Run the test
    var decryptionMaterialsOut :- expect keyring.OnDecrypt(
      Types.OnDecryptInput(
        materials := decryptionMaterialsIn,
        encryptedDataKeys := encryptedDataKeys
      )
    );

    decryptionMaterials := decryptionMaterialsOut.materials;

    // Only the right things changed
    var _ :- expect mpl.ValidDecryptionMaterialsTransition(
      Types.ValidDecryptionMaterialsTransitionInput(
        start := decryptionMaterialsIn,
        stop := decryptionMaterials
      )
    );

    // The resultant materials is valid
    var _ :- expect mpl.DecryptionMaterialsWithPlaintextDataKey(decryptionMaterials);

  }

}