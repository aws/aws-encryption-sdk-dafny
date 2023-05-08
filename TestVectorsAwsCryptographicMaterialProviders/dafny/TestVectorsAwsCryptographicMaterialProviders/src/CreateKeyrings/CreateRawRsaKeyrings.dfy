// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateRawRsaKeyrings {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import TestVectorsUtils
  import opened TestVectorConstants

  // This is cheating,
  // I know that this MUST be here
  // because this is required for MPL
  import Aws.Cryptography.Primitives
  import Crypto = AwsCryptographyPrimitivesTypes

  method CreateAllRawRsaKeyring(input: TestVectorConstants.EncryptDecryptKeyrings)
    returns (allRSA: seq<Types.IKeyring>)
    requires input.RawRsaKeyring?
    ensures forall keyring | keyring in allRSA
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    allRSA := [];
    var AllPaddingSchemes := set w: Types.PaddingScheme | true;
    while AllPaddingSchemes != {}
      invariant forall keyring | keyring in allRSA
        ::
          && keyring.ValidState()
          && fresh(keyring)
          && fresh(keyring.Modifies)
    {
      var paddingScheme :| paddingScheme in AllPaddingSchemes;
      var keyring := CreateRawRsaKeyring(paddingScheme);
      allRSA := allRSA + [keyring];
      AllPaddingSchemes := AllPaddingSchemes - {paddingScheme};
    }
  }

  method CreateRawRsaKeyring(
    paddingScheme: Types.PaddingScheme
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var crypto :- expect Primitives.AtomicPrimitives();

    var keys :- expect crypto.GenerateRSAKeyPair(
      Crypto.GenerateRSAKeyPairInput(
        lengthBits := 2048
      )
    );

    var namespace, name := TestVectorsUtils.NamespaceAndName(0);
    keyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := paddingScheme,
      publicKey := Option.Some(keys.publicKey.pem),
      privateKey := Option.Some(keys.privateKey.pem)
    ));
  }

}
