// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../LibraryIndex.dfy"
include "../TestVectorsUtils.dfy"
include "../TestVectorConstants.dfy"

module CreateRawAesKeyrings {
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

  method CreateAllRawAesKeyring(input: TestVectorConstants.EncryptDecryptKeyrings)
    returns (allAES: seq<Types.IKeyring>)
    requires input.RawAesKeyring?
    ensures forall keyring | keyring in allAES
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    allAES := [];
    var AllAesWrappingAlgs := set w: Types.AesWrappingAlg | true;
    while AllAesWrappingAlgs != {}
      invariant forall keyring | keyring in allAES
        ::
          && keyring.ValidState()
          && fresh(keyring)
          && fresh(keyring.Modifies)
    {
      var wrappingAlg :| wrappingAlg in AllAesWrappingAlgs;
      var keyring := CreateRawAesKeyring(wrappingAlg);
      allAES := allAES + [keyring];
      AllAesWrappingAlgs := AllAesWrappingAlgs - {wrappingAlg};
    }
  }

  method CreateRawAesKeyring(
    wrappingAlg: Types.AesWrappingAlg
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    print "\n CreateRawAesKeyring: ", wrappingAlg;

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var crypto :- expect Primitives.AtomicPrimitives();

    var length := match wrappingAlg
      case ALG_AES128_GCM_IV12_TAG16 => 16
      case ALG_AES192_GCM_IV12_TAG16 => 24
      case ALG_AES256_GCM_IV12_TAG16 => 32;

    var wrappingKey :- expect crypto.GenerateRandomBytes(
      Crypto.GenerateRandomBytesInput(
        length := length
      )
    );

    var namespace, name := TestVectorsUtils.NamespaceAndName(0);
    keyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := wrappingKey,
      wrappingAlg := wrappingAlg
    ));
  }

}
