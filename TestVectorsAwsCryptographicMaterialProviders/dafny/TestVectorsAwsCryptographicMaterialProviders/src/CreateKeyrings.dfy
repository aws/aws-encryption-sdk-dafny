// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "TestVectorsUtils.dfy"
include "TestVectorConstants.dfy"
include "CreateKeyrings/CreateAwsKmsKeyrings.dfy"
include "CreateKeyrings/CreateAwsKmsMultiKeyrings.dfy"
include "CreateKeyrings/CreateAwsKmsMrkKeyrings.dfy"
include "CreateKeyrings/CreateAwsKmsMrkMultiKeyrings.dfy"
include "CreateKeyrings/CreateRawAesKeyrings.dfy"
include "CreateKeyrings/CreateRawRsaKeyrings.dfy"

module CreateKeyrings {
  import opened Wrappers
  import opened TestVectorConstants

  // Import all the keyring factorys
  import CreateAwsKmsKeyrings
  import CreateAwsKmsMultiKeyrings
  import CreateAwsKmsMrkKeyrings
  import CreateAwsKmsMrkMultiKeyrings
  import CreateRawAesKeyrings
  import CreateRawRsaKeyrings

  method CreateAllEncryptDecryptKeyrings()
    returns (all: seq<Types.IKeyring>)
    ensures forall keyring | keyring in all
    ::
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {

    all := [];
    for i := 0 to |AllEncryptDecryptKeyrings|
      invariant forall keyring | keyring in all
      ::
        && keyring.ValidState()
        && fresh(keyring)
        && fresh(keyring.Modifies)
    {
      var keyringType := AllEncryptDecryptKeyrings[i];
      match keyringType
        case AwsKmsKeyring() =>
          var allAwsKms := CreateAwsKmsKeyrings.CreateAllAwsKmsKeyring(keyringType);
          all := all + allAwsKms;
        case AwsKmsMultiKeyring() =>
          var allAwsKms := CreateAwsKmsMultiKeyrings.CreateAllAwsKmsMultiKeyring(keyringType);
          all := all + allAwsKms;
        case AwsKmsMrkKeyring() =>
          var allAwsKmsMrk := CreateAwsKmsMrkKeyrings.CreateAllAwsKmsMrkKeyring(keyringType);
          all := all + allAwsKmsMrk;
        case AwsKmsMrkMultiKeyring() =>
          var allAwsKmsMrkMult := CreateAwsKmsMrkMultiKeyrings.CreateAllAwsKmsMrkMultiKeyring(keyringType);
          all := all + allAwsKmsMrkMult;
        case RawAesKeyring() =>
          var allRSA := CreateRawAesKeyrings.CreateAllRawAesKeyring(keyringType);
          all := all + allRSA;
        case RawRsaKeyring() =>
          var allAES := CreateRawRsaKeyrings.CreateAllRawRsaKeyring(keyringType);
          all := all + allAES;
    }
  }

}