// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/KeyManagementService.dfy"
include "../Util/UTF8.dfy"
include "../Crypto/AESEncryption.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "Keyrings/MultiKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "CMMs/DefaultCMM.dfy"
include "Materials.dfy"
include "AlgorithmSuites.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.dfy"
include "../KMS/AwsKmsArnParsing.dfy"

module
  {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient"}
  MaterialProviders.Client
{
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Aws.Crypto
  import AESEncryption
  import RawAESKeyring
  import MultiKeyring
  import DefaultCMM
  import AlgorithmSuites
  import Materials
  import AwsKmsMrkAwareSymmetricKeyring
  import AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
  import AwsKmsDiscoveryKeyring
  import AwsKmsArnParsing
  import GeneratedKMS = Com.Amazonaws.Kms

  // This file is the entry point for all Material Provider operations.
  // There MUST NOT be any direct includes to any other files in this project.
  // The `constructor` for this `Client` is how any default
  // or unanticipated behavior change will be made.
  // Further anyone implementing their own CMM or Keyring
  // needs to use this `Client` to access the required functions
  // to ensure correctness of their components.
  // This means that anything needed for the `Keyring` or `CMM` traits.

  export
    // Modules
    provides Crypto, AlgorithmSuites, Materials
    // Class
    reveals AwsCryptographicMaterialProvidersClient
    // Functions
    reveals SpecificationClient, SpecificationClient.GetSuite
    // Class Members
    provides
      AwsCryptographicMaterialProvidersClient.CreateRawAesKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareStrictAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareDiscoveryAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateAwsKmsDiscoveryKeyring,
      AwsCryptographicMaterialProvidersClient.CreateDefaultCryptographicMaterialsManager,
      AwsCryptographicMaterialProvidersClient.CreateMultiKeyring

  datatype SpecificationClient = SpecificationClient(
    // Whatever top level closure is added to the constructor needs to be added here
  )
  {
    function method GetSuite(
      id: Crypto.AlgorithmSuiteId
    ):
      (res: AlgorithmSuites.AlgorithmSuite)
      ensures res.id == id
    {
      AlgorithmSuites.GetSuite(id)
    }
  }

  class AwsCryptographicMaterialProvidersClient
    extends Crypto.IAwsCryptographicMaterialsProviderClient
  {
    constructor () {}
    method CreateRawAesKeyring(input: Crypto.CreateRawAesKeyringInput)
      returns (res: Crypto.IKeyring)
    {
      var wrappingAlg:AESEncryption.AES_GCM := match input.wrappingAlg
        case ALG_AES128_GCM_IV12_TAG16 => AESEncryption.AES_GCM(
            keyLength := 16 as AESEncryption.KeyLength,
            tagLength := 16 as AESEncryption.TagLength,
            ivLength := 12 as AESEncryption.IVLength
          )
        case ALG_AES192_GCM_IV12_TAG16 => AESEncryption.AES_GCM(
            keyLength := 24 as AESEncryption.KeyLength,
            tagLength := 16 as AESEncryption.TagLength,
            ivLength := 12 as AESEncryption.IVLength
          )
        case ALG_AES256_GCM_IV12_TAG16 => AESEncryption.AES_GCM(
            keyLength := 32 as AESEncryption.KeyLength,
            tagLength := 16 as AESEncryption.TagLength,
            ivLength := 12 as AESEncryption.IVLength
          );

      // I have no idea why :- isn't working here...
      // Here is why: To use :- requires the type of "res" to be "Result<Crypto.IKeyring, string>".
      var namespaceRes := UTF8.Encode(input.keyNamespace);
      var namespace := []; // TODO: This value gets used below if UTF8.Encode fails
      if namespaceRes.Success? {
        namespace := namespaceRes.value;
      }
      var nameRes := UTF8.Encode(input.keyName);
      var name := []; // TODO: This value gets used below if UTF8.Encode fails
      if nameRes.Success? {
        name := nameRes.value;
      }

      expect |namespace| < UINT16_LIMIT;
      expect |input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32;
      expect |input.wrappingKey| == wrappingAlg.keyLength as int;

      return new RawAESKeyring.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput)
      returns (res: Crypto.ICryptographicMaterialsManager)
    {
        return new DefaultCMM.DefaultCMM.OfKeyring(input.keyring);
    }

    method CreateMrkAwareStrictAwsKmsKeyring(input: Crypto.CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: Crypto.IKeyring)
    {
      expect AwsKmsArnParsing.ParseAwsKmsIdentifier(input.kmsKeyId).Success?;
      expect UTF8.IsASCIIString(input.kmsKeyId);
      expect 0 < |input.kmsKeyId| <= AwsKmsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH;

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      return new AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
    }

    method CreateMrkAwareDiscoveryAwsKmsKeyring(input: Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput) returns (res: Crypto.IKeyring)
    {
      // TODO: validation on discovery filter

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);

      // TODO: update to not 'expect' once we can return Result<IKeyring>
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      return new AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring(input.kmsClient, input.region, input.discoveryFilter, grantTokens);
    }

    method CreateAwsKmsDiscoveryKeyring(input: Crypto.CreateAwsKmsDiscoveryKeyringInput) returns (res: Crypto.IKeyring)
    {
      // TODO: validation on discovery filter

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);

      // TODO: update to not 'expect' once we can return Result<IKeyring>
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      return new AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring(input.kmsClient, input.discoveryFilter, grantTokens);
    }


    method CreateMultiKeyring(input: Crypto.CreateMultiKeyringInput)
      returns (res: Crypto.IKeyring?)
    {

      if input.generator == null && |input.childKeyrings| == 0 {
         // TODO: placeholder, update once we can return Result<>
        return null;
      }

      return new MultiKeyring.MultiKeyring(input.generator, input.childKeyrings);
    }
  }
}
