// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/KeyManagementService.dfy"
include "../Util/UTF8.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/RSAEncryption.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "Keyrings/MultiKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsUtils.dfy"
include "Keyrings/RawRSAKeyring.dfy"
include "CMMs/DefaultCMM.dfy"
include "Materials.dfy"
include "AlgorithmSuites.dfy"
include "Keyrings/AwsKms/AwsKmsStrictKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsArnParsing.dfy"

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
  import RSAEncryption
  import RawAESKeyring
  import RawRSAKeyring
  import MultiKeyring
  import DefaultCMM
  import AlgorithmSuites
  import Materials
  import AwsKmsStrictKeyring
  import AwsKmsMrkAwareSymmetricKeyring
  import AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
  import AwsKmsDiscoveryKeyring
  import AwsKmsArnParsing
  import AwsKmsUtils
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
    provides Crypto, AlgorithmSuites, Materials, Wrappers
    // Class
    reveals AwsCryptographicMaterialProvidersClient
    // Functions
    reveals SpecificationClient, SpecificationClient.GetSuite
    // Class Members
    provides
      AwsCryptographicMaterialProvidersClient.CreateRawAesKeyring,
      AwsCryptographicMaterialProvidersClient.CreateStrictAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareStrictAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareDiscoveryAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateAwsKmsDiscoveryKeyring,
      AwsCryptographicMaterialProvidersClient.CreateDefaultCryptographicMaterialsManager,
      AwsCryptographicMaterialProvidersClient.CreateMultiKeyring,
      AwsCryptographicMaterialProvidersClient.CreateRawRsaKeyring

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
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
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

      var keyring := new RawAESKeyring.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
      return Success(keyring);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput)
      returns (res: Result<Crypto.ICryptographicMaterialsManager, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
        var cmm := new DefaultCMM.DefaultCMM.OfKeyring(input.keyring);
        return Success(cmm);
    }

    method CreateStrictAwsKmsKeyring(input: Crypto.CreateStrictAwsKmsKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      // TODO: return proper exceptions
      expect AwsKmsArnParsing.ParseAwsKmsIdentifier(input.kmsKeyId).Success?;
      expect UTF8.IsASCIIString(input.kmsKeyId);
      expect 0 < |input.kmsKeyId| <= AwsKmsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH;

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var keyring := new AwsKmsStrictKeyring.AwsKmsStrictKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
      return Success(keyring);
    }

    method CreateMrkAwareStrictAwsKmsKeyring(input: Crypto.CreateMrkAwareStrictAwsKmsKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      // TODO: return proper exceptions
      expect AwsKmsArnParsing.ParseAwsKmsIdentifier(input.kmsKeyId).Success?;
      expect UTF8.IsASCIIString(input.kmsKeyId);
      expect 0 < |input.kmsKeyId| <= AwsKmsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH;

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var keyring := new AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
      return Success(keyring);
    }

    method CreateMrkAwareDiscoveryAwsKmsKeyring(input: Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      // TODO: validation on discovery filter

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
      //= type=implication
      //# The keyring SHOULD fail initialization if the
      //# provided region does not match the region of the KMS client.
      // TODO: uncomment once we are returning Result<IKeyring>
      //:- Need(AwsKmsUtils.RegionMatch(input.kmsClient, input.region), "Provided client and region do not match");

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);

      // TODO: update to not 'expect' once we can return Result<IKeyring>
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var keyring := new AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring(input.kmsClient, input.region, input.discoveryFilter, grantTokens);
      return Success(keyring);
    }

    method CreateAwsKmsDiscoveryKeyring(input: Crypto.CreateAwsKmsDiscoveryKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      // TODO: validation on discovery filter

      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);

      // TODO: update to not 'expect' once we can return Result<IKeyring>
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var keyring := new AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring(input.kmsClient, input.discoveryFilter, grantTokens);
      return Success(keyring);
    }


    method CreateMultiKeyring(input: Crypto.CreateMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      if input.generator == null && |input.childKeyrings| == 0 {
        var error := new Crypto.AwsCryptographicMaterialProvidersClientException(
          "Must include a generator keyring and/or at least one child keyring");
        return Failure(error);
      }

      var keyring := new MultiKeyring.MultiKeyring(input.generator, input.childKeyrings);
      return Success(keyring);
    }

    method CreateRawRsaKeyring(input: Crypto.CreateRawRsaKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
      //= compliance/framework/raw-rsa-keyring.txt#2.1.1
      //= type=implication
      //# -  Raw RSA keyring MUST NOT accept a key namespace of "aws-kms".
      ensures
        input.keyNamespace == "aws-kms"
      ==>
        res.Failure?
      ensures
        input.publicKey.None? && input.privateKey.None?
      ==>
        res.Failure?
    {
      // :- Need(
      //   input.keyNamespace != "aws-kms",
      //   "keyNamespace must not be `aws-kms`"
      // );
      if (input.keyNamespace == "aws-kms") {
        var error := new Crypto.AwsCryptographicMaterialProvidersClientException(
          "keyNamespace must not be `aws-kms`");
        return Failure(error);
      }

      // :- Need(
      //   input.publicKey.Some? || input.privateKey.Some?,
      //   "A publicKey or a privateKey is required"
      // );
      if (input.publicKey.None? && input.privateKey.None?) {
        var error := new Crypto.AwsCryptographicMaterialProvidersClientException(
          "A publicKey or a privateKey is required");
        return Failure(error);
      }

      var padding: RSAEncryption.PaddingMode := match input.paddingScheme
        case PKCS1 => RSAEncryption.PaddingMode.PKCS1
        case OAEP_SHA1_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA1
        case OAEP_SHA256_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA256
        case OAEP_SHA384_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA384
        case OAEP_SHA512_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA512
      ;

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

      expect |namespace| < UINT16_LIMIT;  // Both name & namespace will be serialized into the message
      expect |name| < UINT16_LIMIT;       // So both must respect message size limit
      var keyring := new RawRSAKeyring.RawRSAKeyring(namespace, name, input.publicKey, input.privateKey, padding);
      return Success(keyring);
    }
  }
}
