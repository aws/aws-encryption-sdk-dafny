// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Crypto/AESEncryption.dfy"
include "../Crypto/RSAEncryption.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/KeyManagementService.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"
include "../Util/UTF8.dfy"
include "AlgorithmSuites.dfy"
include "DefaultClientSupplier.dfy"
include "CMMs/DefaultCMM.dfy"
include "Keyrings/AwsKms/AwsKmsArnParsing.dfy"
include "Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAreUnique.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsStrictKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsUtils.dfy"
include "Keyrings/MultiKeyring.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "Keyrings/RawRSAKeyring.dfy"
include "Materials.dfy"

module
  {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient"}
  MaterialProviders.Client
{
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import UTF8
  import Seq
  import AESEncryption
  import AlgorithmSuites
  import Aws.Crypto
  import AwsKmsArnParsing
  import AwsKmsDiscoveryKeyring
  import AwsKmsMrkAreUnique
  import AwsKmsMrkAwareSymmetricKeyring
  import AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
  import AwsKmsStrictKeyring
  import AwsKmsUtils
  import Commitment
  import DefaultCMM
  import DefaultClientSupplier
  import GeneratedKMS = Com.Amazonaws.Kms
  import Materials
  import MultiKeyring
  import RSAEncryption
  import RawAESKeyring
  import RawRSAKeyring


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
    reveals
      SpecificationClient,
      SpecificationClient.GetSuite
    provides
      SpecificationClient.ValidateCommitmentPolicyOnEncrypt,
      SpecificationClient.ValidateCommitmentPolicyOnDecrypt
    // Class Members
    provides
      AwsCryptographicMaterialProvidersClient.CreateAwsKmsDiscoveryKeyring,
      AwsCryptographicMaterialProvidersClient.CreateDefaultClientSupplier,
      AwsCryptographicMaterialProvidersClient.CreateDefaultCryptographicMaterialsManager,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareDiscoveryAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareDiscoveryMultiKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareStrictAwsKmsKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMrkAwareStrictMultiKeyring,
      AwsCryptographicMaterialProvidersClient.CreateMultiKeyring,
      AwsCryptographicMaterialProvidersClient.CreateRawAesKeyring,
      AwsCryptographicMaterialProvidersClient.CreateRawRsaKeyring,
      AwsCryptographicMaterialProvidersClient.CreateStrictAwsKmsKeyring

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

    // We want to make these validation methods available to our internal callers
    // (e.g. the ESDK, which also needs to validate commitment policies), but
    // they do not need to be part of the public model. Note that this might
    // need to be tweaked when we extract the material provider library
    method ValidateCommitmentPolicyOnEncrypt(
      algorithm: Crypto.AlgorithmSuiteId,
      commitmentPolicy: Crypto.CommitmentPolicy
    )
      returns (res: Result<bool, string>)
    {
      res := Commitment.ValidateCommitmentPolicyOnEncrypt(algorithm, commitmentPolicy);
    }

    method ValidateCommitmentPolicyOnDecrypt(
      algorithm: Crypto.AlgorithmSuiteId,
      commitmentPolicy: Crypto.CommitmentPolicy
    )
      returns (res: Result<bool, string>)
    {
      res := Commitment.ValidateCommitmentPolicyOnDecrypt(algorithm, commitmentPolicy);
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

    method CreateMrkAwareStrictMultiKeyring(input: Crypto.CreateMrkAwareStrictMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //# If a regional client supplier is
      //# not passed, then a default MUST be created that takes a region string
      //# and generates a default AWS SDK client for the given region.
      if input.clientSupplier == null {
        var clientSupplierOutput := CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
        clientSupplier := clientSupplierOutput.clientSupplier;
      } else {
        clientSupplier := input.clientSupplier;
      }
      res := StrictMultiKeyring(
        input.generator,
        input.kmsKeyIds,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }

    method StrictMultiKeyring(
      generator: Option<string>,
      awsKmsKeys: Option<seq<string>>,
      clientSupplier: Crypto.IClientSupplier,
      grantTokens: Option<GeneratedKMS.GrantTokenList>
    )
      returns (res: Result<MultiKeyring.MultiKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //= type=implication
      //# If any of the AWS KMS key identifiers is null or an empty string this
      //# function MUST fail.
      //# At least one non-null or non-empty string AWS
      //# KMS key identifiers exists in the input this function MUST fail.
      ensures
        || (generator.Some? && generator.value == "")
        || (awsKmsKeys.Some? && (exists k | k in awsKmsKeys.value :: k == ""))
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //= type=implication
      //# All
      //# AWS KMS identifiers are passed to Assert AWS KMS MRK are unique (aws-
      //# kms-mrk-are-unique.md#Implementation) and the function MUST return
      //# success otherwise this MUST fail.
      ensures
        var allStrings := if generator.Some? then
          [generator.value] + awsKmsKeys.UnwrapOr([])
        else
          awsKmsKeys.UnwrapOr([]);
        var allIdentifiers := Seq.MapWithResult(AwsKmsArnParsing.IsAwsKmsIdentifierString, allStrings);
        || allIdentifiers.Failure?
        || (allIdentifiers.Success? && AwsKmsMrkAreUnique.AwsKmsMrkAreUnique(allIdentifiers.value).Fail?)
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //= type=implication
      //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
      //# by using this generator keyring as the generator keyring (../multi-
      //# keyring.md#generator-keyring) and this set of child keyrings as the
      //# child keyrings (../multi-keyring.md#child-keyrings).
      //# This Multi-
      //# Keyring MUST be this functions output.
      ensures
        && res.Success?
      ==>
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
        //= type=implication
        //# If there is a generator input then the generator keyring MUST be a
        //# AWS KMS MRK Aware Symmetric Keyring (aws-kms-mrk-aware-symmetric-
        //# keyring.md) initialized with
        && (generator.Some?
        ==>
          && res.value.generatorKeyring is AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring
          && var g := res.value.generatorKeyring as AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring;
          && g.awsKmsKey == generator.value
          && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
        && (generator.None?
        ==>
          && res.value.generatorKeyring == null)
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
        //= type=implication
        //# If there is a set of child identifiers then a set of AWS KMS MRK
        //# Aware Symmetric Keyring (aws-kms-mrk-aware-symmetric-keyring.md) MUST
        //# be created for each AWS KMS key identifier by initialized each
        //# keyring with
        && (awsKmsKeys.Some?
        ==>
          && |awsKmsKeys.value| == |res.value.childKeyrings|
          && forall index | 0 <= index < |awsKmsKeys.value| ::
            // AWS KMS MRK Aware Symmetric Keying must be created for each AWS KMS Key identifier
            && var childKeyring: Crypto.IKeyring := res.value.childKeyrings[index];
            && childKeyring is AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring
            && var awsKmsChild := childKeyring as AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring;
            // AWS KMS key identifier
            && awsKmsChild.awsKmsKey == awsKmsKeys.value[index]
            // The input list of AWS KMS grant tokens
            && (grantTokens.Some? ==> awsKmsChild.grantTokens == grantTokens.value))
        && (awsKmsKeys.None?
        ==>
          && res.value.childKeyrings == [])
    {
      var allStrings := match (generator) {
        case Some(g) => [g] + awsKmsKeys.UnwrapOr([])
        case None => awsKmsKeys.UnwrapOr([])
      };
      assert generator.Some? ==> generator.value in allStrings;
      assert awsKmsKeys.Some? ==> forall k | k in awsKmsKeys.value :: k in allStrings;

      var allIdentifiersResults := Seq.MapWithResult(
        AwsKmsArnParsing.IsAwsKmsIdentifierString,
        allStrings
      );
      var allIdentifiers :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(
        allIdentifiersResults
      );
      var mrkAreUniqueRes := AwsKmsMrkAreUnique.AwsKmsMrkAreUnique(allIdentifiers);
      :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapOutcomeString(
        mrkAreUniqueRes
      );
      
      var generatorKeyring : AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring?;
      match generator {
        case Some(generatorIdentifier) =>
          var arnRes := AwsKmsArnParsing.IsAwsKmsIdentifierString(generatorIdentifier);
          var arn :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(
            arnRes
          );
          var region := AwsKmsArnParsing.GetRegion(arn);
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
          //= type=implication
          //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
          //# default region.
          //Question: What should the behavior be if there is no region supplied?
          // I assume that the SDK will use the default region or throw an error
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
          generatorKeyring := new AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring(
            client,
            generatorIdentifier,
            grantTokens.UnwrapOr([])
          );           
        case None() => generatorKeyring := null;
      }

      var children : seq<AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring> := [];

      match awsKmsKeys {
        case Some(childIdentifiers) =>
          for index := 0 to |childIdentifiers|
            invariant |awsKmsKeys.value[..index]| == |children|
            invariant forall index | 0 <= index < |children|
            ::
              && children[index].awsKmsKey == awsKmsKeys.value[index]
              && (grantTokens.Some? ==> children[index].grantTokens == grantTokens.value)
          {
            var childIdentifier := childIdentifiers[index];
            var infoRes := AwsKmsArnParsing.IsAwsKmsIdentifierString(childIdentifier);
            var info :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(
              infoRes
            );
            var region := AwsKmsArnParsing.GetRegion(info);
            //Question: What should the behavior be if there is no region supplied?
            // I assume that the SDK will use the default region or throw an error
            var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
            var keyring := new AwsKmsMrkAwareSymmetricKeyring.AwsKmsMrkAwareSymmetricKeyring(
              client,
              childIdentifier,
              grantTokens.UnwrapOr([])
            );  
            // Order is important
            children := children + [keyring];
          }
        case None() =>
          children := [];
      }

      :- Crypto.Need(
        generatorKeyring != null || children != [],
        "generatorKeyring or child Keryings needed to create a multi keyring"
      );
      var keyring := new MultiKeyring.MultiKeyring(
        generatorKeyring,
        children
      );

      return Success(keyring);
    }

    method CreateMrkAwareDiscoveryMultiKeyring(input: Crypto.CreateMrkAwareDiscoveryMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens: Crypto.GrantTokenList := input.grantTokens.UnwrapOr([]);
      expect 0 <= |grantTokens| <= 10;
      expect forall grantToken | grantToken in grantTokens :: 1 <= |grantToken| <= 8192;

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //# If a regional client supplier is
      //# not passed, then a default MUST be created that takes a region string
      //# and generates a default AWS SDK client for the given region.
      if input.clientSupplier == null {
        var clientSupplierOutput := CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
        clientSupplier := clientSupplierOutput.clientSupplier;
      } else {
        clientSupplier := input.clientSupplier;
      }
      res := DiscoveryMultiKeyring(
        input.regions,
        input.discoveryFilter,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
    //= type=implication
    //# The caller MUST provide:
    //#*  A set of Region strings
    //#*  An optional discovery filter that is an AWS partition and a set of
    //#   AWS accounts
    //#*  An optional method that can take a region string and return an AWS
    //#   KMS client e.g. a regional client supplier
    //#*  An optional list of AWS KMS grant tokens
    method DiscoveryMultiKeyring(
      regions: seq<string>,
      discoveryFilter: Option<Crypto.DiscoveryFilter>,
      clientSupplier: Crypto.IClientSupplier,
      grantTokens: Option<GeneratedKMS.GrantTokenList>
    )
      returns (
        res: Result<MultiKeyring.MultiKeyring, Crypto.IAwsCryptographicMaterialProvidersException>
      )

      ensures
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
        //= type=implication
        //# If an empty set of Region is provided this function MUST fail.
        || |regions| == 0
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
        //= type=implication
        //# If
        //# any element of the set of regions is null or an empty string this
        //# function MUST fail.
        || (exists r | r in regions :: r == "")
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
      //= type=implication
      //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
      //# by using this set of discovery keyrings as the child keyrings
      //# (../multi-keyring.md#child-keyrings).
      //# This Multi-Keyring MUST be
      //# this functions output.
      ensures
        && res.Success?
      ==>
        && res.value.generatorKeyring == null
        && |regions| == |res.value.childKeyrings|
        && forall i | 0 <= i < |regions|
        ::
          && var k: Crypto.IKeyring := res.value.childKeyrings[i];
          && k is AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
          && var c := k as AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring;
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
          //= type=implication
          //# Then a set of AWS KMS MRK Aware Symmetric Region Discovery Keyring
          //# (aws-kms-mrk-aware-symmetric-region-discovery-keyring.md) MUST be
          //# created for each AWS KMS client by initializing each keyring with
          //#*  The AWS KMS client
          //#*  The input discovery filter
          //#*  The input AWS KMS grant tokens
          && c.region == regions[i]
          && (discoveryFilter.Some? ==> c.discoveryFilter == discoveryFilter)
          && (grantTokens.Some? ==> c.grantTokens == grantTokens.value)
    {

      :- Crypto.Need(|regions| > 0, "No regions passed.");
      :- Crypto.Need(Seq.IndexOfOption(regions, "").None?, "Empty string is not a valid region.");

      var children : seq<AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring> := [];

      for i := 0 to |regions|
          invariant |regions[..i]| == |children|
          invariant forall i | 0 <= i < |children|
          ::
            && children[i].region == regions[i]
            && (discoveryFilter.Some? ==> children[i].discoveryFilter == discoveryFilter)
            && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
        {
          var region := regions[i];
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
          //# A set of AWS KMS clients MUST be created by calling regional client
          //# supplier for each region in the input set of regions.
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region));
          // :- Crypto.Need(
          //   AwsKmsUtils.RegionMatch(client, region),
          //   "The region for the client did not match the requested region"
          // );
          var keyring := new AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring(
            client,
            region,
            discoveryFilter,
            grantTokens.UnwrapOr([])
          );
          // Order is important
          children := children + [keyring];
        }

      var keyring := new MultiKeyring.MultiKeyring(
        null,
        children
      );

      return Success(keyring);
    }    

    method CreateDefaultClientSupplier(input: Crypto.CreateDefaultClientSupplierInput)
      returns (res: Crypto.CreateDefaultClientSupplierOutput)
    {
      var clientSupplier := new DefaultClientSupplier.DefaultClientSupplier();
      res := Crypto.CreateDefaultClientSupplierOutput(
        clientSupplier := clientSupplier
      );
    }
  }
}
