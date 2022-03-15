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
include "Keyrings/AwsKms/AwsKmsMrkKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsMrkDiscoveryKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsKeyring.dfy"
include "Keyrings/AwsKms/AwsKmsUtils.dfy"
include "Keyrings/MultiKeyring.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "Keyrings/RawRSAKeyring.dfy"
include "Materials.dfy"

module
  {:extern "Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProviders"}
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
  import AwsKmsMrkKeyring
  import AwsKmsMrkDiscoveryKeyring
  import AwsKmsKeyring
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
    reveals AwsCryptographicMaterialProviders
    // Functions
    reveals
      SpecificationClient,
      SpecificationClient.GetSuite
    provides
      SpecificationClient.ValidateCommitmentPolicyOnEncrypt,
      SpecificationClient.ValidateCommitmentPolicyOnDecrypt
    // Class Members
    provides
      AwsCryptographicMaterialProviders.CreateAwsKmsDiscoveryKeyring,
      AwsCryptographicMaterialProviders.CreateDefaultClientSupplier,
      AwsCryptographicMaterialProviders.CreateDefaultCryptographicMaterialsManager,
      AwsCryptographicMaterialProviders.CreateAwsKmsMrkDiscoveryKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsMrkKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsMrkMultiKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsMultiKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsDiscoveryMultiKeyring,
      AwsCryptographicMaterialProviders.CreateMultiKeyring,
      AwsCryptographicMaterialProviders.CreateRawAesKeyring,
      AwsCryptographicMaterialProviders.CreateRawRsaKeyring,
      AwsCryptographicMaterialProviders.CreateAwsKmsKeyring

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
    function method ValidateCommitmentPolicyOnEncrypt(
      algorithm: Crypto.AlgorithmSuiteId,
      commitmentPolicy: Crypto.CommitmentPolicy
    ): (res: Result<(), string>)
    {
      Commitment.ValidateCommitmentPolicyOnEncrypt(algorithm, commitmentPolicy)
    }

    function method ValidateCommitmentPolicyOnDecrypt(
      algorithm: Crypto.AlgorithmSuiteId,
      commitmentPolicy: Crypto.CommitmentPolicy
    ): (res: Result<(), string>)
    {
      Commitment.ValidateCommitmentPolicyOnDecrypt(algorithm, commitmentPolicy)
    }

  }

  class AwsCryptographicMaterialProviders
    extends Crypto.IAwsCryptographicMaterialProviders
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

      var namespaceAndName :- ParseKeyNamespaceAndName(input.keyNamespace, input.keyName);
      var (namespace, name) := namespaceAndName;

      :- Crypto.Need(|input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32,
        "Invalid wrapping key length");
      :- Crypto.Need(|input.wrappingKey| == wrappingAlg.keyLength as int,
        "Wrapping key length does not match specified wrapping algorithm");

      var keyring := new RawAESKeyring.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
      return Success(keyring);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput)
      returns (res: Result<Crypto.ICryptographicMaterialsManager, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
        var cmm := new DefaultCMM.DefaultCMM.OfKeyring(input.keyring);
        return Success(cmm);
    }

    method CreateAwsKmsKeyring(input: Crypto.CreateAwsKmsKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var _ :- ValidateKmsKeyId(input.kmsKeyId);
      var grantTokens :- GetValidGrantTokens(input.grantTokens);
      var keyring := new AwsKmsKeyring.AwsKmsKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
      return Success(keyring);
    }

    method CreateAwsKmsMrkKeyring(input: Crypto.CreateAwsKmsMrkKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var _ :- ValidateKmsKeyId(input.kmsKeyId);
      var grantTokens :- GetValidGrantTokens(input.grantTokens);
      var keyring := new AwsKmsMrkKeyring.AwsKmsMrkKeyring(input.kmsClient, input.kmsKeyId, grantTokens);
      return Success(keyring);
    }

    method CreateAwsKmsMrkDiscoveryKeyring(input: Crypto.CreateAwsKmsMrkDiscoveryKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      if input.discoveryFilter.Some? {
        var _ :- ValidateDiscoveryFilter(input.discoveryFilter.value);
      }

      //= compliance/framework/aws-kms/aws-kms-mrk-discovery-keyring.txt#2.6
      //= type=implication
      //# The keyring SHOULD fail initialization if the
      //# provided region does not match the region of the KMS client.
      var regionMatch := AwsKmsUtils.RegionMatch(input.kmsClient, input.region);
      :- Crypto.Need(regionMatch != Some(false), "Provided client and region do not match");

      var grantTokens :- GetValidGrantTokens(input.grantTokens);
      var keyring := new AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring(input.kmsClient, input.region, input.discoveryFilter, grantTokens);
      return Success(keyring);
    }

    method CreateAwsKmsDiscoveryKeyring(input: Crypto.CreateAwsKmsDiscoveryKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      if input.discoveryFilter.Some? {
        var _ :- ValidateDiscoveryFilter(input.discoveryFilter.value);
      }
      var grantTokens :- GetValidGrantTokens(input.grantTokens);
      var keyring := new AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring(input.kmsClient, input.discoveryFilter, grantTokens);
      return Success(keyring);
    }


    method CreateMultiKeyring(input: Crypto.CreateMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      if input.generator.None? && |input.childKeyrings| == 0 {
        var error := new Crypto.AwsCryptographicMaterialProvidersException(
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
      :- Crypto.Need(input.keyNamespace != "aws-kms",
          "keyNamespace must not be `aws-kms`");
      :- Crypto.Need(input.publicKey.Some? || input.privateKey.Some?,
          "A publicKey or a privateKey is required");

      var padding: RSAEncryption.PaddingMode := match input.paddingScheme
        case PKCS1 => RSAEncryption.PaddingMode.PKCS1
        case OAEP_SHA1_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA1
        case OAEP_SHA256_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA256
        case OAEP_SHA384_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA384
        case OAEP_SHA512_MGF1 => RSAEncryption.PaddingMode.OAEP_SHA512
      ;

      var namespaceAndName :- ParseKeyNamespaceAndName(input.keyNamespace, input.keyName);
      var (namespace, name) := namespaceAndName;

      var keyring := new RawRSAKeyring.RawRSAKeyring(namespace, name, input.publicKey, input.privateKey, padding);
      return Success(keyring);
    }

    method CreateAwsKmsMrkMultiKeyring(input: Crypto.CreateAwsKmsMrkMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens :- GetValidGrantTokens(input.grantTokens);

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
      //# If a regional client supplier is
      //# not passed, then a default MUST be created that takes a region string
      //# and generates a default AWS SDK client for the given region.
      if input.clientSupplier.None? {
        clientSupplier :- CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
      } else {
        clientSupplier := input.clientSupplier.value;
      }
      res := MrkAwareStrictMultiKeyring(
        input.generator,
        input.kmsKeyIds,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }

    method MrkAwareStrictMultiKeyring(
      generator: Option<string>,
      awsKmsKeys: Option<seq<string>>,
      clientSupplier: Crypto.IClientSupplier,
      grantTokens: Option<GeneratedKMS.GrantTokenList>
    )
      returns (res: Result<MultiKeyring.MultiKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
      //= type=implication
      //# If any of the AWS KMS key identifiers is not a valid AWS KMS key ARN
      //# (aws-kms-key-arn.md#a-valid-aws-kms-arn), this function MUST fail All
      //# AWS KMS identifiers are passed to Assert AWS KMS MRK are unique (aws-
      //# kms-mrk-are-unique.md#Implementation) and the function MUST return
      //# success otherwise this MUST fail.
      ensures
        || (generator.Some? && generator.value == "")
        || (awsKmsKeys.Some? && (exists k | k in awsKmsKeys.value :: k == ""))
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
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

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
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
        //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
        //= type=implication
        //# If there is a generator input then the generator keyring MUST be a
        //# AWS KMS MRK Keyring (aws-kms-mrk-keyring.md) initialized with
        && (generator.Some?
        ==>
          && res.value.generatorKeyring.Some?
          && res.value.generatorKeyring.value is AwsKmsMrkKeyring.AwsKmsMrkKeyring
          && var g := res.value.generatorKeyring.value as AwsKmsMrkKeyring.AwsKmsMrkKeyring;
          && g.awsKmsKey == generator.value
          && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
        && (generator.None?
        ==>
          && res.value.generatorKeyring.None?)
        //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
        //= type=implication
        //# If there is a set of child identifiers then a set of AWS KMS MRK
        //# Keyring (aws-kms-mrk-keyring.md) MUST be created for each AWS KMS key
        //# identifier by initialized each keyring with
        && (awsKmsKeys.Some?
        ==>
          && |awsKmsKeys.value| == |res.value.childKeyrings|
          && forall index | 0 <= index < |awsKmsKeys.value| ::
            // AWS KMS MRK Aware Symmetric Keying must be created for each AWS KMS Key identifier
            && var childKeyring: Crypto.IKeyring := res.value.childKeyrings[index];
            && childKeyring is AwsKmsMrkKeyring.AwsKmsMrkKeyring
            && var awsKmsChild := childKeyring as AwsKmsMrkKeyring.AwsKmsMrkKeyring;
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
      var allIdentifiers :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
        allIdentifiersResults
      );
      var mrkAreUniqueRes := AwsKmsMrkAreUnique.AwsKmsMrkAreUnique(allIdentifiers);
      :- Crypto.AwsCryptographicMaterialProvidersException.WrapOutcomeString(
        mrkAreUniqueRes
      );

      var generatorKeyring : Option<AwsKmsMrkKeyring.AwsKmsMrkKeyring>;
      match generator {
        case Some(generatorIdentifier) =>
          var arnRes := AwsKmsArnParsing.IsAwsKmsIdentifierString(generatorIdentifier);
          var arn :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
            arnRes
          );
          var region := AwsKmsArnParsing.GetRegion(arn);
          //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.5
          //= type=implication
          //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
          //# default region.
          //Question: What should the behavior be if there is no region supplied?
          // I assume that the SDK will use the default region or throw an error
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
          var g := new AwsKmsMrkKeyring.AwsKmsMrkKeyring(
            client,
            generatorIdentifier,
            grantTokens.UnwrapOr([])
          );
          generatorKeyring := Some(g);
        case None() => generatorKeyring := None();
      }

      var children : seq<AwsKmsMrkKeyring.AwsKmsMrkKeyring> := [];

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
            var info :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
              infoRes
            );
            var region := AwsKmsArnParsing.GetRegion(info);
            //Question: What should the behavior be if there is no region supplied?
            // I assume that the SDK will use the default region or throw an error
            var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
            var keyring := new AwsKmsMrkKeyring.AwsKmsMrkKeyring(
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
        generatorKeyring.Some? || |children| > 0,
        "generatorKeyring or child Keyrings needed to create a multi keyring"
      );
      var keyring := new MultiKeyring.MultiKeyring(
        generatorKeyring,
        children
      );

      return Success(keyring);
    }

    method CreateAwsKmsMrkDiscoveryMultiKeyring(input: Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens :- GetValidGrantTokens(input.grantTokens);

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
      //# If a regional client supplier is not passed,
      //# then a default MUST be created that takes a region string and
      //# generates a default AWS SDK client for the given region.
      if input.clientSupplier.None? {
        clientSupplier :- CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
      } else {
        clientSupplier := input.clientSupplier.value;
      }
      res := MrkAwareDiscoveryMultiKeyring(
        input.regions,
        input.discoveryFilter,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }

    //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
    //= type=implication
    //# The caller MUST provide:
    //#*  A set of Region strings
    //#*  An optional discovery filter that is an AWS partition and a set of
    //#   AWS accounts
    //#*  An optional method that can take a region string and return an AWS
    //#   KMS client e.g. a regional client supplier
    //#*  An optional list of AWS KMS grant tokens
    method MrkAwareDiscoveryMultiKeyring(
      regions: seq<string>,
      discoveryFilter: Option<Crypto.DiscoveryFilter>,
      clientSupplier: Crypto.IClientSupplier,
      grantTokens: Option<GeneratedKMS.GrantTokenList>
    )
      returns (
        res: Result<MultiKeyring.MultiKeyring, Crypto.IAwsCryptographicMaterialProvidersException>
      )

      ensures
        //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
        //= type=implication
        //# If an empty set of Region is provided this function MUST fail.
        || |regions| == 0
        //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
        //= type=implication
        //# If
        //# any element of the set of regions is null or an empty string this
        //# function MUST fail.
        || (exists r | r in regions :: r == "")
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
      //= type=implication
      //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
      //# by using this set of discovery keyrings as the child keyrings
      //# (../multi-keyring.md#child-keyrings).
      //# This Multi-Keyring MUST be
      //# this functions output.
      ensures
        && res.Success?
      ==>
        && res.value.generatorKeyring.None?
        && |regions| == |res.value.childKeyrings|
        && forall i | 0 <= i < |regions|
        ::
          && var k: Crypto.IKeyring := res.value.childKeyrings[i];
          && k is AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring
          && var c := k as AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring;
          //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
          //= type=implication
          //# Then a set of AWS KMS MRK Discovery Keyring (aws-kms-mrk-discovery-
          //# keyring.md) MUST be created for each AWS KMS client by initializing
          //# each keyring with
          //#*  The AWS KMS client
          //#*  The input discovery filter
          //#*  The input AWS KMS grant tokens
          && c.region == regions[i]
          && (discoveryFilter.Some? ==> c.discoveryFilter == discoveryFilter)
          && (grantTokens.Some? ==> c.grantTokens == grantTokens.value)
    {
      :- Crypto.Need(|regions| > 0, "No regions passed.");
      :- Crypto.Need(Seq.IndexOfOption(regions, "").None?, "Empty string is not a valid region.");

      var children : seq<AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring> := [];

      for i := 0 to |regions|
          invariant |regions[..i]| == |children|
          invariant forall i | 0 <= i < |children|
          ::
            && children[i].region == regions[i]
            && (discoveryFilter.Some? ==> children[i].discoveryFilter == discoveryFilter)
            && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
        {
          var region := regions[i];
          //= compliance/framework/aws-kms/aws-kms-mrk-multi-keyrings.txt#2.6
          //# A set of AWS KMS clients MUST be created by calling regional client
          //# supplier for each region in the input set of regions.
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region));
          // :- Crypto.Need(
          //   AwsKmsUtils.RegionMatch(client, region),
          //   "The region for the client did not match the requested region"
          // );
          var keyring := new AwsKmsMrkDiscoveryKeyring.AwsKmsMrkDiscoveryKeyring(
            client,
            region,
            discoveryFilter,
            grantTokens.UnwrapOr([])
          );
          // Order is important
          children := children + [keyring];
        }

      var keyring := new MultiKeyring.MultiKeyring(
        None(),
        children
      );

      return Success(keyring);
    }

    method CreateAwsKmsMultiKeyring(input: Crypto.CreateAwsKmsMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens :- GetValidGrantTokens(input.grantTokens);

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //# If a regional client supplier is not passed, then a default MUST be
      //# created that takes a region string and generates a default AWS SDK
      //# client for the given region.
      if input.clientSupplier.None? {
        clientSupplier :- CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
      } else {
        clientSupplier := input.clientSupplier.value;
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

      ensures
        || (generator.Some? && generator.value == "")
        || (awsKmsKeys.Some? && (exists k | k in awsKmsKeys.value :: k == ""))
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //= type=implication
      //# If any of the AWS KMS key identifiers is not a valid AWS KMS key ARN
      //# (aws-kms-key-arn.md#a-valid-aws-kms-arn), this function MUST fail.
      ensures
        var allStrings := if generator.Some? then
          [generator.value] + awsKmsKeys.UnwrapOr([])
        else
          awsKmsKeys.UnwrapOr([]);
        var allIdentifiers := Seq.MapWithResult(AwsKmsArnParsing.IsAwsKmsIdentifierString, allStrings);
        && allIdentifiers.Failure?
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //= type=implication
      //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
      //# by using this generator keyring as the generator keyring (../multi-
      //# keyring.md#generator-keyring) and this set of child keyrings as the
      //# child keyrings (../multi-keyring.md#child-keyrings).

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //= type=implication
      //# This Multi-
      //# Keyring MUST be this function's output.
      ensures
        && res.Success?
      ==>
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
        //= type=implication
        //# If there is a generator input then the generator keyring MUST be a
        //# AWS KMS Keyring (aws-kms-keyring.md) initialized with
        && (generator.Some?
        ==>
          && res.value.generatorKeyring.Some?
          && res.value.generatorKeyring.value is AwsKmsKeyring.AwsKmsKeyring
          && var g := res.value.generatorKeyring.value as AwsKmsKeyring.AwsKmsKeyring;
          && g.awsKmsKey == generator.value
          && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
        && (generator.None?
        ==>
          && res.value.generatorKeyring.None?)
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
        //= type=implication
        //# If there is a set of child identifiers then a set of AWS KMS Keyring
        //# (aws-kms-keyring.md) MUST be created for each AWS KMS key identifier
        //# by initializing each keyring with
        && (awsKmsKeys.Some?
        ==>
          && |awsKmsKeys.value| == |res.value.childKeyrings|
          && forall index | 0 <= index < |awsKmsKeys.value| ::
            // AWS KMS Keyring must be created for each AWS KMS Key identifier
            && var childKeyring: Crypto.IKeyring := res.value.childKeyrings[index];
            && childKeyring is AwsKmsKeyring.AwsKmsKeyring
            && var awsKmsChild := childKeyring as AwsKmsKeyring.AwsKmsKeyring;
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
      var allIdentifiers :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
        allIdentifiersResults
      );

      var generatorKeyring : Option<AwsKmsKeyring.AwsKmsKeyring>;
      match generator {
        case Some(generatorIdentifier) =>
          var arnRes := AwsKmsArnParsing.IsAwsKmsIdentifierString(generatorIdentifier);
          var arn :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
            arnRes
          );
          var region := AwsKmsArnParsing.GetRegion(arn);
          //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
          //= type=implication
          //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
          //# default region.
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
          var g := new AwsKmsKeyring.AwsKmsKeyring(
            client,
            generatorIdentifier,
            grantTokens.UnwrapOr([])
          );
          generatorKeyring := Some(g);
        case None() => generatorKeyring := None();
      }

      var children : seq<AwsKmsKeyring.AwsKmsKeyring> := [];

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
            var info :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
              infoRes
            );
            var region := AwsKmsArnParsing.GetRegion(info);
            //Question: What should the behavior be if there is no region supplied?
            // I assume that the SDK will use the default region or throw an error
            var client :- clientSupplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
            var keyring := new AwsKmsKeyring.AwsKmsKeyring(
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
        generatorKeyring.Some? || |children| > 0,
        "generatorKeyring or child Keryings needed to create a multi keyring"
      );
      var keyring := new MultiKeyring.MultiKeyring(
        generatorKeyring,
        children
      );

      return Success(keyring);
    }

    method CreateAwsKmsDiscoveryMultiKeyring(input: Crypto.CreateAwsKmsDiscoveryMultiKeyringInput)
      returns (res: Result<Crypto.IKeyring, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var grantTokens :- GetValidGrantTokens(input.grantTokens);

      var clientSupplier: Crypto.IClientSupplier;

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
      //# If a regional client supplier is not passed,
      //# then a default MUST be created that takes a region string and
      //# generates a default AWS SDK client for the given region.
      if input.clientSupplier.None? {
        clientSupplier :- CreateDefaultClientSupplier(Crypto.CreateDefaultClientSupplierInput());
      } else {
        clientSupplier := input.clientSupplier.value;
      }
      res := DiscoveryMultiKeyring(
        input.regions,
        input.discoveryFilter,
        clientSupplier,
        Option.Some(grantTokens)
      );
    }

    //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
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
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
        //= type=implication
        //# If an empty set of Region is provided this function MUST fail.
        || |regions| == 0
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
        //= type=implication
        //# If
        //# any element of the set of regions is null or an empty string this
        //# function MUST fail.
        || (exists r | r in regions :: r == "")
      ==>
        res.Failure?

      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
      //= type=implication
      //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
      //# by using this set of discovery keyrings as the child keyrings
      //# (../multi-keyring.md#child-keyrings).
      //# This Multi-Keyring MUST be
      //# this functions output.
      ensures
        && res.Success?
      ==>
        && res.value.generatorKeyring.None?
        && |regions| == |res.value.childKeyrings|
        && forall i | 0 <= i < |regions|
        ::
          && var k: Crypto.IKeyring := res.value.childKeyrings[i];
          && k is AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring
          && var c := k as AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring;
          //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
          //= type=implication
          //# Then a set of AWS KMS Discovery Keyring (aws-kms-discovery-
          //# keyring.md) MUST be created for each AWS KMS client by initializing
          //# each keyring with
          //#*  The AWS KMS client
          //#*  The input discovery filter
          //#*  The input AWS KMS grant tokens
          && (discoveryFilter.Some? ==> c.discoveryFilter == discoveryFilter)
          && (grantTokens.Some? ==> c.grantTokens == grantTokens.value)
    {

      :- Crypto.Need(|regions| > 0, "No regions passed.");
      :- Crypto.Need(Seq.IndexOfOption(regions, "").None?, "Empty string is not a valid region.");

      var children : seq<AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring> := [];

      for i := 0 to |regions|
          invariant |regions[..i]| == |children|
          invariant forall i | 0 <= i < |children|
          ::
            && (discoveryFilter.Some? ==> children[i].discoveryFilter == discoveryFilter)
            && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
        {
          var region := regions[i];
          //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
          //# A set of AWS KMS clients MUST be created by calling regional client
          //# supplier for each region in the input set of regions.
          var client :- clientSupplier.GetClient(Crypto.GetClientInput(region));
          // :- Crypto.Need(
          //   AwsKmsUtils.RegionMatch(client, region),
          //   "The region for the client did not match the requested region"
          // );
          var keyring := new AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring(
            client,
            discoveryFilter,
            grantTokens.UnwrapOr([])
          );
          // Order is important
          children := children + [keyring];
        }

      var keyring := new MultiKeyring.MultiKeyring(
        None(),
        children
      );

      return Success(keyring);
    }

    method CreateDefaultClientSupplier(input: Crypto.CreateDefaultClientSupplierInput)
      returns (res: Result<Crypto.IClientSupplier, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
      var clientSupplier := new DefaultClientSupplier.DefaultClientSupplier();
      return Success(clientSupplier);
    }
  }

  method ValidateKmsKeyId(keyId: string)
    returns (res: Result<(), Crypto.IAwsCryptographicMaterialProvidersException>)
    ensures res.Success? ==>
      && AwsKmsArnParsing.ParseAwsKmsIdentifier(keyId).Success?
      && UTF8.IsASCIIString(keyId)
      && 0 < |keyId| <= AwsKmsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH
  {
    var _ :- Crypto.AwsCryptographicMaterialProvidersException.WrapResultString(
      AwsKmsArnParsing.ParseAwsKmsIdentifier(keyId));
    :- Crypto.Need(UTF8.IsASCIIString(keyId), "Key identifier is not ASCII");
    :- Crypto.Need(0 < |keyId| <= AwsKmsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH, "Key identifier is too long");
  }

  method GetValidGrantTokens(grantTokens: Option<Crypto.GrantTokenList>)
    returns (res: Result<Crypto.GrantTokenList, Crypto.IAwsCryptographicMaterialProvidersException>)
    ensures res.Success? ==>
      var tokens := res.value;
      && 0 <= |tokens| <= 10
      && forall token | token in tokens :: 1 <= |token| <= 8192
    ensures res.Success? && grantTokens.Some? ==> res.value == grantTokens.value
  {
    var tokens: Crypto.GrantTokenList := grantTokens.UnwrapOr([]);
    :- Crypto.Need(0 <= |tokens| <= 10, "Grant token list can have no more than 10 tokens");
    :- Crypto.Need(forall token | token in tokens :: 1 <= |token| <= 8192,
      "Grant token list contains a grant token with invalid length");
    return Success(tokens);
  }

  method ParseKeyNamespaceAndName(keyNamespace: string, keyName: string)
    returns (res: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), Crypto.IAwsCryptographicMaterialProvidersException>)
    ensures res.Success? ==>
      var (namespace, name) := res.value;
      && |namespace| < UINT16_LIMIT
      && |name| < UINT16_LIMIT
  {
    var namespaceRes := UTF8.Encode(keyNamespace);
    :- Crypto.Need(namespaceRes.Success?, "Key namespace could not be UTF8-encoded");
    var namespace := namespaceRes.value;
    :- Crypto.Need(|namespace| < UINT16_LIMIT, "Key namespace too long");

    var nameRes := UTF8.Encode(keyName);
    :- Crypto.Need(nameRes.Success?, "Key name could not be UTF8-encoded");
    var name := nameRes.value;
    :- Crypto.Need(|name| < UINT16_LIMIT, "Key name too long");

    return Success((namespace, name));
  }

  method ValidateDiscoveryFilter(filter: Crypto.DiscoveryFilter)
    returns (res: Result<(), Crypto.IAwsCryptographicMaterialProvidersException>)
    ensures res.Success? ==>
      && |filter.accountIds| > 0
      && (forall accountId | accountId in filter.accountIds :: |accountId| > 0)
      && |filter.partition| > 0
  {
    :- Crypto.Need(|filter.accountIds| > 0, "Discovery filter must have at least one account ID");
    :- Crypto.Need(forall accountId | accountId in filter.accountIds :: |accountId| > 0,
      "Discovery filter account IDs cannot be blank");
    :- Crypto.Need(|filter.partition| > 0, "Discovery filter partition cannot be blank");
    return Success(());
  }
}
