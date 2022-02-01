// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"

include "../../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../Generated/KeyManagementService.dfy"

include "AwsKmsMrkAwareSymmetricKeyring.dfy"
include "AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "../MultiKeyring.dfy"
include "../../Keyring.dfy"
include "AwsKmsArnParsing.dfy"

module
    {:extern "Dafny.Aws.Crypto.MaterialProviders.AwsKmsMrkAwareMultiKeyrings"}
    AwsKmsMrkAwareMultiKeyrings
 {
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsKmsArnParsing
  import opened A = MaterialProviders.AwsKmsMrkAwareSymmetricKeyring
  import opened D = MaterialProviders.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
  import opened U = AwsKmsMrkAreUnique
  import opened MaterialProviders.MultiKeyring
  import opened MaterialProviders.Keyring
  import KMS = Com.Amazonaws.Kms
  import Aws.Crypto

  //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
  //= type=implication
  //# The caller MUST provide:
  //#*  An optional AWS KMS key identifiers to use as the generator.
  //#*  An optional set of AWS KMS key identifiers to us as child
  //#   keyrings.
  //#*  An optional method that can take a region string and return an AWS
  //#   KMS client e.g. a regional client supplier
  //#*  An optional list of AWS KMS grant tokens
  method StrictMultiKeyring(
    generator: Option<string>,
    awsKmsKeys: Option<seq<string>>,
    clientSupplier: Option<Crypto.IClientSupplier>,
    grantTokens: Option<KMS.GrantTokenList>
  )
    returns (
      res: Result<MultiKeyring.MultiKeyring, string>
    )
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
      var allIdentifiers := Seq.MapWithResult(IsAwsKmsIdentifierString, allStrings);
      || allIdentifiers.Failure?
      || (allIdentifiers.Success? && AwsKmsMrkAreUnique(allIdentifiers.value).Fail?)
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
        && res.value.generatorKeyring is AwsKmsMrkAwareSymmetricKeyring
        && var g := res.value.generatorKeyring as AwsKmsMrkAwareSymmetricKeyring;
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
          && childKeyring is AwsKmsMrkAwareSymmetricKeyring
          && var awsKmsChild := childKeyring as AwsKmsMrkAwareSymmetricKeyring;
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

    var allIdentifiers :- Seq.MapWithResult(IsAwsKmsIdentifierString, allStrings);
    :- AwsKmsMrkAreUnique(allIdentifiers);

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
    //= type=implication
    //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
    //# default region.
    var supplier: Crypto.IClientSupplier;
    match clientSupplier {
      case Some(s) =>
        supplier := s;
      case None() =>
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
        //# If a regional client supplier is
        //# not passed, then a default MUST be created that takes a region string
        //# and generates a default AWS SDK client for the given region.
        supplier := null; //TODO replace with BaseClientSupplier from model
    }

    var generatorKeyring : AwsKmsMrkAwareSymmetricKeyring?;
    match generator {
      case Some(generatorIdentifier) =>
        var arn :- IsAwsKmsIdentifierString(generatorIdentifier);
        var region := GetRegion(arn);
        //Question: What should the behavior be if there is no region supplied?
        // I assume that the SDK will use the default region or throw an error
        var client := supplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
        :- Need(
          client != null,
          "Failed to initialize client"
        );
        generatorKeyring := new AwsKmsMrkAwareSymmetricKeyring(
          client,
          generatorIdentifier,
          grantTokens.UnwrapOr([])
        );
      case None() => generatorKeyring := null;
    }

    var children : seq<AwsKmsMrkAwareSymmetricKeyring> := [];

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
          var info :- IsAwsKmsIdentifierString(childIdentifier);
          var region := GetRegion(info);
          //Question: What should the behavior be if there is no region supplied?
          // I assume that the SDK will use the default region or throw an error
          var client := supplier.GetClient(Crypto.GetClientInput(region.UnwrapOr("")));
          :- Need(
            client != null,
            "Failed to initialize client"
          );
          var keyring := new AwsKmsMrkAwareSymmetricKeyring(
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

    :- Need(
      generatorKeyring != null || children != [],
      "generatorKeyring or child Keryings needed to create a multi keyring"
    );
    var keyring := new MultiKeyring.MultiKeyring(
      generatorKeyring,
      children
    );

    return Success(keyring);
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
    clientSupplier: Option<Crypto.IClientSupplier>,
    grantTokens: Option<KMS.GrantTokenList>
  )
    returns (
      res: Result<MultiKeyring.MultiKeyring, string>
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
        && k is AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
        && var c := k as AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring;
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

    :- Need(|regions| > 0, "No regions passed.");
    :- Need(Seq.IndexOfOption(regions, "").None?, "Empty string is not a valid region.");

    var supplier: Crypto.IClientSupplier;
    match clientSupplier {
      case Some(s) =>
        supplier := s;
      case None() =>
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.5
        //# If a regional client supplier is not passed,
        //# then a default MUST be created that takes a region string and
        //# generates a default AWS SDK client for the given region.
        supplier := null; //TODO replace with BaseClientSupplier from model
    }

    var children : seq<AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring> := [];

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
        var client := supplier.GetClient(Crypto.GetClientInput(region));
        :- Need(
          client != null,
          "Client failed to initialize"
        );
        :- Need(
          AwsKmsUtils.RegionMatch(client, region),
          "The region for the client did not match the requested region"
        );
        var keyring := new AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring(
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

}
