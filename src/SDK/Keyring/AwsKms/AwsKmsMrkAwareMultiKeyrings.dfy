// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "AwsKmsMrkAwareSymmetricKeyring.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "../MultiKeyring.dfy"
include "../Defs.dfy"

module {:extern "AwsKmsMrkAwareMultiKeyrings"} AwsKmsMrkAwareMultiKeyrings {
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened A = AwsKmsMrkAwareSymmetricKeyring
  import opened U = AwsKmsMrkAreUnique
  import opened MultiKeyringDef
  import opened KMSUtils
  import opened KeyringDefs

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
    clientSupplier: Option<KMSUtils.DafnyAWSKMSClientSupplier>,
    grantTokens: Option<KMSUtils.GrantTokens>
  )
    returns (
      res: Result<MultiKeyring, string>
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
        && res.value.generator is AwsKmsMrkAwareSymmetricKeyring
        && var g := res.value.generator as AwsKmsMrkAwareSymmetricKeyring;
        && g.awsKmsKey == generator.value
        && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
      && (generator.None?
      ==>
        && res.value.generator == null)
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
      //= type=implication
      //# If there is a set of child identifiers then a set of AWS KMS MRK
      //# Aware Symmetric Keyring (aws-kms-mrk-aware-symmetric-keyring.md) MUST
      //# be created for each AWS KMS key identifier by initialized each
      //# keyring with
      && (awsKmsKeys.Some?
      ==>
        && |awsKmsKeys.value| == |res.value.children|
        && forall i | 0 <= i < |awsKmsKeys.value| ::
          // AWS KMS MRK Aware Symmetric Keying must be created for each AWS KMS Key identifier
          && var k: Keyring := res.value.children[i];
          && k is AwsKmsMrkAwareSymmetricKeyring
          && var c := k as AwsKmsMrkAwareSymmetricKeyring;
          // AWS KMS key identifier
          && c.awsKmsKey == awsKmsKeys.value[i]
          // The input list of AWS KMS grant tokens
          && (grantTokens.Some? ==> c.grantTokens == grantTokens.value))
      && (awsKmsKeys.None?
      ==>
        && res.value.children == [])
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
    var supplier: KMSUtils.DafnyAWSKMSClientSupplier;
    match clientSupplier {
      case Some(s) =>
        supplier := s;
      case None() =>
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-multi-keyrings.txt#2.6
        //# If a regional client supplier is
        //# not passed, then a default MUST be created that takes a region string
        //# and generates a default AWS SDK client for the given region.
        supplier := new KMSUtils.BaseClientSupplier();
    }

    var generatorKeyring : AwsKmsMrkAwareSymmetricKeyring?;
    match generator {
      case Some(generatorIdentifier) =>
        var info :- IsAwsKmsIdentifierString(generatorIdentifier);
        var region := GetRegion(info);
        var client :- supplier.GetClient(region);
        generatorKeyring := new AwsKmsMrkAwareSymmetricKeyring(
          client,
          generatorIdentifier,
          grantTokens.UnwrapOr([])
        );
        assert generatorKeyring.Valid();
      case None() => generatorKeyring := null;
    }

    var children : seq<AwsKmsMrkAwareSymmetricKeyring> := [];

    match awsKmsKeys {
      case Some(childIdentifiers) =>
        for i := 0 to |childIdentifiers|
          invariant generatorKeyring != null ==> generatorKeyring.Valid()
          invariant forall k :: k in children ==> k.Valid()
          invariant |awsKmsKeys.value[..i]| == |children|
          invariant forall i | 0 <= i < |children|
          ::
            && children[i].awsKmsKey == awsKmsKeys.value[i]
            && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
        {
          var childIdentifier := childIdentifiers[i];
          var info :- IsAwsKmsIdentifierString(childIdentifier);
          var region := GetRegion(info);
          var client :- supplier.GetClient(region);
          var keyring := new AwsKmsMrkAwareSymmetricKeyring(
            client,
            childIdentifier,
            grantTokens.UnwrapOr([])
          );
          assert keyring.Valid();
          // Order is important
          children := children + [keyring];
        }
      case None() =>
        assert generatorKeyring != null ==> generatorKeyring.Valid();
        children := [];
    }

    var keyring := new MultiKeyring(
      generatorKeyring,
      children
    );

    return Success(keyring);
  }

  predicate ChildKeyringCorrect(
    c: AwsKmsMrkAwareSymmetricKeyring,
    awsKmsKeys: seq<string>,
    grantTokens: Option<KMSUtils.GrantTokens>
  ) {
    && c.awsKmsKey in awsKmsKeys
    && (grantTokens.Some? ==> c.grantTokens == grantTokens.value)
  }

}
