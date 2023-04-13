// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../MultiKeyring.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "AwsKmsMrkKeyring.dfy"
include "AwsKmsUtils.dfy"
include "../../AlgorithmSuites.dfy"

module MrkAwareStrictMultiKeyring {
  import opened Wrappers
  import Seq
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = Types.ComAmazonawsKmsTypes
  import MultiKeyring
  import AwsArnParsing
  import AwsKmsMrkAreUnique
  import AwsKmsMrkKeyring
  import opened AwsKmsUtils

  method {:vcs_split_on_every_assert} MrkAwareStrictMultiKeyring(
    generator: Option<string>,
    awsKmsKeys: Option<seq<string>>,
    clientSupplier: Types.IClientSupplier,
    grantTokens: Option<KMS.GrantTokenList>
  )
    returns (output: Result<MultiKeyring.MultiKeyring, Types.Error>)
    requires clientSupplier.ValidState()
    modifies clientSupplier.Modifies
    ensures output.Success? ==>
    && output.value.ValidState()
    && fresh(output.value)
    && fresh(output.value.History)
    && fresh(output.value.Modifies - clientSupplier.Modifies)

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
    //= type=implication
    //# If any of the AWS KMS key identifiers is not a [valid AWS KMS key ARN]
    //# (aws-kms-key-arn.md#a-valid-aws-kms-arn), this function MUST fail All
    //# AWS KMS identifiers are passed to [Assert AWS KMS MRK are unique](aws-
    //# kms-mrk-are-unique.md#Implementation) and the function MUST return
    //# success otherwise this MUST fail.
    ensures
      || (generator.Some? && generator.value == "")
      || (awsKmsKeys.Some? && (exists k | k in awsKmsKeys.value :: k == ""))
    ==>
      output.Failure?

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
    //= type=implication
    //# All
    //# AWS KMS identifiers are passed to [Assert AWS KMS MRK are unique](aws-
    //# kms-mrk-are-unique.md#Implementation) and the function MUST return
    //# success otherwise this MUST fail.
    ensures
      var allStrings := if generator.Some? then
        [generator.value] + awsKmsKeys.UnwrapOr([])
      else
        awsKmsKeys.UnwrapOr([]);
      var allIdentifiers := Seq.MapWithResult(AwsArnParsing.IsAwsKmsIdentifierString, allStrings);
      || allIdentifiers.Failure?
      || (allIdentifiers.Success? && AwsKmsMrkAreUnique.AwsKmsMrkAreUnique(allIdentifiers.value).Fail?)
    ==>
      output.Failure?

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
    //= type=implication
    //# Then a [Multi-Keyring](../multi-keyring.md#inputs) MUST be initialize
    //# by using this generator keyring as the [generator keyring](../multi-
    //# keyring.md#generator-keyring) and this set of child keyrings as the
    //# [child keyrings](../multi-keyring.md#child-keyrings).
    //# This Multi-
    //# Keyring MUST be this functions output.
    ensures
      && output.Success?
    ==>
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
      //= type=implication
      //# If there is a generator input then the generator keyring MUST be a
      //# [AWS KMS MRK Keyring](aws-kms-mrk-keyring.md) initialized with
      && (generator.Some?
      ==>
        && output.value.generatorKeyring.Some?
        && output.value.generatorKeyring.value is AwsKmsMrkKeyring.AwsKmsMrkKeyring
        && var g := output.value.generatorKeyring.value as AwsKmsMrkKeyring.AwsKmsMrkKeyring;
        && g.awsKmsKey == generator.value
        && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
      && (generator.None?
      ==>
        && output.value.generatorKeyring.None?)
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
      //= type=implication
      //# If there is a set of child identifiers then a set of [AWS KMS MRK
      //# Keyring](aws-kms-mrk-keyring.md) MUST be created for each AWS KMS key
      //# identifier by initialized each keyring with
      && (awsKmsKeys.Some?
      ==>
        && |awsKmsKeys.value| == |output.value.childKeyrings|
        && forall index | 0 <= index < |awsKmsKeys.value| ::
          // AWS KMS MRK Aware Symmetric Keying must be created for each AWS KMS Key identifier
          && var childKeyring: Types.IKeyring := output.value.childKeyrings[index];
          && childKeyring is AwsKmsMrkKeyring.AwsKmsMrkKeyring
          && var awsKmsChild := childKeyring as AwsKmsMrkKeyring.AwsKmsMrkKeyring;
          // AWS KMS key identifier
          && awsKmsChild.awsKmsKey == awsKmsKeys.value[index]
          // The input list of AWS KMS grant tokens
          && (grantTokens.Some? ==> awsKmsChild.grantTokens == grantTokens.value))
      && (awsKmsKeys.None?
      ==>
        && output.value.childKeyrings == [])
  {
    var allStrings := match (generator) {
      case Some(g) => [g] + awsKmsKeys.UnwrapOr([])
      case None => awsKmsKeys.UnwrapOr([])
    };
    assert generator.Some? ==> generator.value in allStrings;
    assert awsKmsKeys.Some? ==> forall k | k in awsKmsKeys.value :: k in allStrings;

    var allIdentifiers :- Seq.MapWithResult(
      AwsArnParsing.IsAwsKmsIdentifierString,
      allStrings
    ).MapFailure(WrapStringToError);
    :- AwsKmsMrkAreUnique.AwsKmsMrkAreUnique(allIdentifiers);

    var generatorKeyring : Option<AwsKmsMrkKeyring.AwsKmsMrkKeyring>;
    match generator {
      case Some(generatorIdentifier) =>
        var arn :- AwsArnParsing.IsAwsKmsIdentifierString(generatorIdentifier).MapFailure(WrapStringToError);
        var region := AwsArnParsing.GetRegion(arn);
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-multi-keyrings.md#aws-kms-mrk-multi-keyring
        //= type=implication
        //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
        //# default region.
        //Question: What should the behavior be if there is no region supplied?
        // I assume that the SDK will use the default region or throw an error
        var client :- clientSupplier.GetClient(Types.GetClientInput( region := region.UnwrapOr("")));
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
          invariant fresh(MultiKeyring.GatherModifies(generatorKeyring, children) - clientSupplier.Modifies)
          invariant forall i | 0 <= i < |children|
          :: ChildLoopInvariant(children[i],  awsKmsKeys.value[i], grantTokens)
        {
          var childIdentifier := childIdentifiers[index];
          var info :- AwsArnParsing.IsAwsKmsIdentifierString(childIdentifier).MapFailure(WrapStringToError);
          var region := AwsArnParsing.GetRegion(info);
          //Question: What should the behavior be if there is no region supplied?
          // I assume that the SDK will use the default region or throw an error
          var client :- clientSupplier.GetClient(Types.GetClientInput(region := region.UnwrapOr("")));
          var keyring := new AwsKmsMrkKeyring.AwsKmsMrkKeyring(
            client,
            childIdentifier,
            grantTokens.UnwrapOr([])
          );

          // Order is important
          children := children + [keyring];

          // Dafny needs a little help because we modify the `children` seq.
          assert forall i | 0 <= i < |children|
          :: ChildLoopInvariant(children[i],  awsKmsKeys.value[i], grantTokens) by {
            // Clearly everything holds for all children _before_ this one
            assert forall i | 0 <= i < |children| - 1
            :: ChildLoopInvariant(children[i],  awsKmsKeys.value[i], grantTokens);
            // The invariant holds for this last keyring
            assert ChildLoopInvariant(keyring, awsKmsKeys.value[index], grantTokens);
            // The last child is this last keyring
            assert children[|children| - 1 ] == keyring;
          }
        }
      case None() =>
        children := [];
    }

    :- Need(
      generatorKeyring.Some? || |children| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "generatorKeyring or child Keyrings needed to create a multi keyring")
    );
    var keyring := new MultiKeyring.MultiKeyring(
      generatorKeyring,
      children
    );

    return Success(keyring);
  }

  predicate ChildLoopInvariant(
    child: AwsKmsMrkKeyring.AwsKmsMrkKeyring,
    awsKmsKey: string,
    grantTokens: Option<KMS.GrantTokenList>
  )
  {
    && child.awsKmsKey == awsKmsKey
    && (grantTokens.Some? ==> child.grantTokens == grantTokens.value)
    && child.ValidState()
  }
}
