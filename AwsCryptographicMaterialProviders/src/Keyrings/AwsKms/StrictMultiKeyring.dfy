// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../MultiKeyring.dfy"
include "AwsKmsArnParsing.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "AwsKmsKeyring.dfy"
include "AwsKmsUtils.dfy"
include "../../AlgorithmSuites.dfy"

module StrictMultiKeyring {
  import opened Wrappers
  import Seq
  import Types = AwsCryptographyMaterialProvidersTypes 
  import KMS = Types.ComAmazonawsKmsTypes
  import MultiKeyring
  import AwsKmsArnParsing
  import AwsKmsMrkAreUnique
  import AwsKmsKeyring
  import opened AwsKmsUtils

  method StrictMultiKeyring(
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

    ensures
      || (generator.Some? && generator.value == "")
      || (awsKmsKeys.Some? && (exists k | k in awsKmsKeys.value :: k == ""))
    ==>
      output.Failure?

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
      output.Failure?

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
      && output.Success?
    ==>
      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //= type=implication
      //# If there is a generator input then the generator keyring MUST be a
      //# AWS KMS Keyring (aws-kms-keyring.md) initialized with
      && (generator.Some?
      ==>
        && output.value.generatorKeyring.Some?
        && output.value.generatorKeyring.value is AwsKmsKeyring.AwsKmsKeyring
        && var g := output.value.generatorKeyring.value as AwsKmsKeyring.AwsKmsKeyring;
        && g.awsKmsKey == generator.value
        && (grantTokens.Some? ==> g.grantTokens == grantTokens.value))
      && (generator.None?
      ==>
        && output.value.generatorKeyring.None?)
      //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
      //= type=implication
      //# If there is a set of child identifiers then a set of AWS KMS Keyring
      //# (aws-kms-keyring.md) MUST be created for each AWS KMS key identifier
      //# by initializing each keyring with
      && (awsKmsKeys.Some?
      ==>
        && |awsKmsKeys.value| == |output.value.childKeyrings|
        && forall index | 0 <= index < |awsKmsKeys.value| ::
          // AWS KMS Keyring must be created for each AWS KMS Key identifier
          && var childKeyring: Types.IKeyring := output.value.childKeyrings[index];
          && childKeyring is AwsKmsKeyring.AwsKmsKeyring
          && var awsKmsChild := childKeyring as AwsKmsKeyring.AwsKmsKeyring;
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
      AwsKmsArnParsing.IsAwsKmsIdentifierString,
      allStrings
    ).MapFailure(WrapStringToError);

    var generatorKeyring : Option<AwsKmsKeyring.AwsKmsKeyring>;
    match generator {
      case Some(generatorIdentifier) =>
        var arn :- AwsKmsArnParsing.IsAwsKmsIdentifierString(generatorIdentifier).MapFailure(WrapStringToError);
        var region := AwsKmsArnParsing.GetRegion(arn);
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.5
        //= type=implication
        //# NOTE: The AWS Encryption SDK SHOULD NOT attempt to evaluate its own
        //# default region.
        var client :- clientSupplier.GetClient(Types.GetClientInput( region := region.UnwrapOr("")));
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
          invariant fresh(MultiKeyring.GatherModifies(generatorKeyring, children) - clientSupplier.Modifies)
          invariant forall i | 0 <= i < |children[..index]|
          ::
            && children[i].awsKmsKey == awsKmsKeys.value[i]
            && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
            && children[i].ValidState()
        {
          var childIdentifier := childIdentifiers[index];
          var info :- AwsKmsArnParsing.IsAwsKmsIdentifierString(childIdentifier).MapFailure(WrapStringToError);
          var region := AwsKmsArnParsing.GetRegion(info);
          //Question: What should the behavior be if there is no region supplied?
          // I assume that the SDK will use the default region or throw an error
          var client :- clientSupplier.GetClient(Types.GetClientInput( region := region.UnwrapOr("")));
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

    :- Need(
      generatorKeyring.Some? || |children| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "generatorKeyring or child Keryings needed to create a multi keyring")
    );
    var keyring := new MultiKeyring.MultiKeyring(
      generatorKeyring,
      children
    );

    return Success(keyring);
  }

}
