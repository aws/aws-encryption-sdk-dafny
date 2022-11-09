// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../MultiKeyring.dfy"
include "AwsKmsArnParsing.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "AwsKmsDiscoveryKeyring.dfy"
include "AwsKmsUtils.dfy"
include "../../AlgorithmSuites.dfy"

module DiscoveryMultiKeyring {
  import opened Wrappers
  import Seq
  import Types = AwsCryptographyMaterialProvidersTypes 
  import KMS = Types.ComAmazonawsKmsTypes
  import MultiKeyring
  import AwsKmsArnParsing
  import AwsKmsMrkAreUnique
  import AwsKmsDiscoveryKeyring
  import opened AwsKmsUtils

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
    discoveryFilter: Option<Types.DiscoveryFilter>,
    clientSupplier: Types.IClientSupplier,
    grantTokens: Option<KMS.GrantTokenList>
  )
    returns (
      output: Result<MultiKeyring.MultiKeyring, Types.Error>
    )
    requires clientSupplier.ValidState()
    modifies clientSupplier.Modifies
    ensures output.Success? ==>
    && output.value.ValidState()
    && fresh(output.value)
    && fresh(output.value.History)
    && fresh(output.value.Modifies - clientSupplier.Modifies)

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
      output.Failure?

    //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
    //= type=implication
    //# Then a Multi-Keyring (../multi-keyring.md#inputs) MUST be initialize
    //# by using this set of discovery keyrings as the child keyrings
    //# (../multi-keyring.md#child-keyrings).
    //# This Multi-Keyring MUST be
    //# this functions output.
    ensures
      && output.Success?
    ==>
      && output.value.generatorKeyring.None?
      && |regions| == |output.value.childKeyrings|
      && forall i | 0 <= i < |regions|
      ::
        && var k: Types.IKeyring := output.value.childKeyrings[i];
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

    :- Need(|regions| > 0, Types.AwsCryptographicMaterialProvidersException(
        message := "No regions passed."));
    :- Need(Seq.IndexOfOption(regions, "").None?, Types.AwsCryptographicMaterialProvidersException(
        message := "Empty string is not a valid region."));

    var children : seq<AwsKmsDiscoveryKeyring.AwsKmsDiscoveryKeyring> := [];

    for i := 0 to |regions|
        invariant |regions[..i]| == |children|
        invariant fresh(MultiKeyring.GatherModifies(None, children) - clientSupplier.Modifies)
        invariant forall i | 0 <= i < |children|
        ::
          && (discoveryFilter.Some? ==> children[i].discoveryFilter == discoveryFilter)
          && (grantTokens.Some? ==> children[i].grantTokens == grantTokens.value)
          && children[i].ValidState()
      {
        var region := regions[i];
        //= compliance/framework/aws-kms/aws-kms-multi-keyrings.txt#2.6
        //# A set of AWS KMS clients MUST be created by calling regional client
        //# supplier for each region in the input set of regions.
        var client :- clientSupplier.GetClient(Types.GetClientInput(region := region));
        // :- Need(
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


}
