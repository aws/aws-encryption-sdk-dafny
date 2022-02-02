// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"

include "../../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../Generated/KeyManagementService.dfy"

include "../../Keyring.dfy"
include "../MultiKeyring.dfy"
include "AwsKmsArnParsing.dfy"
include "AwsKmsMrkAreUnique.dfy"
include "AwsKmsMrkAwareSymmetricKeyring.dfy"
include "AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring.dfy"

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
        var client := clientSupplier.GetClient(Crypto.GetClientInput(region));
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
