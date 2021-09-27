// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Defs.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuite.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "AwsKmsMrkAwareSymmetricKeyring.dfy"
include "../MultiKeyring.dfy"

module {:extern "AwsKmsMrkAwareMultiKeyrings"} AwsKmsMrkAwareMultiKeyrings {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Seq
  import opened AwsKmsMrkAwareSymmetricKeyring
  import opened MultiKeyringDef
  import AlgorithmSuite
  import KeyringDefs
  import Materials
  import KMSUtils
  import UTF8

  const defaultClientSupplier : KMSUtils.DafnyAWSKMSClientSupplier := new KMSUtils.BaseClientSupplier();

  method StrictMultiKeyring(
    generator: Option<string>,
    awsKmsKeys: Option<seq<string>>,
    clientSupplier: Option<KMSUtils.DafnyAWSKMSClientSupplier>,
    grantTokens: Option<seq<KMSUtils.GrantToken>>
  ) returns (res: Result<MultiKeyring, string>) {

    var supplier := match clientSupplier {
      case Some(s) => s
      case None() => defaultClientSupplier
    };

    var generatorKeyring : AwsKmsMrkAwareSymmetricKeyring?;

    match (generator) {
      case Some(generatorIdentifier) => 
        var info :- ParseAwsKmsIdentifier(generatorIdentifier);
        var region := GetRegion(info);
        var client :- supplier(region);
        generatorKeyring := new AwsKmsMrkAwareSymmetricKeyring(
          client,
          generatorIdentifier,
          grantTokens
        );
      case None() => generatorKeyring := null;
    }

    var children : seq<AwsKmsMrkAwareSymmetricKeyring>;

    match awsKmsKeys {
      case Some(childIdentifiers) =>
        for i := 0 to |childIdentifiers| {
          var childIdentifier := childIdentifiers[i];
          var info :- ParseAwsKmsIdentifier(childIdentifier);
          var region := GetRegion(info);
          var client :- supplier(region);
          var keyring := new AwsKmsMrkAwareSymmetricKeyring(
            client,
            childIdentifier,
            grantTokens
          );
          // Order is important
          children := children + [keyring];
        }

      case None() => children := [];
    }

    var keyring := new MultiKeyring(
      generatorKeyring,
      children
    );

    return Success(keyring);
  }

  method DiscoveryMultiKeyring(
    regions: seq<string>
    discoveryFilter: Option<string>,
    clientSupplier: Option<KMSUtils.DafnyAWSKMSClientSupplier>,
    grantTokens: Option<seq<KMSUtils.GrantToken>>
  ) returns (res: Result<MultiKeyring, string>) {

    var supplier := match clientSupplier {
      case Some(s) => s
      case None() => defaultClientSupplier
    };

    var children : seq<AwsKmsMrkAwareSymmetricKeyring>;

    for i := 0 to |regions| {
      var client := supplier(regions[i]);


  }

}
