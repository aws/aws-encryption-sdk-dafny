// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"

module  AwsKmsMrkAreUnique {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import opened AwsKmsArnParsing

  //= compliance/framework/aws-kms/aws-kms-mrk-are-unique.txt#2.5
  //= type=implication
  //# The caller MUST provide:
  function method AwsKmsMrkAreUnique(identifiers: seq<AwsKmsIdentifier>)
  : (result: Result<(), string>)
  {
    var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);

    if |mrks| == 0 then
      Success(())
    else
      var mrkKeyIds := Seq.Map(GetKeyId, mrks);
      var setMrks := ToSet(mrkKeyIds);
      if |mrkKeyIds| == |setMrks| then
        Success(())
      else
        var duplicateMrkIds := set x | x in mrkKeyIds && multiset(mrkKeyIds)[x] >= 1;
        var isDuplicate := identifier => GetKeyId(identifier) in duplicateMrkIds;
        var identifierToString := (i: AwsKmsIdentifier) => i.ToString();

        var duplicateIdentifiers := Seq.Filter(isDuplicate, identifiers);
        var duplicates := Seq.Map(identifierToString, duplicateIdentifiers);
        :- Need(|duplicates| > 0, "Impossible");

        Failure(
          "Related multi-Region keys: "
          + Join(duplicates, ",")
          + "are not allowed."
        )
  }

  function method GetKeyId(identifier: AwsKmsIdentifier): (result: string) {
    match identifier {
      case AwsKmsArnIdentifier(a) => a.resource.value
      case AwsKmsRawResourceIdentifier(i) => i.value
    }
  }

  lemma AwsKmsMrkAreUniqueCorrect(identifiers: seq<AwsKmsIdentifier>)
    //= compliance/framework/aws-kms/aws-kms-mrk-are-unique.txt#2.5
    //= type=implication
    //# If the list does not contain any multi-Region keys (aws-kms-key-
    //# arn.md#identifying-an-aws-kms-multi-region-key) this function MUST
    //# exit successfully.
    ensures
      |Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers)| == 0
    ==>
      AwsKmsMrkAreUnique(identifiers).Success?

    //= compliance/framework/aws-kms/aws-kms-mrk-are-unique.txt#2.5
    //= type=implication
    //# If there are zero duplicate resource ids between the multi-region
    //# keys, this function MUST exit successfully
    ensures
      var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
      var ids := Seq.Map(GetKeyId, mrks);
      && |mrks| > 0
      && Seq.HasNoDuplicates(ids)
    ==>
      AwsKmsMrkAreUnique(identifiers).Success?

    //= compliance/framework/aws-kms/aws-kms-mrk-are-unique.txt#2.5
    //= type=implication
    //# If any duplicate multi-region resource ids exist, this function MUST
    //# yield an error that includes all identifiers with duplicate resource
    //# ids not only the first duplicate found.
    ensures
      var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
      var ids := Seq.Map(GetKeyId, mrks);
      && |mrks| > 0
      && !Seq.HasNoDuplicates(ids)
    ==>
      AwsKmsMrkAreUnique(identifiers).Failure?
  {
    var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
    var ids := Seq.Map(GetKeyId, mrks);
    if Seq.HasNoDuplicates(ids) {
      LemmaCardinalityOfSetNoDuplicates(ids);
    }
    if |ToSet(ids)| == |ids| {
      LemmaNoDuplicatesCardinalityOfSet(ids);
    }
  }
}
