// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../../AwsArnParsing.dfy"

module AwsKmsMrkAreUnique {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
   import opened AwsArnParsing
  import Types = AwsCryptographyMaterialProvidersTypes 

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-are-unique.md#implementation
  //= type=implication
  //# The caller MUST provide:
  function method AwsKmsMrkAreUnique(identifiers: seq<AwsKmsIdentifier>)
  : (result: Outcome<Types.Error>)
  {
    var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);

    if |mrks| == 0 then
      Pass
    else
      var mrkKeyIds := Seq.Map(GetKeyId, mrks);
      var setMrks := ToSet(mrkKeyIds);
      if |mrkKeyIds| == |setMrks| then
        Pass
      else
        var duplicateMrkIds := set x | x in mrkKeyIds && multiset(mrkKeyIds)[x] >= 1;
        var isDuplicate := identifier => GetKeyId(identifier) in duplicateMrkIds;
        var identifierToString := (i: AwsKmsIdentifier) => i.ToString();

        var duplicateIdentifiers := Seq.Filter(isDuplicate, identifiers);
        assert |identifiers| >= |mrkKeyIds|;
        assert |mrks| == |mrkKeyIds|;
        var duplicates := Seq.Map(identifierToString, duplicateIdentifiers);

        if |duplicates| == 0 then
          Fail(Types.AwsCryptographicMaterialProvidersException(message :="Impossible"))
        else
          Fail(Types.AwsCryptographicMaterialProvidersException(
            message := "Related multi-Region keys: "
                + Join(duplicates, ",")
                + "are not allowed.")
          )
  }

  function method GetKeyId(identifier: AwsKmsIdentifier): (result: string) {
    match identifier {
      case AwsKmsArnIdentifier(a) => a.resource.value
      case AwsKmsRawResourceIdentifier(i) => i.value
    }
  }

  lemma AwsKmsMrkAreUniqueCorrect(identifiers: seq<AwsKmsIdentifier>)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-are-unique.md#implementation
    //= type=implication
    //# If the list does not contain any [multi-Region keys](aws-kms-key-
    //# arn.md#identifying-an-aws-kms-multi-region-key) this function MUST
    //# exit successfully.
    ensures
      |Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers)| == 0
    ==>
      AwsKmsMrkAreUnique(identifiers).Pass?

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-are-unique.md#implementation
    //= type=implication
    //# If there are zero duplicate resource ids between the multi-region
    //# keys, this function MUST exit successfully
    ensures
      var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
      var ids := Seq.Map(GetKeyId, mrks);
      && |mrks| > 0
      && Seq.HasNoDuplicates(ids)
    ==>
      AwsKmsMrkAreUnique(identifiers).Pass?

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-are-unique.md#implementation
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
      // TODO this only checks for failure, but not the error message
      AwsKmsMrkAreUnique(identifiers).Fail?
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
