// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AwsKmsArnParsing.dfy"

module  AwsKmsMrkMatchForDecrypt {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import opened AwsKmsArnParsing

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-match-for-decrypt.md#implementation
  //= type=implication
  //# The caller MUST provide:
  //# *  2 AWS KMS key identifiers 
  predicate method AwsKmsMrkMatchForDecrypt(
    configuredAwsKmsIdentifier: AwsKmsIdentifier,
    messageAwsKmsIdentifer: AwsKmsIdentifier
  ) {
    if (configuredAwsKmsIdentifier == messageAwsKmsIdentifer) then true
    else
      match (messageAwsKmsIdentifer, configuredAwsKmsIdentifier) {
        case (
          AwsKmsArnIdentifier(configuredAwsKmsArn),
          AwsKmsArnIdentifier(messageAwsKmsArn)
        ) =>
          if !IsMultiRegionAwsKmsArn(configuredAwsKmsArn) || !IsMultiRegionAwsKmsArn(messageAwsKmsArn) then false
          else
            && messageAwsKmsArn.partition == configuredAwsKmsArn.partition
            && messageAwsKmsArn.service   == configuredAwsKmsArn.service
            && messageAwsKmsArn.account   == configuredAwsKmsArn.account
            && messageAwsKmsArn.resource  == configuredAwsKmsArn.resource
        case (_,_) => false
      }
  }

  lemma AwsKmsMrkMatchForDecryptCorrect(config: string, message: string)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-match-for-decrypt.md#implementation
    //= type=implication
    //# If both identifiers are identical, this function MUST return `true`.
    ensures
      var c := ParseAwsKmsIdentifier(config);
      var m := ParseAwsKmsIdentifier(message);
      && config == message
      && c.Success?
      && m.Success?
    ==>
      AwsKmsMrkMatchForDecrypt(c.value, m.value)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-match-for-decrypt.md#implementation
    //= type=implication
    //# Otherwise if either input is not [identified as a multi-Region key]
    //# (aws-kms-key-arn.md#identifying-an-aws-kms-multi-region-key), then
    //# this function MUST return `false`.
    ensures
      var c := ParseAwsKmsArn(config);
      var m := ParseAwsKmsArn(message);
      && config != message
      && c.Success?
      && m.Success?
      && IsMultiRegionAwsKmsArn(c.value) != IsMultiRegionAwsKmsArn(m.value)
    ==>
      !AwsKmsMrkMatchForDecrypt(
        AwsKmsArnIdentifier(c.value), 
        AwsKmsArnIdentifier(m.value)
      );
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-match-for-decrypt.md#implementation
    //= type=implication
    //# Otherwise if both inputs are
    //# [identified as a multi-Region keys](aws-kms-key-arn.md#identifying-an-
    //# aws-kms-multi-region-key), this function MUST return the result of
    //# comparing the `partition`, `service`, `accountId`, `resourceType`,
    //# and `resource` parts of both ARN inputs.
    ensures
      var c := ParseAwsKmsArn(config);
      var m := ParseAwsKmsArn(message);
      && c.Success?
      && m.Success?
      && IsMultiRegionAwsKmsArn(c.value)
      && IsMultiRegionAwsKmsArn(m.value)
    ==>
      AwsKmsMrkMatchForDecrypt(
        AwsKmsArnIdentifier(c.value),
        AwsKmsArnIdentifier(m.value)
      ) == (
        && m.value.partition == c.value.partition
        && m.value.service   == c.value.service
        && m.value.account   == c.value.account
        && m.value.resource  == c.value.resource
      );
  {}
}
