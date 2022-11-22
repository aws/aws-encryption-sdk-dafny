// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module  AwsKmsArnParsing {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import opened UInt = StandardLibrary.UInt
  import UTF8

  const MAX_AWS_KMS_IDENTIFIER_LENGTH := 2048

  datatype AwsResource = AwsResource(
    resourceType: string,
    value: string
  ) {
    predicate method Valid()
    {
      && 0 < |value|
    }

    function method ToString(): string
    {
      // By the ARN specification both `:` and `/` are valid.
      // But this class does not aim to preserve this choice.
      // So I pick `/` because this is the only valid value for AWS KMS.
      resourceType + "/" + value
    }
  }

  datatype AwsArn = AwsArn(
    arnLiteral: string,
    partition: string,
    service: string,
    region: string,
    account: string,
    resource: AwsResource
  ) {
    predicate method Valid()
    {
      && arnLiteral == "arn"
      && 0 < |partition|
      && 0 < |service|
      && 0 < |region|
      && 0 < |account|
      && resource.Valid()
    }

    function method ToString(): string
      requires this.Valid()
    {
      ToArnString(None)
    }

    function method ToArnString(customRegion: Option<string>): string
      requires this.Valid()
      decreases if customRegion.None? then 1 else 0
    {
      match customRegion {
        case None => ToArnString(Some(region))
        case Some(customRegion) => Join(
          [
            arnLiteral,
            partition,
            service,
            customRegion,
            account,
            resource.ToString()
          ],
          ":")
      }
    }
  }

  predicate method ValidAwsKmsResource(resource: AwsResource)
  {
    && resource.Valid()
    && (
      || resource.resourceType == "key"
      || resource.resourceType == "alias"
      )
  }

  predicate method ValidAwsKmsArn(arn: AwsArn)
  {
    && arn.Valid()
    && arn.service == "kms"
    && ValidAwsKmsResource(arn.resource)
  }

  type AwsKmsArn = a : AwsArn | ValidAwsKmsArn(a)
    witness *

  type AwsKmsResource = r : AwsResource | ValidAwsKmsResource(r)
    witness *

  datatype AwsKmsIdentifier =
    | AwsKmsArnIdentifier(a: AwsKmsArn)
    | AwsKmsRawResourceIdentifier(r: AwsKmsResource)
  {
    function method ToString(): string
    {
      match this {
        case AwsKmsArnIdentifier(a: AwsKmsArn) => a.ToString()
        case AwsKmsRawResourceIdentifier(r: AwsKmsResource)  => r.ToString()
      }
    }
  }

  function method ParseAwsKmsRawResources(identifier: string): (result: Result<AwsKmsResource, string>)
  {
    var info := Split(identifier, '/');

    :- Need(info[0] != "key", "Malformed raw key id: " + identifier);

    if |info| == 1 then
      ParseAwsKmsResources("key/" + identifier)
    else
      ParseAwsKmsResources(identifier)
  }

  function method ParseAwsKmsResources(identifier: string): (result: Result<AwsKmsResource, string>)
  {
    var info := Split(identifier, '/');

    :- Need(|info| > 1, "Malformed resource: " + identifier);

    var resourceType := info[0];
    var value := Join(info[1..], "/");

    var resource := AwsResource(resourceType, value);

    :- Need(ValidAwsKmsResource(resource), "Malformed resource: " + identifier);

    Success(resource)
  }

  lemma ParseAwsKmsResourcesCorrect(identifier: string)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The resource section MUST be non-empty and MUST be split by a
    //# single `/` any additional `/` are included in the resource id
    ensures ParseAwsKmsResources(identifier).Success? ==>
      var info := Split(identifier, '/');
      var r := ParseAwsKmsResources(identifier);
      && |info| > 1
      && Join([r.value.resourceType, r.value.value], "/") == identifier
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The resource type MUST be either `alias` or `key`
    ensures ParseAwsKmsResources(identifier).Success? ==>
      var resourceType := Split(identifier, '/')[0];
      "key" == resourceType || "alias" == resourceType
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The resource id MUST be a non-empty string
    ensures ParseAwsKmsResources(identifier).Success? ==>
      var info := Split(identifier, '/');
      |Join(info[1..], "/")| > 0
  {}

  function method ParseAwsKmsArn(identifier: string): (result: Result<AwsKmsArn, string>)
  {
    var components := Split(identifier, ':');

    :- Need(6 == |components|, "Malformed arn: " + identifier);

    var resource :- ParseAwsKmsResources(components[5]);

    var arn := AwsArn(
      components[0],
      components[1],
      components[2],
      components[3],
      components[4],
      resource
    );

    :- Need(ValidAwsKmsArn(arn), "Malformed Arn:" + identifier);

    Success(arn)
  }

  lemma ParseAwsKmsArnCorrect(identifier: string)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# MUST start with string `arn`
    ensures ParseAwsKmsArn(identifier).Success? ==> "arn" <= identifier

    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')| == 6

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The partition MUST be a non-empty
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[1]| > 0

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The service MUST be the string `kms`
    ensures ParseAwsKmsArn(identifier).Success? ==> Split(identifier, ':')[2] == "kms"

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The region MUST be a non-empty string
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[3]| > 0

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#a-valid-aws-kms-arn
    //= type=implication
    //# The account MUST be a non-empty string
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[4]| > 0
  {}

  function method ParseAwsKmsIdentifier(identifier: string): (result: Result<AwsKmsIdentifier, string>)
  {
    if "arn:" <= identifier then
      var arn :- ParseAwsKmsArn(identifier);
      Success(AwsKmsArnIdentifier(arn))
    else
      var r :- ParseAwsKmsRawResources(identifier);
      Success(AwsKmsRawResourceIdentifier(r))
  }

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-arn
  //= type=implication
  //# This function MUST take a single AWS KMS ARN
  //# If the input is an invalid AWS KMS ARN this function MUST error.
  predicate method IsMultiRegionAwsKmsArn(arn: AwsKmsArn)
  {
    IsMultiRegionAwsKmsResource(arn.resource)
  }

  lemma IsMultiRegionAwsKmsArnCorrectness(arn: AwsKmsArn)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-arn
    //= type=implication
    //# If resource type is “alias”,
    //# this is an AWS KMS alias ARN and MUST return false.
    ensures !IsMultiRegionAwsKmsArn(arn) <== arn.resource.resourceType == "alias"
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-arn
    //= type=implication
    //# If resource type is “key” and resource ID starts with “mrk-“,
    //# this is a AWS KMS multi-Region key ARN and MUST return true.
    ensures !IsMultiRegionAwsKmsArn(arn) <==
        && arn.resource.resourceType == "key"
        && !("mrk-" <= arn.resource.value)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-arn
    //= type=implication
    //# If resource type is “key” and resource ID does not start with “mrk-“,
    //# this is a (single-region) AWS KMS key ARN and MUST return false.
    ensures IsMultiRegionAwsKmsArn(arn) <==
      && arn.resource.resourceType == "key"
      && "mrk-" <= arn.resource.value
  {
  }

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-identifier
  //= type=implication
  //# This function MUST take a single AWS KMS identifier
  predicate method IsMultiRegionAwsKmsIdentifier(identifier: AwsKmsIdentifier)
  {
    match identifier {
      case AwsKmsArnIdentifier(arn) =>
        IsMultiRegionAwsKmsArn(arn)
      case AwsKmsRawResourceIdentifier(r) =>
        IsMultiRegionAwsKmsResource(r)
    }
  }

  lemma IsMultiRegionAwsKmsIdentifierCorrect(s: string)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-identifier
    //= type=implication
    //# If the input starts with "arn:",
    //# this MUST return the output of [identifying an an AWS KMS multi-Region ARN](aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-arn)
    //# called with this input.
    ensures "arn:" <= s && ParseAwsKmsArn(s).Success?
      ==>
        var arn := ParseAwsKmsArn(s);
        var arnIdentifier := AwsKmsArnIdentifier(arn.value);
        IsMultiRegionAwsKmsIdentifier(arnIdentifier) == IsMultiRegionAwsKmsArn(arn.value)

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-identifier
    //= type=implication
    //# If the input starts with “alias/“,
    //# this an AWS KMS alias and not a multi-Region key id and MUST return false.
    ensures "alias/" <= s && ParseAwsKmsResources(s).Success?
      ==>
        var resource := ParseAwsKmsResources(s);
        var resourceIdentifier := AwsKmsRawResourceIdentifier(resource.value);
        !IsMultiRegionAwsKmsIdentifier(resourceIdentifier)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-identifier
    //= type=implication
    //# If the input starts with “mrk-“,
    //# this is a multi-Region key id and MUST return true.
    ensures "mrk-" <= s && ParseAwsKmsResources(s).Success?
      ==>
        var resource := ParseAwsKmsResources(s);
        var resourceIdentifier := AwsKmsRawResourceIdentifier(resource.value);
        IsMultiRegionAwsKmsIdentifier(resourceIdentifier)
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-key-arn.md#identifying-an-an-aws-kms-multi-region-identifier
    //= type=implication
    //# If
    //# the input does not start with any of the above, this is not a multi-
    //# Region key id and MUST return false.
    ensures (
        && !("arn:" <= s )
        && !("alias/" <= s )
        && !("mrk-" <= s )
        && ParseAwsKmsIdentifier(s).Success?
      )
      ==>
        var resourceIdentifier := ParseAwsKmsIdentifier(s);
        !IsMultiRegionAwsKmsIdentifier(resourceIdentifier.value)
  {}

  predicate method IsMultiRegionAwsKmsResource(resource: AwsKmsResource)
  {
    resource.resourceType == "key" && "mrk-" <= resource.value
  }

  function method GetRegion(
    identifier: AwsKmsIdentifier
  ): (res: Option<string>)
  {
    match identifier {
      case AwsKmsArnIdentifier(a) => Some(a.region)
      case AwsKmsRawResourceIdentifier(_) => None()
    }
  }

  function method IsAwsKmsIdentifierString(
    s: string
  ): (res: Result<AwsKmsIdentifier, string>)
  {
    :- Need(UTF8.IsASCIIString(s), "Not a valid ASCII string.");
    :- Need(0 < |s| <= MAX_AWS_KMS_IDENTIFIER_LENGTH , "Identifier exceeds maximum length.");
    ParseAwsKmsIdentifier(s)
  }

  type AwsKmsIdentifierString = s: string |
    IsAwsKmsIdentifierString(s).Success?
    witness *

}
