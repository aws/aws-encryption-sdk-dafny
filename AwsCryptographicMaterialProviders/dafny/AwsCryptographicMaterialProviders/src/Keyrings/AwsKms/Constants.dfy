// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../../AwsArnParsing.dfy"

module Constants {
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes
  import AwsArnParsing

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s
  
  // UTF-8 encoded "aws-kms-hierarchy"
  const PROVIDER_ID_HIERARCHY:  UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73, 
      0x2D, 0x68, 0x69, 0x65, 0x72, 0x61, 0x72, 0x63, 0x68, 0x79];
    assert UTF8.ValidUTF8Range(s, 0, 17);
    s

  // UTF-8 encoded "aws-kms-rsa"
  const RSA_PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [ 0x61, 0x77, 0x73, 0x2d, 0x6b, 0x6d, 0x73, 0x2d, 0x72, 0x73, 0x61 ];
    assert UTF8.ValidUTF8Range(s, 0, 11);
    s

  type AwsKmsEncryptedDataKey = edk: Types.EncryptedDataKey |
    && edk.keyProviderId == PROVIDER_ID
    && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
    witness *

  /*
   * A datatype to make it easier to work with Encrypted Data Keys
   * that are protected by AWS KMS. Though the EDK technically contains
   * the ARN (in the keyProviderInfo field), pulling it out into a
   * dedicated variable which has already been converted into a usable
   * format makes our lives easier.
   */
  datatype AwsKmsEdkHelper = AwsKmsEdkHelper(
    edk: AwsKmsEncryptedDataKey,
    arn: AwsArnParsing.AwsKmsArn
  )
}
