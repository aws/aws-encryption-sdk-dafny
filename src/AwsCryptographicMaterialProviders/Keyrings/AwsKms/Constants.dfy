// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Util/UTF8.dfy"
include "../../../Generated/AwsCryptographicMaterialProviders.dfy" 
include "../../../KMS/AwsKmsArnParsing.dfy"

module Constants {
  import UTF8
  import Aws.Crypto
  import AwsKmsArnParsing

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s

  type AwsKmsEncryptedDataKey = edk: Crypto.EncryptedDataKey |
    && edk.keyProviderId == PROVIDER_ID
    && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
    witness *

  datatype AwsKmsEdkHelper = AwsKmsEdkHelper(
    edk: AwsKmsEncryptedDataKey,
    arn: AwsKmsArnParsing.AwsKmsArn
  )
}
