// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AmazonKeyManagementService.dfy"
include "../SDK/EncryptionContext.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"
include "AwsKmsArnParsing.dfy"

module {:extern "KMSUtils"} KMSUtils {
  import EncryptionContext
  import opened AmazonKeyManagementService
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import UTF8

  const MAX_GRANT_TOKENS := 10

  type CustomerMasterKey = AwsKmsIdentifierString
  type GrantTokens = s: seq<GrantToken> | 0 <= |s| <= MAX_GRANT_TOKENS
  type GrantToken = s: string | 0 < |s| <= 8192 witness *

  datatype ResponseMetadata = ResponseMetadata(metadata: map<string, string>, requestID: string)

  type HttpStatusCode = int //FIXME: Restrict this

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(
    encryptionContext: EncryptionContext.Map,
    grantTokens: seq<GrantToken>,
    keyID: AwsKmsIdentifierString,
    numberOfBytes: int32
  )
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS && 0 < numberOfBytes <= 1024
    }
  }

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(
    ciphertextBlob: seq<uint8>,
    keyID: string,
    plaintext: seq<uint8>
  )
  {
    predicate method IsWellFormed() {
      |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype EncryptRequest = EncryptRequest(
    encryptionContext: EncryptionContext.Map,
    grantTokens: seq<GrantToken>,
    keyID: AwsKmsIdentifierString,
    plaintext: seq<uint8>
  )
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype EncryptResponse = EncryptResponse(
    ciphertextBlob: seq<uint8>,
    contentLength: int,
    httpStatusCode: HttpStatusCode,
    keyID: string,
    responseMetadata: ResponseMetadata
  )
  {
    predicate method IsWellFormed() {
      |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype DecryptRequest = DecryptRequest(
    keyId: string,
    ciphertextBlob: seq<uint8>,
    encryptionContext: EncryptionContext.Map,
    grantTokens: seq<GrantToken>)
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype DecryptResponse = DecryptResponse(
    contentLength: int,
    httpStatusCode: HttpStatusCode,
    keyID: string,
    plaintext: seq<uint8>,
    responseMetadata: ResponseMetadata
  )

  method {:extern "KMSUtils.ClientHelper", "GetDefaultAWSKMSServiceClientExtern"} GetDefaultAWSKMSServiceClientExtern(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)

  // The `{:opaque}` is important.
  // This forces the verify to _only_ accept
  // the exact values passed in the `ensures` clause.
  // Without this, any client or request would pass verification.
  predicate {:opaque} GenerateDataKeyCalledWith(
    client: IAmazonKeyManagementService,
    request: GenerateDataKeyRequest
  ) {true}
  predicate {:opaque} GenerateDataKeyResult(
    ciphertextBlob: seq<uint8>,
    plaintext: seq<uint8>
  ) {true}

  predicate {:opaque} EncryptCalledWith(
    client: IAmazonKeyManagementService,
    request: EncryptRequest
  ) {true}
  predicate {:opaque} EncryptResult(
    ciphertextBlob: seq<uint8>
  ) {true}

  predicate {:opaque} DecryptCalled(
    client: IAmazonKeyManagementService,
    request: DecryptRequest
  ) {true}
  predicate {:opaque} DecryptResult(
    keyID: string,
    plaintext: seq<uint8>
  ) {true}

  method {:extern "KMSUtils.ClientHelper", "GenerateDataKey"} GenerateDataKey(
    client: IAmazonKeyManagementService,
    request: GenerateDataKeyRequest
  ) 
    returns (res: Result<GenerateDataKeyResponse, string>)
    requires request.Valid()
    ensures GenerateDataKeyCalledWith(client, request)
    ensures res.Success? ==>
      var r := res.value;
      GenerateDataKeyResult(r.ciphertextBlob, r.plaintext)

  method {:extern "KMSUtils.ClientHelper", "Encrypt"} Encrypt(
    client: IAmazonKeyManagementService,
    request: EncryptRequest
  )
    returns (res: Result<EncryptResponse, string>)
    requires request.Valid()
    ensures EncryptCalledWith(client, request)
    ensures res.Success? ==> EncryptResult(res.value.ciphertextBlob)

  method {:extern "KMSUtils.ClientHelper", "Decrypt"} Decrypt(
    client: IAmazonKeyManagementService,
    request: DecryptRequest
  ) returns (res: Result<DecryptResponse, string>)
    requires request.Valid()
    ensures DecryptCalled(client, request)
    ensures res.Success? ==>
      var r := res.value;
      DecryptResult(r.keyID, r.plaintext)

  trait {:extern "DafnyAWSKMSClientSupplier"} DafnyAWSKMSClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)
  }

  class BaseClientSupplier extends DafnyAWSKMSClientSupplier {

    constructor(){}

    // Since this is the base client supplier, this just calls the extern GetClient method
    method GetClient(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)
    {
      // Since this is the base client supplier, this obtains the extern client
      var resClient := GetDefaultAWSKMSServiceClientExtern(region);
      return resClient;
    }
  }
}
