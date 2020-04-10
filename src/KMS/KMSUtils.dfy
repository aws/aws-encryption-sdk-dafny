include "../SDK/EncryptionContext.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"

module {:extern "KMSUtils"} KMSUtils {
  import EncryptionContext
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8

  const MAX_GRANT_TOKENS := 10

  type CustomerMasterKey = s: string | ValidFormatCMK(s) witness "alias/ExampleAlias"

  predicate method ValidFormatCMK(cmk: string) {
    ValidFormatCMKKeyARN(cmk) || ValidFormatCMKAlias(cmk) || ValidFormatCMKAliasARN(cmk)
  }

  predicate method ValidFormatCMKKeyARN(cmk: string) {
    var components := Split(cmk, ':');
    UTF8.IsASCIIString(cmk) && 0 < |cmk| <= 2048 && |components| == 6 && components[0] == "arn" && components[2] == "kms" && Split(components[5], '/')[0] == "key"
  }

  predicate method ValidFormatCMKAlias(cmk: string) {
    var components := Split(cmk, '/');
    UTF8.IsASCIIString(cmk) && 0 < |cmk| <= 2048 && |components| == 2 && components[0] == "alias"
  }

  predicate method ValidFormatCMKAliasARN(cmk: string) {
    var components := Split(cmk, ':');
    UTF8.IsASCIIString(cmk) && 0 < |cmk| <= 2048 && |components| == 6 && components[0] == "arn" && components[2] == "kms" && Split(components[5], '/')[0] == "alias"
  }
  
  type GrantToken = s: string | 0 < |s| <= 8192 witness "witness"

  datatype ResponseMetadata = ResponseMetadata(metadata: map<string, string>, requestID: string)

  type HttpStatusCode = int //FIXME: Restrict this

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, numberOfBytes: int32)
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS && 0 < numberOfBytes <= 1024
    }
  }

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)
  {
    predicate method IsWellFormed() {
      |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype EncryptRequest = EncryptRequest(encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, plaintext: seq<uint8>)
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype EncryptResponse = EncryptResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, responseMetadata: ResponseMetadata)
  {
    predicate method IsWellFormed() {
      |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype DecryptRequest = DecryptRequest(ciphertextBlob: seq<uint8>, encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>)
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype DecryptResponse = DecryptResponse(contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)

  // TODO: Return Result<KMSClient>, Dafny does not currently support returning interfaces
  trait KMSClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
  }

  class DefaultClientSupplier extends KMSClientSupplier {
    constructor() {}
    method {:extern} GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
  }

  // https://docs.aws.amazon.com/sdkfornet/v3/apidocs/items/KeyManagementService/TKeyManagementServiceClient.html
  trait KMSClient {
    method GenerateDataKey(request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
      requires request.Valid()

	method Encrypt(request: EncryptRequest) returns (res: Result<EncryptResponse>)
      requires request.Valid()

    method Decrypt(request: DecryptRequest) returns (res: Result<DecryptResponse>)
      requires request.Valid()
  }

  class DefaultClient extends KMSClient {
    method {:extern} GenerateDataKey(request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
      requires request.Valid()

	method {:extern} Encrypt(request: EncryptRequest) returns (res: Result<EncryptResponse>)
      requires request.Valid()

    method {:extern} Decrypt(request: DecryptRequest) returns (res: Result<DecryptResponse>)
      requires request.Valid()
  }
}
