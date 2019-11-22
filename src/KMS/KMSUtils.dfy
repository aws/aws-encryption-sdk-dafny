include "../SDK/Materials.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"

module {:extern "KMSUtils"} KMSUtils {
  import Mat = Materials
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8

  const PROVIDER_ID := "aws-kms"

  function method ProviderID(): (id: UTF8.ValidUTF8Bytes)
  {
    UTF8.Encode(PROVIDER_ID).value
  }

  trait ClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<KMSClient>)
  }

  class DefaultClientSupplier extends ClientSupplier {
    constructor() {}
    method {:extern} GetClient(region: Option<string>) returns (res: Result<KMSClient>)
  }

  datatype DataKeySpec = AES_128 | AES_256

  datatype ResponseMetadata = ResponseMetadata(metadate: map<string, string>, requestID: string)

  type HttpStatusCode = int //FIXME: Restrict this


  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<string>, keyID: string, numberOfBytes: int32)

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)
  {
    predicate method IsWellFormed() {
      StringIs8Bit(keyID) && |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }


  datatype EncryptRequest = EncryptRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<string>, keyID: string, plaintext: seq<uint8>)

  datatype EncryptResponse = EncryptResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, responseMetadata: ResponseMetadata)
  {
    predicate method IsWellFormed() {
      StringIs8Bit(keyID) && |keyID| < UINT16_LIMIT && |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype DecryptRequest = DecryptRequest(ciphertextBlob: seq<uint8>, encryptionContext: Mat.EncryptionContext, grantTokens: seq<string>)

  datatype DecryptResponse = DecryptResponse(contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)

  // https://docs.aws.amazon.com/sdkfornet/v3/apidocs/items/KeyManagementService/TKeyManagementServiceClient.html
  class KMSClient {
    method {:extern} GenerateDataKey(request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
      //TODO mmtj: Should this be marked as modifying all of request's fields?

	method {:extern} Encrypt(request: EncryptRequest) returns (res: Result<EncryptResponse>)
      //TODO mmtj: Should this be marked as modifying all of request's fields?

    method {:extern} Decrypt(request: DecryptRequest) returns (res: Result<DecryptResponse>)
      // TODO mmtj: Should this be marked as modifying all of request's fields?
  }
}
