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

  // TODO: Return Result<KMSClient>, Dafny does not currently support returning Result<trait>
  trait {:termination false} KMSClientSupplier {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
  }

  class DefaultClientSupplier extends KMSClientSupplier {
    const clientSupplier: KMSClientSupplier

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid()
    }

    constructor()
      ensures Valid()
    {
      var newClientSupplier := new BaseClientSupplier();
      this.clientSupplier := newClientSupplier;
      Repr := {this} + newClientSupplier.Repr;
    }

    method GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
    {
      var resClient := this.clientSupplier.GetClient(region);
      return resClient;
    }
  }

  // An implementation of a KMSClientSupplier that takes in an existing KMSClientSupplier as well as a seq of regions
  // (strings). The LimitRegionsClientSupplier will only return a KMSClient from the given KMSClientSupplier if the
  // region provided to GetClient(region) is in the list of regions associated with the LimitRegionsClientSupplier.
  class LimitRegionsClientSupplier extends KMSClientSupplier {
    const clientSupplier: KMSClientSupplier
    const regions: seq<string>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid()
    }

    constructor(clientSupplier: KMSClientSupplier, regions: seq<string>)
      requires clientSupplier.Valid()
      ensures this.clientSupplier == clientSupplier
      ensures this.regions == regions
      ensures Valid()
    {
      this.clientSupplier := clientSupplier;
      this.regions := regions;
      Repr := {this} + clientSupplier.Repr;
    }

    method GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
      ensures region.None? ==> res.Failure?
      ensures region.Some? && !(region.get in regions) ==> res.Failure?
      ensures region.Some? && region.get in regions ==> res.Success?
    {
      // In order to limit regions, make sure our given region string exists and is a member of the regions to limit to
      if region.Some? && region.get in regions {
        var resClient := this.clientSupplier.GetClient(region);
        return resClient;
      } else {
        return Failure("Given region not in regions maintained by LimitRegionsClientSupplier");
      }
    }
  }

  // An implementation of a KMSClientSupplier that takes in an existing KMSClientSupplier as well as a seq of regions
  // (strings). The ExcludeRegionsClientSupplier will only return a KMSClient from the given KMSClientSupplier if the
  // region provided to GetClient(region) is not in the list of regions associated with the ExcludeRegionsClientSupplier.
  class ExcludeRegionsClientSupplier extends KMSClientSupplier {
    const clientSupplier: KMSClientSupplier
    const regions: seq<string>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid()
    }

    constructor(clientSupplier: KMSClientSupplier, regions: seq<string>)
      requires clientSupplier.Valid()
      ensures this.clientSupplier == clientSupplier
      ensures this.regions == regions
      ensures Valid()
    {
      this.clientSupplier := clientSupplier;
      this.regions := regions;
      Repr := {this} + clientSupplier.Repr;
    }

    method GetClient(region: Option<string>) returns (res: Result<DefaultClient>)
      ensures region.None? ==> res.Success?
      ensures region.Some? && !(region.get in regions) ==> res.Success?
      ensures region.Some? && region.get in regions ==> res.Failure?
    {
      // Exclude if our regions is a member of the maintained regions
      if region.Some? && region.get in regions {
        return Failure("Given region is in regions maintained by ExcludeRegionsClientSupplier");
      } else {
        var resClient := this.clientSupplier.GetClient(region);
        return resClient;
      }
    }
  }

  class BaseClientSupplier extends KMSClientSupplier {

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }

    // TODO: This needs to take in a region, and creds
    // What we really want to do is take in a AmazonKeyManagementServiceConfig
    // and an AWSCredentials
    constructor()
      ensures Valid()
    {
       Repr := {this};
    }

    // Since this is the base client supplier, this just calls the extern GetClient method
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
