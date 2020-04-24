include "../SDK/EncryptionContext.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"

// Add extern reference for a native AWS KMS service client
module {:extern "Amazon.KeyManagementService"} AmazonKeyManagementService {
  class {:extern "AmazonKeyManagementServiceClient"} AmazonKeyManagementServiceClient {}
}

module {:extern "KMSUtils"} KMSUtils {
  import EncryptionContext
  import opened AmazonKeyManagementService
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

  method {:extern "KMSUtils.ClientHelper", "GetDefaultAWSKMSServiceClientExtern"} GetDefaultAWSKMSServiceClientExtern(region: Option<string>) returns (res: Result<AmazonKeyManagementServiceClient>)

  method {:extern "KMSUtils.ClientHelper", "GenerateDataKey"} GenerateDataKey(client: AmazonKeyManagementServiceClient, request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
    requires request.Valid()

  method {:extern "KMSUtils.ClientHelper", "Encrypt"} Encrypt(client: AmazonKeyManagementServiceClient, request: EncryptRequest) returns (res: Result<EncryptResponse>)
    requires request.Valid()

  method {:extern "KMSUtils.ClientHelper", "Decrypt"} Decrypt(client: AmazonKeyManagementServiceClient, request: DecryptRequest) returns (res: Result<DecryptResponse>)
    requires request.Valid()

  trait {:extern "AWSKMSClientSupplier"} AWSKMSClientSupplier {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    method GetClient(region: Option<string>) returns (res: Result<AmazonKeyManagementServiceClient>)
      requires Valid()
      ensures Valid()
      decreases Repr
  }

  // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as a seq of regions (strings).
  // The LimitRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
  // if the region provided to GetClient(region) is in the list of regions associated with the LimitRegionsClientSupplier.
  class LimitRegionsClientSupplier extends AWSKMSClientSupplier {
    const clientSupplier: AWSKMSClientSupplier
    const regions: seq<string>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid()
    }

    constructor(clientSupplier: AWSKMSClientSupplier, regions: seq<string>)
      requires clientSupplier.Valid()
      ensures this.clientSupplier == clientSupplier
      ensures this.regions == regions
      ensures Valid() && fresh(Repr - clientSupplier.Repr)
    {
      this.clientSupplier := clientSupplier;
      this.regions := regions;
      Repr := {this} + clientSupplier.Repr;
    }

    method GetClient(region: Option<string>) returns (res: Result<AmazonKeyManagementServiceClient>)
      requires Valid()
      ensures Valid()
      // Verify this behavior with the spec. TODO: https://github.com/awslabs/aws-encryption-sdk-dafny/issues/272
      // Only add a post condition around failures, since the GetClient call could return a success or failure
      ensures region.None? ==> res.Failure?
      ensures region.Some? && !(region.get in regions) ==> res.Failure?
      decreases Repr
    {
      // In order to limit regions, make sure our given region string exists and is a member of the regions to limit to
      if region.Some? && region.get in regions {
        var resClient := clientSupplier.GetClient(region);
        return resClient;
      } else if region.None? {
        return Result.Failure("LimitRegionsClientSupplier GetClient requires a region");
      }
      var failure := "Given region " + region.get + " not in regions maintained by LimitRegionsClientSupplier";
      return Result.Failure(failure);
    }
  }

  // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as a seq of regions (strings).
  // The ExcludeRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
  // if the region provided to GetClient(region) is not in the list of regions associated with the ExcludeRegionsClientSupplier.
  class ExcludeRegionsClientSupplier extends AWSKMSClientSupplier {
    const clientSupplier: AWSKMSClientSupplier
    const regions: seq<string>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid()
    }

    constructor(clientSupplier: AWSKMSClientSupplier, regions: seq<string>)
      requires clientSupplier.Valid()
      ensures this.clientSupplier == clientSupplier
      ensures this.regions == regions
      ensures Valid() && fresh(Repr - clientSupplier.Repr)
    {
      this.clientSupplier := clientSupplier;
      this.regions := regions;
      Repr := {this} + clientSupplier.Repr;
    }

    method GetClient(region: Option<string>) returns (res: Result<AmazonKeyManagementServiceClient>)
      requires Valid()
      ensures Valid()
      // Verify this behavior with the spec. TODO: https://github.com/awslabs/aws-encryption-sdk-dafny/issues/272
      // Only add a post condition around failures, since the GetClient call could return a success or failure
      ensures region.None? ==> res.Failure?
      ensures region.Some? && region.get in regions ==> res.Failure?
      decreases Repr
    {
      // In order to exclude regions, make sure our given region string exists and is not a member of the regions to exclude
      if region.None? {
        return Result.Failure("ExcludeRegionsClientSupplier GetClient requires a region");
      } else if (region.Some? && region.get in regions) {
        var failure := "Given region " + region.get + " is in regions maintained by ExcludeRegionsClientSupplier";
        return Result.Failure(failure);
      }
      var resClient := clientSupplier.GetClient(region);
      return resClient;
    }
  }

  class BaseClientSupplier extends AWSKMSClientSupplier {
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }

    constructor()
      ensures Valid() && fresh(Repr)
    {
      Repr := {this};
    }

    // Since this is the base client supplier, this just calls the extern GetClient method
    method GetClient(region: Option<string>) returns (res: Result<AmazonKeyManagementServiceClient>)
      requires Valid()
      ensures Valid()
      decreases Repr
    {
      // Since this is the base client supplier, this obtains the extern client
      var resClient := GetDefaultAWSKMSServiceClientExtern(region);
      return resClient;
    }
  }
}
