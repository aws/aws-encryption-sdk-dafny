include "../SDK/Materials.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"

module {:extern "KMSUtils"} KMSUtils {
  import Mat = Materials
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
  /*

  function method CreateValidFormatCMKAlias(y: string): (s: string)
    requires UTF8.IsASCIIString(y)
    requires |"alias/"| + |y| <= 2048 && '/' !in y
    ensures s == "alias/" + y && ValidFormatCMKAlias(s)
  {
    var s := "alias/" + y;
    ghost var delim := '/';
    calc {
      Split(s, delim);
    ==  { AboutSplit0(s, delim, "alias"); }
      ["alias"] + Split(s[6..], delim);
    ==  { assert s[6..] == y; }
      ["alias"] + Split(y, delim);
    ==  { AboutSplit1(y, delim); }
      ["alias"] + [y];
    ==  // concatenation of singleton sequences
      ["alias", y];
    }
    s
  }

  //TODO: CreateValidFormatCMKAliasARN
  function method CreateValidFormatCMKKeyARN(aws: string, region: string, account_id: string, y: string): (s: CustomerMasterKey)
    requires UTF8.IsASCIIString(aws) && UTF8.IsASCIIString(region) && UTF8.IsASCIIString(account_id) && UTF8.IsASCIIString(y)
    requires ':' !in aws && ':' !in region && ':' !in account_id && ':' !in y
    requires |aws| <= 10 && |region| <= 1000 && |account_id| == 12 && |y| == 36
    ensures s == "arn:" + aws + ":kms:" + region + ":" + account_id + ":key/" + y
    ensures ValidFormatCMKKeyARN(s)
  {
    var arn, kms, key := "arn", "kms", "key";
    var keyY := key + "/" + y;
    var s := arn + ":" + aws + ":" + kms + ":" + region + ":" + account_id + ":" + keyY;
    // To prove ValidFormatCMKKeyARN, we need to prove three things. The first is easy:
    assert 0 < |s| <= 2048;
    // The second is the most complicated, because we need to reason about what
    // Split(s, ':') returns. If you're reading this line by line, you may want to
    // look at the third part next, because its ingredients are the same as in the second
    // part, but simpler.
    ghost var components := Split(s, ':');
    assert components == [arn, aws, kms, region, account_id, keyY] by {
      var delim := ':';
      calc {
        Split(s, delim);
      ==  { AboutSplit0(s, delim, arn); }
        [arn] + Split(s[|arn|+1..], delim);
      ==  { AboutSplit0(s[|arn|+1..], delim, aws); }
        [arn] + ([aws] + Split(s[|arn|+1..][|aws|+1..], delim));
      ==  { assert s[|arn|+1..][|aws|+1..] == s[|arn|+|aws|+2..]; }
        [arn, aws] + Split(s[|arn|+|aws|+2..], delim);
      ==  { AboutSplit0(s[|arn|+|aws|+2..], delim, kms); }
        [arn, aws] + ([kms] + Split(s[|arn|+|aws|+2..][|kms|+1..], delim));
      ==  { assert s[|arn|+|aws|+2..][|kms|+1..] == s[|arn|+|aws|+|kms|+3..]; }
        [arn, aws, kms] + Split(s[|arn|+|aws|+|kms|+3..], delim);
      ==  { AboutSplit0(s[|arn|+|aws|+|kms|+3..], delim, region); }
        [arn, aws, kms] + ([region] + Split(s[|arn|+|aws|+|kms|+3..][|region|+1..], delim));
      ==  { assert s[|arn|+|aws|+|kms|+3..][|region|+1..] == s[|arn|+|aws|+|kms|+|region|+4..]; }
        [arn, aws, kms, region] + Split(s[|arn|+|aws|+|kms|+|region|+4..], delim);
      ==  { AboutSplit0(s[|arn|+|aws|+|kms|+|region|+4..], delim, account_id); }
        [arn, aws, kms, region] + ([account_id] + Split(s[|arn|+|aws|+|kms|+|region|+4..][|account_id|+1..], delim));
      ==  { assert s[|arn|+|aws|+|kms|+|region|+4..][|account_id|+1..] == s[|arn|+|aws|+|kms|+|region|+|account_id|+5..]; }
        [arn, aws, kms, region, account_id] + Split(s[|arn|+|aws|+|kms|+|region|+|account_id|+5..], delim);
      ==  { assert s[|arn|+|aws|+|kms|+|region|+|account_id|+5..] == keyY; }
        [arn, aws, kms, region, account_id] + Split(keyY, delim);
      ==  { AboutSplit1(keyY, delim); }
        [arn, aws, kms, region, account_id] + [keyY];
      ==
        [arn, aws, kms, region, account_id, keyY];
      }
    }
    // The third is like a shorter version of the second part.
    ghost var kcomponents := Split(keyY, '/');
    assert kcomponents[0] == key by {
      AboutSplit0(keyY, '/', key);
    }
    // And after proving those three things, we have proved that s satisfies ValidFormatCMKKeyARN,
    // so we are ready to return it:
    s
  }
  */
  
  type GrantToken = s: string | 0 < |s| <= 8192 witness "witness"

  trait ClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<KMSClient>)
  }

  class DefaultClientSupplier extends ClientSupplier {
    constructor() {}
    method {:extern} GetClient(region: Option<string>) returns (res: Result<KMSClient>)
  }

  datatype ResponseMetadata = ResponseMetadata(metadata: map<string, string>, requestID: string)

  type HttpStatusCode = int //FIXME: Restrict this

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, numberOfBytes: int32)
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

  datatype EncryptRequest = EncryptRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, plaintext: seq<uint8>)
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

  datatype DecryptRequest = DecryptRequest(ciphertextBlob: seq<uint8>, encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>)
  {
    predicate Valid() {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype DecryptResponse = DecryptResponse(contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)

  // https://docs.aws.amazon.com/sdkfornet/v3/apidocs/items/KeyManagementService/TKeyManagementServiceClient.html
  class KMSClient {
    method {:extern} GenerateDataKey(request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
      requires request.Valid()
      //TODO mmtj: Should this be marked as modifying all of request's fields?

	method {:extern} Encrypt(request: EncryptRequest) returns (res: Result<EncryptResponse>)
      requires request.Valid()
      //TODO mmtj: Should this be marked as modifying all of request's fields?

    method {:extern} Decrypt(request: DecryptRequest) returns (res: Result<DecryptResponse>)
      // TODO mmtj: Should this be marked as modifying all of request's fields?
  }
}
