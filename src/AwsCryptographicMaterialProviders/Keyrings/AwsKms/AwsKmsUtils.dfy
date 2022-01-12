// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../Generated/KeyManagementService.dfy"
include "../../../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "AwsKmsUtils"} AwsKmsUtils {
  import opened Wrappers
  import KMS = Com.Amazonaws.Kms
  import Aws.Crypto
  import UTF8

  // TODO: These EncryptionContext methods can be removed once we move to UTF8 strings
  function method StringifyEncryptionContext(utf8EncCtx: Crypto.EncryptionContext):
    (res: Result<KMS.EncryptionContextType, string>)
  {
    if |utf8EncCtx| == 0 then Success(map[])
    else
      var stringifyResults: map<UTF8.ValidUTF8Bytes, Result<(string, string), string>> :=
        map utf8Key | utf8Key in utf8EncCtx.Keys :: utf8Key := StringifyEncryptionContextPair(utf8Key, utf8EncCtx[utf8Key]);
      if exists r | r in stringifyResults.Values :: r.Failure?
        then Failure("Encryption context contains invalid UTF8")
      else
        assert forall r | r in stringifyResults.Values :: r.Success?;
        // TODO state that UTF8.Decode is injective so we don't need this
        var stringKeysUnique := forall k, k' | k in stringifyResults && k' in stringifyResults
          :: k != k' ==> stringifyResults[k].value.0 != stringifyResults[k'].value.0;
        if !stringKeysUnique then Failure("Encryption context keys are not unique")  // this should never happen...
        else Success(map r | r in stringifyResults.Values :: r.value.0 := r.value.1)
  }

  function method StringifyEncryptionContextPair(utf8Key: UTF8.ValidUTF8Bytes, utf8Value: UTF8.ValidUTF8Bytes):
    (res: Result<(string, string), string>)
    ensures (UTF8.Decode(utf8Key).Success? && UTF8.Decode(utf8Value).Success?) <==> res.Success?
  {
    var decodedKey := UTF8.Decode(utf8Key);
    var decodedValue := UTF8.Decode(utf8Value);
    if (decodedKey.Failure?) then Failure(decodedKey.error)
    else if (decodedValue.Failure?) then Failure(decodedValue.error)
    else Success((decodedKey.value, decodedValue.value))
  }

  /*
   * Determines whether the given client is configured to talk to the given region.
   *
   * Useful for MRKs where we need to check whether our client can decrypt an MRK.
   *
   * Note that not all AWS SDK implementations will support this, so some implemetations
   * may treat this as a no-op. Therefore we cannot make any guarantees in our
   * Dafny code about client and region matching; we will always need to account
   * for the case where they do not.
   */
  predicate method {:extern "RegionMatch"} RegionMatch(
    client: KMS.IKeyManagementServiceClient,
    region: string
  )

}
