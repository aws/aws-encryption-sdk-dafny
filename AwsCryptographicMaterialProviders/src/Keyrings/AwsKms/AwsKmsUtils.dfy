// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../../AwsArnParsing.dfy"

module AwsKmsUtils {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = Types.ComAmazonawsKmsTypes
  import AwsArnParsing
  import UTF8

  // TODO: These EncryptionContext methods can be removed once we move to UTF8 strings
  function method StringifyEncryptionContext(utf8EncCtx: Types.EncryptionContext):
    (res: Result<KMS.EncryptionContextType, Types.Error>)
  {
    if |utf8EncCtx| == 0 then Success(map[])
    else
      var stringifyResults: map<UTF8.ValidUTF8Bytes, Result<(string, string), Types.Error>> :=
        map utf8Key | utf8Key in utf8EncCtx.Keys :: utf8Key := StringifyEncryptionContextPair(utf8Key, utf8EncCtx[utf8Key]);
      if exists r | r in stringifyResults.Values :: r.Failure?
        then Failure(
          Types.AwsCryptographicMaterialProvidersException( message := "Encryption context contains invalid UTF8")
        )
      else
        assert forall r | r in stringifyResults.Values :: r.Success?;
        // TODO state that UTF8.Decode is injective so we don't need this
        var stringKeysUnique := forall k, k' | k in stringifyResults && k' in stringifyResults
          :: k != k' ==> stringifyResults[k].value.0 != stringifyResults[k'].value.0;
        if !stringKeysUnique then Failure(Types.AwsCryptographicMaterialProvidersException(
          message := "Encryption context keys are not unique"))  // this should never happen...
        else Success(map r | r in stringifyResults.Values :: r.value.0 := r.value.1)
  }

  function method StringifyEncryptionContextPair(utf8Key: UTF8.ValidUTF8Bytes, utf8Value: UTF8.ValidUTF8Bytes):
    (res: Result<(string, string), Types.Error>)
    ensures (UTF8.Decode(utf8Key).Success? && UTF8.Decode(utf8Value).Success?) <==> res.Success?
  {
    var key :- UTF8
      .Decode(utf8Key)
      .MapFailure(WrapStringToError);
    var value :- UTF8
      .Decode(utf8Value)
      .MapFailure(WrapStringToError);

    Success((key, value))
  }

  function method WrapStringToError(e: string)
    :(ret: Types.Error)
  {
    Types.AwsCryptographicMaterialProvidersException( message := e )
  }

  function method ValidateKmsKeyId(keyId: string)
    : (res: Result<(), Types.Error>)
    ensures res.Success? ==>
      && AwsArnParsing.ParseAwsKmsIdentifier(keyId).Success?
      && UTF8.IsASCIIString(keyId)
      && 0 < |keyId| <= AwsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH
  {
    var _ :- AwsArnParsing.ParseAwsKmsIdentifier(keyId).MapFailure(WrapStringToError);

    :- Need(UTF8.IsASCIIString(keyId),
      Types.AwsCryptographicMaterialProvidersException(
        message := "Key identifier is not ASCII"));
    :- Need(0 < |keyId| <= AwsArnParsing.MAX_AWS_KMS_IDENTIFIER_LENGTH,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Key identifier is too long"));
    Success(())
  }

  function method GetValidGrantTokens(grantTokens: Option<Types.GrantTokenList>)
    : (res: Result<Types.GrantTokenList, Types.Error>)
    ensures res.Success? ==>
      var tokens := res.value;
      && 0 <= |tokens| <= 10
      && forall token | token in tokens :: 1 <= |token| <= 8192
    ensures res.Success? && grantTokens.Some? ==> res.value == grantTokens.value
  {
    var tokens: Types.GrantTokenList := grantTokens.UnwrapOr([]);
    :- Need(0 <= |tokens| <= 10,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Grant token list can have no more than 10 tokens"));
    :- Need(forall token | token in tokens :: 1 <= |token| <= 8192,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Grant token list contains a grant token with invalid length"));
    Success(tokens)
  }

  function method ParseKeyNamespaceAndName(keyNamespace: string, keyName: string)
    : (res: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), Types.Error>)
    ensures res.Success? ==>
      var (namespace, name) := res.value;
      && |namespace| < UINT16_LIMIT
      && |name| < UINT16_LIMIT
  {
    var namespace :- UTF8.Encode(keyNamespace)
      .MapFailure(e => Types.AwsCryptographicMaterialProvidersException(
        message := "Key namespace could not be UTF8-encoded" + e ));
    :- Need(|namespace| < UINT16_LIMIT,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Key namespace too long"));

    var name :- UTF8.Encode(keyName)
      .MapFailure(e => Types.AwsCryptographicMaterialProvidersException(
        message := "Key name could not be UTF8-encoded" + e ));
    :- Need(|name| < UINT16_LIMIT,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Key name too long"));

    Success((namespace, name))
  }

  function method ValidateDiscoveryFilter(filter: Types.DiscoveryFilter)
    : (res: Result<(), Types.Error>)
    ensures res.Success? ==>
      && |filter.accountIds| > 0
      && (forall accountId | accountId in filter.accountIds :: |accountId| > 0)
      && |filter.partition| > 0
  {
    :- Need(|filter.accountIds| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Discovery filter must have at least one account ID"));
    :- Need(forall accountId | accountId in filter.accountIds :: |accountId| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Discovery filter account IDs cannot be blank"));
    :- Need(|filter.partition| > 0,
      Types.AwsCryptographicMaterialProvidersException(
        message := "Discovery filter partition cannot be blank"));
    Success(())
  }
}
