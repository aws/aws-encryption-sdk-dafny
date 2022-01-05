// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../StandardLibrary/Actions.dfy"
include "../../../Generated/KeyManagementService.dfy"
include "Constants.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.AwsKmsDiscoveryKeyring"}
  MaterialProviders.AwsKmsDiscoveryKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened Actions
  import opened Constants
  import AlgorithmSuites
  import Keyring
  import Materials
  import opened KMSUtils
  import opened AwsKmsArnParsing
  import UTF8
  import KMS = Com.Amazonaws.Kms


  class AwsKmsDiscoveryKeyring
    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.5
    //= type=implication
    //# MUST implement that AWS Encryption SDK Keyring interface (../keyring-
    //# interface.md#interface)
    extends Keyring.VerifiableInterface
  {
    const client: KMS.IKeyManagementServiceClient
    const discoveryFilter: Option<Crypto.DiscoveryFilter>
    const grantTokens: GrantTokens

    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.6
    //= type=implication
    //# On initialization the caller MUST provide:
    constructor (
      client: KMS.IKeyManagementServiceClient,
      discoveryFilter: Option<Crypto.DiscoveryFilter>,
      grantTokens: GrantTokens
    )
    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.6
    //= type=implication
    //# The AWS KMS SDK client MUST NOT be null.
    requires client != null
    ensures
        && this.client          == client
        && this.discoveryFilter == discoveryFilter
        && this.grantTokens     == grantTokens
    {
      this.client          := client;
      this.discoveryFilter := discoveryFilter;
      this.grantTokens     := grantTokens;
    }

    method OnEncrypt(
      input: Crypto.OnEncryptInput
    )
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.7
      //= type=implication
      //# This function MUST fail.
      ensures res.Failure?
    {
      return Failure("Encryption is not supported with a Discovery Keyring.");
    }

    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
    //= type=implication
    //# OnDecrypt MUST take decryption materials
    //# (../structures.md#decryption-materials) and a list of encrypted data
    //# keys (../structures.md#encrypted-data-key) as input.
    method OnDecrypt(
      input: Crypto.OnDecryptInput
    )
      returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //= type=implication
      //# If the decryption materials (../structures.md#decryption-materials)
      //# already contained a valid plaintext data key, they keyring MUST fail
      //# and MUST NOT modify the decryption materials
      //# (../structures.md#decryption-materials).
      ensures
        input.materials.plaintextDataKey.Some?
      ==>
        && res.Failure?

      ensures
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && input.materials.plaintextDataKey.None?
        && res.Success?
        && maybeStringifiedEncCtx.Success?
      ==>
        && res.value.materials.plaintextDataKey.Some?
        && exists edk: Crypto.EncryptedDataKey, awsKmsKey: string
        |
          && edk in input.encryptedDataKeys
        ::
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          && KMS.IsValid_KeyIdType(awsKmsKey)
          && var request := KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob :=  edk.ciphertext,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          );
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# To attempt to decrypt a particular encrypted data key
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
          //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.
          && client.DecryptCalledWith(
            //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
            //= type=implication
            //# When calling AWS KMS Decrypt
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            request)
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# If the response does satisfy these requirements then OnDecrypt MUST
          //# do the following with the response:
          && DecryptResult(
            awsKmsKey,
            res.value.materials.plaintextDataKey.value)
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# *  The length of the response's "Plaintext" MUST equal the key
          //# derivation input length (../algorithm-suites.md#key-derivation-
          //# input-length) specified by the algorithm suite (../algorithm-
          //# suites.md) included in the input decryption materials
          //# (../structures.md#decryption-materials).
          && Materials.DecryptionMaterialsWithPlaintextDataKey(res.value.materials)
    {

      var materials := input.materials;
      var encryptedDataKeys := input.encryptedDataKeys;
      var suite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials), 
        "Keyring received decryption materials that already contain a plaintext data key.");

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var edkFilterTransform : OnDecryptEncryptedDataKeyFilterMap := new OnDecryptEncryptedDataKeyFilterMap(discoveryFilter);
      var edksToAttempt, parts :- Actions.FlatMapWithResult(edkFilterTransform, encryptedDataKeys);

      forall i
      | 0 <= i < |parts|
      ensures
        && edkFilterTransform.Ensures(encryptedDataKeys[i], Success(parts[i]))
        && 1 >= |parts[i]|
        && |encryptedDataKeys| == |parts|
        && edksToAttempt == Seq.Flatten(parts)
        && |encryptedDataKeys| >= |edksToAttempt|
        && multiset(parts[i]) <= multiset(edksToAttempt)
        && multiset(edksToAttempt) <= multiset(Seq.Flatten(parts))
        && forall helper: AwsKmsEdk
          | helper in parts[i]
          ::
            && helper in edksToAttempt
            && helper.edk == encryptedDataKeys[i]
            && helper.arn.resource.resourceType == "key"
      {
        if |parts| < |edksToAttempt| {
          Seq.LemmaFlattenLengthLeMul(parts, 1);
          Seq.LemmaFlattenAndFlattenReverseAreEquivalent(parts);
          assert |parts| * 1 >= |Seq.Flatten(parts)|;
        }

        forall helper: AwsKmsEdk
        | helper in parts[i]
        ensures
          && helper in edksToAttempt
          && helper.edk == encryptedDataKeys[i]
          && helper.arn.resource.resourceType == "key"
        {
          LemmaMultisetSubMembership(parts[i], edksToAttempt);
        }
      }

      forall helper: AwsKmsEdk
      | helper in edksToAttempt
      ensures
        && helper.edk in encryptedDataKeys
        && helper.arn.resource.resourceType == "key"
      {
        LemmaFlattenMembership(parts, edksToAttempt);
        assert helper in Seq.Flatten(parts);
      }

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# For each encrypted data key in the filtered set, one at a time, the
      //# OnDecrypt MUST attempt to decrypt the data key.
      var decryptAction: EncryptedDataKeyDecryptor := new EncryptedDataKeyDecryptor(
        materials,
        client,
        grantTokens
      );
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# If the response does not satisfy these requirements then an error
      //# is collected and the next encrypted data key in the filtered set MUST
      //# be attempted.
      var outcome := Actions.ReduceToSuccess(
        decryptAction,
        edksToAttempt
      );

      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);
      return match outcome {
        case Success(mat) =>
          assert exists helper: AwsKmsEdk | helper in edksToAttempt
          ::
            && var awsKmsKey := helper.arn.arnLiteral;
            
            && var suite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);  
            && helper.edk in encryptedDataKeys;
            /*&& helper.arn.resource.resourceType == "key"
            && helper.edk.keyProviderId == PROVIDER_ID
            && decryptAction.Ensures(helper, Success(mat))
            && KMS.IsValid_CiphertextType(helper.edk.ciphertext)
            && KMS.IsValid_KeyIdType(awsKmsKey)
            && var request := KMS.DecryptRequest(
              KeyId := Option.Some(awsKmsKey),
              CiphertextBlob :=  helper.edk.ciphertext,
              EncryptionContext := Option.Some(stringifiedEncCtx),
              GrantTokens := Option.Some(grantTokens),
              EncryptionAlgorithm := Option.None()
            );
            && client.DecryptCalledWith(request)
            && var response := KMS.DecryptResponse(
              KeyId := Some(awsKmsKey),
              Plaintext := mat.plaintextDataKey,
              EncryptionAlgorithm := Some(KMS.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT) // TODO, don't hardcode
            );
            && client.DecryptSucceededWith(request, response);
            */
          Success(Crypto.OnDecryptOutput(materials := mat))

        //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
        //# If OnDecrypt fails to successfully decrypt any encrypted data key
        //# (../structures.md#encrypted-data-key), then it MUST yield an error that
        //# includes all collected errors.
        case Failure(errors) =>
          if |errors| == 0 then
            Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.")
          else
            var concatString := (s, a) => a + "\n" + s;
            var error := Seq.FoldRight(
              concatString,
              errors,
              "Unable to decrypt data key:\n"
            );
            Failure(error)
      };
    }
  }

  /*
   * A class responsible for filtering Encrypted Data Keys based on whether they match
   * an MRK-aware keyring's configuration. Specifically, this class knows how to filter
   * based on region and discovery filters.
   *
   * TODO: Explain somewhere (here or maybe elsewhere) our motivation beyond our approach
   * here. We're adding a lot of complexity to the code, which gives us good value (like
   * being able to prove more things), but this comes at a cost. And the concept/approach
   * are complicated enough that variable and method names alone are not enough.
   */
  class OnDecryptEncryptedDataKeyFilterMap
    extends ActionWithResult<
      Crypto.EncryptedDataKey,
      AwsKmsEdk,
      string
    >
  {
    const discoveryFilter: Option<Crypto.DiscoveryFilter>
    constructor(
      discoveryFilter: Option<Crypto.DiscoveryFilter>
    )
      ensures
        && this.discoveryFilter == discoveryFilter
    {
      this.discoveryFilter := discoveryFilter;
    }

    predicate Ensures(
      edk: Crypto.EncryptedDataKey,
      res: Result<AwsKmsEdk, string>
    ) {
      && res.Success?
      ==>
        && var matchingEdk := res.value;
        && matchingEdk.edk.keyProviderId == PROVIDER_ID
        && matchingEdk.edk == edk
        && matchingEdk.arn.resource.resourceType == "key"
        && DiscoveryMatch(matchingEdk.arn, discoveryFilter)
    }

    method Invoke(edk: Crypto.EncryptedDataKey
    )
      returns (res: Result<AwsKmsEdk, string>)
      ensures Ensures(edk, res)
    {

      if edk.keyProviderId != PROVIDER_ID {
        return Failure("TODO");
      }

      // The Keyring produces UTF8 providerInfo.
      // If an `aws-kms` encrypted data key's providerInfo is not UTF8
      // this is an error, not simply an EDK to filter out.
      :- Need(UTF8.ValidUTF8Seq(edk.keyProviderInfo), "Invalid AWS KMS encoding, provider info is not UTF8.");

      var keyId :- UTF8.Decode(edk.keyProviderInfo);
      var arn :- ParseAwsKmsArn(keyId);

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
      //# OnDecrypt MUST fail.
      :- Need(arn.resource.resourceType == "key", "Only AWS KMS Keys supported");

      if !DiscoveryMatch(arn, discoveryFilter) {
        return Failure("TODO");
      }

      return Success(AwsKmsEdk(edk, arn));
    }
  }

  class EncryptedDataKeyDecryptor
    extends ActionWithResult<
      AwsKmsEdk,
      Materials.SealedDecryptionMaterials,
      string>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: KMS.IKeyManagementServiceClient
    const grantTokens: GrantTokens

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: KMS.IKeyManagementServiceClient,
      grantTokens: GrantTokens
    )
      ensures
      && this.materials == materials
      && this.client == client
      && this.grantTokens == grantTokens
    {
      this.materials := materials;
      this.client := client;
      this.grantTokens := grantTokens;
    }

    predicate Ensures(
      helper: AwsKmsEdk,
      res: Result<Materials.SealedDecryptionMaterials, string>
    ) {
        res.Success?
      ==>
        && KMS.IsValid_CiphertextType(helper.edk.ciphertext)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var awsKmsKey := helper.arn.ToString();
        && KMS.IsValid_KeyIdType(awsKmsKey)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && var request := KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob := helper.edk.ciphertext,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          );
        && client.DecryptCalledWith(request)
        && exists returnedKeyId, returnedEncryptionAlgorithm ::
          && var response := KMS.DecryptResponse(
            KeyId := returnedKeyId,
            Plaintext := Option.Some(res.value.plaintextDataKey.value),
            EncryptionAlgorithm := returnedEncryptionAlgorithm
          );
          && client.DecryptSucceededWith(request, response)
    }

    method Invoke(
      helper: AwsKmsEdk
    )
      returns (res: Result<Materials.SealedDecryptionMaterials, string>)
      ensures Ensures(helper, res)
    {

      var awsKmsKey := helper.arn.ToString();

      :- Need(KMS.IsValid_CiphertextType(helper.edk.ciphertext), "Ciphertext length invalid");
      :- Need(KMS.IsValid_KeyIdType(awsKmsKey), "KMS key arn invalid");
      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);

      var decryptRequest := KMS.DecryptRequest(
        KeyId := Option.Some(awsKmsKey),
        CiphertextBlob := helper.edk.ciphertext,
        EncryptionContext := Option.Some(stringifiedEncCtx),
        GrantTokens := Option.Some(grantTokens),
        EncryptionAlgorithm := Option.None()
      );

      var maybeDecryptResponse := client.Decrypt(decryptRequest);
      if maybeDecryptResponse.Failure? {
        return Failure(KMS.CastKeyManagementServiceErrorToString(maybeDecryptResponse.error));
      }


      var decryptResponse := maybeDecryptResponse.value;
      var algId := AlgorithmSuites.GetSuite(materials.algorithmSuiteId);
      :- Need(
        //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
        //# *  The "KeyId" field in the response MUST equal the AWS KMS ARN from
        //# the provider info
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && algId.encrypt.keyLength as int == |decryptResponse.Plaintext.value|
        , "Invalid response from KMS Decrypt");

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value);
      return Success(result);
    }
  }

  function method DiscoveryMatch(
    arn: AwsKmsArn,
    discoveryFilter: Option<Crypto.DiscoveryFilter>
  ):
    (res: bool)
    ensures
      && discoveryFilter.Some?
      && res
    ==>
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //= type=implication
      //# *  If a discovery filter is configured, its partition and the
      //# provider info partition MUST match.
      && discoveryFilter.value.partition == arn.partition
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //= type=implication
      //# *  If a discovery filter is configured, its set of accounts MUST
      //# contain the provider info account.
      && discoveryFilter.value.accountIds <= [arn.account]
  {
    && match discoveryFilter {
      case Some(filter) =>
        && filter.partition == arn.partition
        && filter.accountIds <= [arn.account]
      case None() => true
    }
  }

  lemma LemmaMultisetSubMembership<T>(a: seq<T>, b: seq<T>)
    requires multiset(a) <= multiset(b)
    ensures forall i | i in a :: i in b
  {
    if |a| == 0 {
    } else {
      assert multiset([Seq.First(a)]) <= multiset(b);
      assert Seq.First(a) in b;
      assert a == [Seq.First(a)] + a[1..];
      LemmaMultisetSubMembership(a[1..], b);
    }
  }

  lemma LemmaFlattenMembership<T>(parts: seq<seq<T>>, flat: seq<T>)
    requires Seq.Flatten(parts) == flat
    ensures forall index
    | 0 <= index < |parts|
    :: multiset(parts[index]) <= multiset(flat)
    ensures multiset(Seq.Flatten(parts)) == multiset(flat)
    ensures forall part | part in parts
    :: (forall i | i in part :: i in flat)
    ensures forall i | i in flat
    :: (exists part | part in parts :: i in part)
  {
    if |parts| == 0 {
    } else {
      assert multiset(Seq.First(parts)) <= multiset(flat);
      assert parts == [Seq.First(parts)] + parts[1..];
      assert flat ==  Seq.First(parts) + Seq.Flatten(parts[1..]);
      LemmaFlattenMembership(parts[1..], Seq.Flatten(parts[1..]));
    }
  }

  // TODO: copied from AwsKmsMrkAwareSymmetricKeyring
  //    use ValidUTF8Bytes everywhere in business logic, so that this (and usages in implementation/preconditions) can be removed
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

}
