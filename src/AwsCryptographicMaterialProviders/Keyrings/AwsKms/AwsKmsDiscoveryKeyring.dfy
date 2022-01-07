// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
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
    const grantTokens: KMS.GrantTokenList

    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.6
    //= type=implication
    //# On initialization the caller MUST provide:
    constructor (
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      // This is trivially true because the type we accept in this constructor
      // is non-nullable (as evidenced by the lack of a '?')
      client: KMS.IKeyManagementServiceClient,
      discoveryFilter: Option<Crypto.DiscoveryFilter>,
      grantTokens: KMS.GrantTokenList
    )
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

      // If we could not convert the encryption context into a form understandable
      // by KMS, the result must be failure
      // TODO: add this to the spec
      ensures
        StringifyEncryptionContext(input.materials.encryptionContext).Failure?
      ==>
        res.Failure?

      ensures
        res.Success?
      ==>
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
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
          && exists returnedKeyId, returnedEncryptionAlgorithm ::
            && var response := KMS.DecryptResponse(
              KeyId := returnedKeyId,
              Plaintext := res.value.materials.plaintextDataKey,
              EncryptionAlgorithm := returnedEncryptionAlgorithm
            );
            && client.DecryptSucceededWith(request, response)
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
      var edkFilter : EncryptedDataKeyFilter := new EncryptedDataKeyFilter(discoveryFilter);
      var edksToAttempt, parts :- Actions.FlatMapWithResult(edkFilter, encryptedDataKeys);

      // We want to make sure that the set of EDKs we're about to attempt
      // to decrypt all actually came from the original set of EDKs. This is useful
      // in our post-conditions that prove we made the correct KMS calls, which
      // need to match the fields of the input EDKs to the KMS calls that were made.
      forall helper: AwsKmsEdkHelper | helper in edksToAttempt
        ensures helper.edk in encryptedDataKeys
      {
        LemmaFlattenMembership(parts, edksToAttempt);
        assert helper.edk in encryptedDataKeys;
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

      return match outcome {
        case Success(mat) =>
          assert exists helper: AwsKmsEdkHelper | helper in edksToAttempt
          ::
            && decryptAction.Ensures(helper, Success(mat));
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
   * A class responsible for both filtering and transforming Encrypted Data Keys.
   *
   * Filtering happens based on whether the input EDK is a valid AWS KMS-encrypted EDK,
   * as well as whether it matches a configured Discovery Filter.
   *
   * The class also transforms input Crypto.EncryptedDataKey to Constants.AwsKmsEdk,
   * which is primarily for convenience as the AwsKmsEdk helper class provides easier
   * access to the KMS key ARN.
   *
   * Note that our return type (seq<AwsKmsEdk>) does not technically need to be a seq,
   * since we are operating on a single EDK at a time. However, we want to be able to do
   * one of three things: 1) the EDK matches our config so we transform/return it,
   * 2) the EDK is valid but doesn't match our config, in which case we return nothing
   * and continue to the remaining EDKs, and 3) the EDK is invalid and we want to fail
   * immediately.
   */
  class EncryptedDataKeyFilter
    extends ActionWithResult<
      Crypto.EncryptedDataKey,
      seq<AwsKmsEdkHelper>,
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

    /*
     * Since this class does both transformation and filtering, we need to prove
     * that both were correct.
     *
     * For transformation, this means ensuring that the output AwsKmsEdkHelper
     * corresponds to the input EDK.
     *
     * For filtering, this means ensuring that the output AwsKmsEdkHelper
     * is of the right resource type and matches our discovery filter.
     */
    predicate Ensures(
      edk: Crypto.EncryptedDataKey,
      res: Result<seq<AwsKmsEdkHelper>, string>
    ) {
      && res.Success?
      ==>
        if |res.value| == 1 then
          && var matchingEdk := res.value[0];

          // Ensure correct transformation (edks and ARNs match)
          && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
          && var keyId := UTF8.Decode(edk.keyProviderInfo);
          && keyId.Success?
          && var arn := ParseAwsKmsArn(keyId.value);
          && arn.Success?
          && arn.value == matchingEdk.arn
          && matchingEdk.edk == edk

          // Ensure correct filtering (resource type and discovery filter match)
          && matchingEdk.edk.keyProviderId == PROVIDER_ID
          && matchingEdk.arn.resource.resourceType == "key"
          && DiscoveryMatch(matchingEdk.arn, discoveryFilter)
        else
          && |res.value| == 0
    }

    method Invoke(edk: Crypto.EncryptedDataKey
    )
      returns (res: Result<seq<AwsKmsEdkHelper>, string>)
      ensures Ensures(edk, res)
    {

      if edk.keyProviderId != PROVIDER_ID {
        return Success([]);
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
        return Success([]);
      }

      return Success([AwsKmsEdkHelper(edk, arn)]);
    }
  }

  /*
   * A class responsible for executing the actual KMS.Decrypt call on input EDKs,
   * returning decryption materials on success or an error message on failure.
   */
  class EncryptedDataKeyDecryptor
    extends ActionWithResult<
      AwsKmsEdkHelper,
      Materials.SealedDecryptionMaterials,
      string>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: KMS.IKeyManagementServiceClient
    const grantTokens: KMS.GrantTokenList

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: KMS.IKeyManagementServiceClient,
      grantTokens: KMS.GrantTokenList
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
      helper: AwsKmsEdkHelper,
      res: Result<Materials.SealedDecryptionMaterials, string>
    ) {
        res.Success?
      ==>
        && KMS.IsValid_CiphertextType(helper.edk.ciphertext)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var keyArn := helper.arn.ToString();
        && KMS.IsValid_KeyIdType(keyArn)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && var request := KMS.DecryptRequest(
            KeyId := Option.Some(keyArn),
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
      helper: AwsKmsEdkHelper
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

  /*
   * Proves that the given parts (a sequence of sequences) are
   * equivalent to the given flattened version of the parts.
   */
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
