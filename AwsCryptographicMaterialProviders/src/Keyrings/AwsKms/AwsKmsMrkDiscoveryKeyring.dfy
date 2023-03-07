// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Constants.dfy"
include "AwsKmsUtils.dfy"
include "../../AwsArnParsing.dfy"

module AwsKmsMrkDiscoveryKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
   import opened AwsArnParsing
  import opened Actions
  import opened Constants
  import AlgorithmSuites
  import Keyring
  import Materials
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = Types.ComAmazonawsKmsTypes
  import opened AwsKmsUtils

  class AwsKmsMrkDiscoveryKeyring
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#interface
    //= type=implication
    //# MUST implement that [AWS Encryption SDK Keyring interface](../keyring-
    //# interface.md#interface)
    extends Keyring.VerifiableInterface
  {
    const client: KMS.IKeyManagementServiceClient
    const discoveryFilter: Option<Types.DiscoveryFilter>
    const grantTokens: KMS.GrantTokenList
    const region: string

    predicate ValidState()
    ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && client.ValidState()
      && client.Modifies <= Modifies
      && History !in client.Modifies
    }

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#initialization
    //= type=implication
    //# On initialization the keyring MUST accept the following parameters:
    constructor (
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#initialization
      //= type=implication
      //# They keyring MUST fail initialization if any required parameters are
      //# missing or null.
      // Dafny does not allow null values for parameters unless explicitly told to (Option or '?')
      client: KMS.IKeyManagementServiceClient,
      region: string,
      discoveryFilter: Option<Types.DiscoveryFilter>,
      grantTokens: KMS.GrantTokenList
    )
      requires client.ValidState()
      ensures
        && this.client          == client
        && this.region          == region
        && this.discoveryFilter == discoveryFilter
        && this.grantTokens     == grantTokens
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - client.Modifies)
    {
      this.client          := client;
      this.region          := region;
      this.discoveryFilter := discoveryFilter;
      this.grantTokens     := grantTokens;

      History := new Types.IKeyringCallHistory();
      Modifies := {History} + client.Modifies;
    }

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}

    method OnEncrypt'(
      input: Types.OnEncryptInput
    )
      returns (output: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#onencrypt
      //= type=implication
      //# This function MUST fail.
      ensures output.Failure?
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(
        message := "Encryption is not supported with a Discovery Keyring."));
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
    //= type=implication
    //# OnDecrypt MUST take [decryption materials](../structures.md#decryption-
    //# materials) and a list of [encrypted data keys]
    //# (../structures.md#encrypted-data-key) as input.
    method OnDecrypt'(
      input: Types.OnDecryptInput
    )
      returns (output: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures output.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          output.value.materials
        )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //= type=implication
      //# If the [decryption materials](../structures.md#decryption-materials)
      //# already contained a valid plaintext data key, they keyring MUST fail
      //# and MUST NOT modify the [decryption materials]
      //# (../structures.md#decryption-materials).
      ensures
        input.materials.plaintextDataKey.Some?
      ==>
        && output.Failure?

      // If we could not convert the encryption context into a form understandable
      // by KMS, the result must be failure
      // TODO: add this to the spec
      ensures
        StringifyEncryptionContext(input.materials.encryptionContext).Failure?
      ==>
        output.Failure?

      ensures
        && output.Success?
      ==>
        && var stringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext).Extract();
        && output.value.materials.plaintextDataKey.Some?
        && 0 < |client.History.Decrypt|
        && Seq.Last(client.History.Decrypt).output.Success?
        && exists edk: Types.EncryptedDataKey, awsKmsKey: string
        |
          && edk in input.encryptedDataKeys
        ::
          // && edk is EncryptedDataKey
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
          //= type=implication
          //# - Its provider ID MUST exactly match the value “aws-kms”.
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          && KMS.IsValid_KeyIdType(awsKmsKey)
          && var request := KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob :=  edk.ciphertext,
            EncryptionContext := Option.Some(stringifiedEncCtx),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          );

          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
          //= type=implication
          //# - The length of the response’s `Plaintext` MUST equal the [key
          //# derivation input length](../algorithm-suites.md#key-derivation-
          //# input-length) specified by the [algorithm suite](../algorithm-
          //# suites.md) included in the input [decryption materials]
          //# (../structures.md#decryption-materials).
          && Materials.DecryptionMaterialsWithPlaintextDataKey(output.value.materials)

          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
          //= type=implication
          //# To attempt to decrypt a particular [encrypted data key]
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call [AWS KMS
          //# Decrypt](https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.
          && Seq.Last(client.History.Decrypt).input
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
            //= type=implication
            //# When calling [AWS KMS Decrypt]
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            == request
            
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
          //= type=implication
          //# Since the response does satisfies these requirements then OnDecrypt
          //# MUST do the following with the response:
          //#*  set the plaintext data key on the [decryption materials]
          //#   (../structures.md#decryption-materials) as the response `Plaintext`.
          && (exists returnedKeyId, returnedEncryptionAlgorithm ::
            && var response := KMS.DecryptResponse(
              KeyId := returnedKeyId,
              Plaintext := output.value.materials.plaintextDataKey,
              EncryptionAlgorithm := returnedEncryptionAlgorithm
            );
            && Seq.Last(client.History.Decrypt).output.value == response)
    {

      var materials := input.materials;
      var encryptedDataKeys := input.encryptedDataKeys;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring received decryption materials that already contain a plaintext data key."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring’s configuration.
      var edkFilterTransform : AwsKmsEncryptedDataKeyFilterTransform := new AwsKmsEncryptedDataKeyFilterTransform(region, discoveryFilter);
      var edksToAttempt, parts :- Actions.DeterministicFlatMapWithResult(edkFilterTransform, encryptedDataKeys);

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
        && forall helper: AwsKmsEdkHelper
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

        forall helper: AwsKmsEdkHelper
        | helper in parts[i]
        ensures
          && helper in edksToAttempt
          && helper.edk == encryptedDataKeys[i]
          && helper.arn.resource.resourceType == "key"
        {
          LemmaMultisetSubMembership(parts[i], edksToAttempt);
        }
      }

      forall helper: AwsKmsEdkHelper
      | helper in edksToAttempt
      ensures
        && helper.edk in encryptedDataKeys
        && helper.arn.resource.resourceType == "key"
      {
        LemmaFlattenMembership(parts, edksToAttempt);
        assert helper in Seq.Flatten(parts);
      }

      :- Need(0 < |edksToAttempt|,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unable to decrypt data key: No Encrypted Data Keys found to match."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# For each encrypted data key in the filtered set, one at a time, the
      //# OnDecrypt MUST attempt to decrypt the data key.
      var decryptAction: AwsKmsEncryptedDataKeyDecryptor := new AwsKmsEncryptedDataKeyDecryptor(
        materials,
        client,
        region,
        grantTokens
      );
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# If the response does not satisfies these requirements then an error
      //# is collected and the next encrypted data key in the filtered set MUST
      //# be attempted.
      var outcome, attempts := Actions.ReduceToSuccess(
        decryptAction,
        edksToAttempt
      );

      return match outcome {
        case Success(mat) =>
          assert exists helper: AwsKmsEdkHelper
          | helper in edksToAttempt
          ::
            && helper.edk in encryptedDataKeys
            && helper.arn.resource.resourceType == "key"
            && decryptAction.Ensures(helper, Success(mat), attempts);

          Success(Types.OnDecryptOutput(materials := mat))
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
        //# If OnDecrypt fails to successfully decrypt any [encrypted data key]
        //# (../structures.md#encrypted-data-key), then it MUST yield an error that
        //# includes all collected errors.
        case Failure(errors) => Failure(Types.CollectionOfErrors(list := errors))
      };
    }
  }

  class AwsKmsEncryptedDataKeyFilterTransform
    extends DeterministicActionWithResult<
      Types.EncryptedDataKey,
      seq<AwsKmsEdkHelper>,
      Types.Error
    >
  {
    const region: string
    const discoveryFilter: Option<Types.DiscoveryFilter>
    constructor(
      region: string,
      discoveryFilter: Option<Types.DiscoveryFilter>
    )
      ensures
        && this.region == region
        && this.discoveryFilter == discoveryFilter
    {
      this.region := region;
      this.discoveryFilter := discoveryFilter;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<seq<AwsKmsEdkHelper>, Types.Error>
    ) {
      && res.Success?
      ==>
        if |res.value| == 1 then
          && var h := res.value[0];
          && h.edk.keyProviderId == PROVIDER_ID
          && UTF8.ValidUTF8Seq(h.edk.keyProviderInfo)
          && h.edk == edk
          && h.arn.resource.resourceType == "key"
          && DiscoveryMatch(h.arn, discoveryFilter, region)
        else
          && |res.value| == 0
    }

    method Invoke(edk: Types.EncryptedDataKey)
      returns (res: Result<seq<AwsKmsEdkHelper>, Types.Error>)
      ensures Ensures(edk, res)
    {

      if edk.keyProviderId != PROVIDER_ID {
        return Success([]);
      }

      // The Keyring produces UTF8 providerInfo.
      // If an `aws-kms` encrypted data key's providerInfo is not UTF8
      // this is an error, not simply an EDK to filter out.
      :- Need(UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException( message := "Invalid AWS KMS encoding, provider info is not UTF8."));

      var keyId :- UTF8.Decode(edk.keyProviderInfo)
        .MapFailure(e => Types.AwsCryptographicMaterialProvidersException( message := e ));
      var arn :- ParseAwsKmsArn(keyId)
        .MapFailure(e => Types.AwsCryptographicMaterialProvidersException( message := e ));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# - The provider info MUST be a [valid AWS KMS ARN](aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of `key` or
      //# OnDecrypt MUST fail.
      :- Need(arn.resource.resourceType == "key",
        Types.AwsCryptographicMaterialProvidersException( message := "Only AWS KMS Keys supported"));

      if !DiscoveryMatch(arn, discoveryFilter, region) {
        return Success([]);
      }

      return Success([
        AwsKmsEdkHelper(edk, arn)
      ]);
    }
  }

  /*
   * Responsible for executing the actual KMS.Decrypt call on input EDKs,
   * returning decryption materials on success or an error message on failure.
   *
   * TODO: we may want to combine this with the very similar class in
   * AwsKmsDiscoveryKeyring.dfy. However they're not *perfectly* identical
   * because they handle ARNs differently. We can probably abstract that away,
   * but in the interest of small changes, I'm leaving that for a separate PR.
   */
  class AwsKmsEncryptedDataKeyDecryptor
    extends ActionWithResult<
      AwsKmsEdkHelper,
      Materials.SealedDecryptionMaterials,
      Types.Error>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: KMS.IKeyManagementServiceClient
    const region : string
    const grantTokens: KMS.GrantTokenList

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: KMS.IKeyManagementServiceClient,
      region : string,
      grantTokens: KMS.GrantTokenList
    )
      requires client.ValidState()
      ensures
      && this.materials == materials
      && this.client == client
      && this.region == region
      && this.grantTokens == grantTokens
      ensures Invariant()
    {
      this.materials := materials;
      this.client := client;
      this.region := region;
      this.grantTokens := grantTokens;
      Modifies := client.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && client.ValidState()
      && client.Modifies == Modifies
    }

    predicate Ensures(
      helper: AwsKmsEdkHelper,
      res: Result<Materials.SealedDecryptionMaterials, Types.Error>,
      attempts : seq<ActionInvoke<AwsKmsEdkHelper, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && res.Success?
      ==>
        && Invariant()
        // Confirm that the materials we're about to output are a valid transition
        // from the input materials
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)

        // Confirm that all our input values were valid
        && var keyArn := ToStringForRegion(helper.arn, region);
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && KMS.IsValid_CiphertextType(helper.edk.ciphertext)
        && KMS.IsValid_KeyIdType(keyArn)
        && maybeStringifiedEncCtx.Success?

        && 0 < |client.History.Decrypt|
        // Confirm that we called KMS in the right way and correctly returned the values
        // it gave us
        && KMS.DecryptRequest(
            KeyId := Option.Some(keyArn),
            CiphertextBlob := helper.edk.ciphertext,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          ) == Seq.Last(client.History.Decrypt).input
        && Seq.Last(client.History.Decrypt).output.Success?
        && exists returnedKeyId, returnedEncryptionAlgorithm ::
          && var response := KMS.DecryptResponse(
            KeyId := returnedKeyId,
            Plaintext := Option.Some(res.value.plaintextDataKey.value),
            EncryptionAlgorithm := returnedEncryptionAlgorithm
          );
          && Seq.Last(client.History.Decrypt).output.value == response
    }

    method Invoke(
      helper: AwsKmsEdkHelper,
      ghost attemptsState: seq<ActionInvoke<AwsKmsEdkHelper, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      decreases Modifies
      modifies Modifies
      ensures Invariant()
      ensures Ensures(helper, res, attemptsState)
    {
      var awsKmsKey := ToStringForRegion(helper.arn, region);
      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);

      :- Need(KMS.IsValid_CiphertextType(helper.edk.ciphertext), 
        Types.AwsCryptographicMaterialProvidersException( message := "Ciphertext length invalid"));
      :- Need(KMS.IsValid_KeyIdType(awsKmsKey),
        Types.AwsCryptographicMaterialProvidersException( message := "KMS key arn invalid"));

      var decryptRequest := KMS.DecryptRequest(
        KeyId := Option.Some(awsKmsKey),
        CiphertextBlob := helper.edk.ciphertext,
        EncryptionContext := Option.Some(stringifiedEncCtx),
        GrantTokens := Option.Some(grantTokens),
        EncryptionAlgorithm := Option.None()
      );

      var maybeDecryptResponse := client.Decrypt(decryptRequest);
      var decryptResponse :- maybeDecryptResponse
        .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

      var algId := materials.algorithmSuite;
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# - The `KeyId` field in the response MUST equal the requested `KeyId`
      :- Need(
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && AlgorithmSuites.GetEncryptKeyLength(algId) as nat == |decryptResponse.Plaintext.value|
        , Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from KMS Decrypt"));

      // TODO add support
      :- Need(materials.algorithmSuite.symmetricSignature.None?,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Symmetric Signatures not yet implemented."));

      var result :-  Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value, None);
      return Success(result);
    }
  }

  /*
   * Given an ARN and a region, returns a string version of the ARN, with support for MRKs
   * (that is, if the ARN is an MRK, we replace its region portion with the provided region).
   */
  function method ToStringForRegion(
    arn: AwsKmsArn,
    region: string
  ): (res: string) {
    if IsMultiRegionAwsKmsArn(arn) then
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# - `KeyId`: If the provider info’s resource type is `key` and its
      //# resource is a multi-Region key then a new ARN MUST be created
      //# where the region part MUST equal the AWS KMS client region and
      //# every other part MUST equal the provider info.
      arn.ToArnString(Some(region))
    else
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //# Otherwise it MUST
      //# be the provider info.
      arn.ToString()
  }

  /*
   * Determines whether the given KMS Key ARN matches the given discovery filter and region,
   * with support for MRKs (that is, if a given ARN refers to an MRK, it will be considered to
   * "match" regardless of the region in the ARN).
   */
  function method DiscoveryMatch(
    arn: AwsKmsArn,
    discoveryFilter: Option<Types.DiscoveryFilter>,
    region: string
  ):
    (res: bool)
    ensures
      && discoveryFilter.Some?
      && res
    ==>
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //= type=implication
      //# - If a discovery filter is configured, its partition and the
      //# provider info partition MUST match.
      && discoveryFilter.value.partition == arn.partition
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
      //= type=implication
      //# - If a discovery filter is configured, its set of accounts MUST
      //# contain the provider info account.
      && arn.account in discoveryFilter.value.accountIds
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-discovery-keyring.md#ondecrypt
    //= type=implication
    //# - If the provider info is not [identified as a multi-Region key](aws-
    //# kms-key-arn.md#identifying-an-aws-kms-multi-region-key), then the
    //# provider info’sRegion MUST match the AWS KMS client region.
    ensures
      && !IsMultiRegionAwsKmsArn(arn)
      && res
    ==>
      arn.region == region
  {
    && match discoveryFilter {
      case Some(filter) =>
        && filter.partition == arn.partition
        && arn.account in filter.accountIds
      case None() => true
    }
    && if !IsMultiRegionAwsKmsArn(arn) then
      region == arn.region
    else
      true
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

}
