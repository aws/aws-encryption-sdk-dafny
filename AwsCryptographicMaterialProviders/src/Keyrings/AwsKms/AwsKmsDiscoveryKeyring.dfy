// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../../src/StandardLibrary/Actions.dfy"
include "Constants.dfy"
include "AwsKmsUtils.dfy"
include "AwsKmsArnParsing.dfy"
include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsDiscoveryKeyring {
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
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = ComAmazonawsKmsTypes
  import opened AwsKmsUtils

  class AwsKmsDiscoveryKeyring
    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.5
    //= type=implication
    //# MUST implement that AWS Encryption SDK Keyring interface (../keyring-
    //# interface.md#interface)
    extends Keyring.VerifiableInterface
  {
    const client: KMS.IKeyManagementServiceClient
    const discoveryFilter: Option<Types.DiscoveryFilter>
    const grantTokens: KMS.GrantTokenList

    predicate ValidState()
    ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && client.ValidState()
      && client.Modifies <= Modifies
      && History !in client.Modifies
    }

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
      discoveryFilter: Option<Types.DiscoveryFilter>,
      grantTokens: KMS.GrantTokenList
    )
    requires client.ValidState()
    ensures
        && this.client          == client
        && this.discoveryFilter == discoveryFilter
        && this.grantTokens     == grantTokens
    ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - client.Modifies)
    {
      this.client          := client;
      this.discoveryFilter := discoveryFilter;
      this.grantTokens     := grantTokens;

      History := new Types.IKeyringCallHistory();
      Modifies := {History} + client.Modifies;
    }

    predicate OnEncryptEnsuresPublicly (
      input: Types.OnEncryptInput ,
      output: Result<Types.OnEncryptOutput, Types.Error> )
      {
        true
      }

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
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.7
      //= type=implication
      //# This function MUST fail.
      ensures output.Failure?
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(
        message := "Encryption is not supported with a Discovery Keyring."));
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> )
    {
      true
    }

    //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
    //= type=implication
    //# OnDecrypt MUST take decryption materials
    //# (../structures.md#decryption-materials) and a list of encrypted data
    //# keys (../structures.md#encrypted-data-key) as input.
    method OnDecrypt'(
      input: Types.OnDecryptInput
    )
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
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

      // The primary purpose of this post-condition is to make assertions about how
      // we called KMS; specifically, that we constructed a response to KMS
      // using one of the input EDKs, and correctly used the values from KMS's
      // response in our own output.
      ensures
        res.Success?
      ==>
        && var stringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext).Extract();
        && 0 < |client.History.Decrypt|
        && Seq.Last(client.History.Decrypt).output.Success?
        && exists edk: Types.EncryptedDataKey, awsKmsKey: string
        |
          && edk in input.encryptedDataKeys
        ::
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          && KMS.IsValid_KeyIdType(awsKmsKey)

          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# *  The length of the response's "Plaintext" MUST equal the key
          //# derivation input length (../algorithm-suites.md#key-derivation-
          //# input-length) specified by the algorithm suite (../algorithm-
          //# suites.md) included in the input decryption materials
          //# (../structures.md#decryption-materials).
          && Materials.DecryptionMaterialsWithPlaintextDataKey(res.value.materials)

          && var request := KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob :=  edk.ciphertext,
            EncryptionContext := Option.Some(stringifiedEncCtx),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          );
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# To attempt to decrypt a particular encrypted data key
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
          //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.
          && Seq.Last(client.History.Decrypt).input
            //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
            //= type=implication
            //# When calling AWS KMS Decrypt
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            == request
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# If the response does satisfy these requirements then OnDecrypt MUST
          //# do the following with the response:
          && (exists returnedKeyId, returnedEncryptionAlgorithm ::
            && var response := KMS.DecryptResponse(
              KeyId := returnedKeyId,
              Plaintext := res.value.materials.plaintextDataKey,
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

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var edkFilter : AwsKmsEncryptedDataKeyFilter := new AwsKmsEncryptedDataKeyFilter(discoveryFilter);
      var matchingEdks :- Actions.FilterWithResult(edkFilter, encryptedDataKeys);

      // Next we convert the input Types.EncrypteDataKeys into Constant.AwsKmsEdkHelpers,
      // which makes them slightly easier to work with.
      var edkTransform : AwsKmsEncryptedDataKeyTransformer := new AwsKmsEncryptedDataKeyTransformer();
      var edksToAttempt, parts :- Actions.DeterministicFlatMapWithResult(edkTransform, matchingEdks);

      :- Need(0 < |edksToAttempt|,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unable to decrypt data key: No Encrypted Data Keys found to match."));

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
      var decryptAction: AwsKmsEncryptedDataKeyDecryptor := new AwsKmsEncryptedDataKeyDecryptor(
        materials,
        client,
        grantTokens
      );
      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# If the response does not satisfy these requirements then an error
      //# is collected and the next encrypted data key in the filtered set MUST
      //# be attempted.
      var outcome, attempts := Actions.ReduceToSuccess(
        decryptAction,
        edksToAttempt
      );

      return match outcome {
        case Success(mat) =>
          assert exists helper: AwsKmsEdkHelper | helper in edksToAttempt
          ::
            && helper.edk in encryptedDataKeys
            && decryptAction.Ensures(helper, Success(mat), attempts);
          Success(Types.OnDecryptOutput(materials := mat))

        //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
        //# If OnDecrypt fails to successfully decrypt any encrypted data key
        //# (../structures.md#encrypted-data-key), then it MUST yield an error that
        //# includes all collected errors.
        case Failure(errors) => Failure(Types.Collection(list := errors))
      };
    }
  }

  /*
   * A class responsible for filtering Encrypted Data Keys to include only ones
   * that were encrypted by AWS KMS and match a provided discovery filter.
   */
  class AwsKmsEncryptedDataKeyFilter
    extends DeterministicActionWithResult<
      Types.EncryptedDataKey,
      bool,
      Types.Error
    >
  {
    const discoveryFilter: Option<Types.DiscoveryFilter>
    constructor(
      discoveryFilter: Option<Types.DiscoveryFilter>
    )
      ensures
        && this.discoveryFilter == discoveryFilter
    {
      this.discoveryFilter := discoveryFilter;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<bool, Types.Error>
    ) {
      && res.Success?
      && res.value
      ==>

        // Pull out some values so we can compare them
        && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
        && var keyId := UTF8.Decode(edk.keyProviderInfo);
        && keyId.Success?
        && var arn := ParseAwsKmsArn(keyId.value);
        && arn.Success?

        && edk.keyProviderId == PROVIDER_ID
        && arn.value.resource.resourceType == "key"
        && DiscoveryMatch(arn.value, discoveryFilter)
    }

    method Invoke(edk: Types.EncryptedDataKey)
      returns (output: Result<bool, Types.Error>)
      ensures Ensures(edk, output)
    {
      // The Keyring produces UTF8 providerInfo.
      // If an `aws-kms` encrypted data key's providerInfo is not UTF8
      // this is an error, not simply an EDK to filter out.
      :- Need(UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid AWS KMS encoding, provider info is not UTF8."));

      var keyId :- UTF8.Decode(edk.keyProviderInfo).MapFailure(WrapStringToError);
      var arn :- ParseAwsKmsArn(keyId).MapFailure(WrapStringToError);

      //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
      //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
      //# OnDecrypt MUST fail.
      :- Need(arn.resource.resourceType == "key",
        Types.AwsCryptographicMaterialProvidersException(
          message := "Only AWS KMS Keys supported"));

      if edk.keyProviderId != PROVIDER_ID {
        return Success(false);
      }

      if !DiscoveryMatch(arn, discoveryFilter) {
        return Success(false);
      }

      return Success(true);
    }
  }

  /*
   * Responsible for transforming Encrypted Data Keys which have
   * been generated by AWS KMS into a more usable format (specifically
   * the output is of type AwsKmsEdkHelper, which provides easier access
   * to the KMS ARN).
   *
   * Note that this transform will fail if it is given EDKs which were not
   * encrypted by AWS KMS or have invalid values, so it is recommended that
   * input first be run through AwsKmsEncryptedDataKeyFilter to filter out
   * incorrect EDKs.
   *
   * Our return type (seq<AwsKmsEdk>) does not technically need to be a seq,
   * since we are operating on a single EDK at a time. However, I can't seem
   * to use Actions.MapWithResult because it wants the return type to have
   * an auto-init and I'm not sure what that would look like for AwsKmsEdkHelper.
   * So I'm using this with Actions.FlatMapWithResult instead, which does not
   * have the same issue issue, but it requires returns of type seq.
   * This may be fixed by https://github.com/dafny-lang/dafny/issues/1553.
   */
  class AwsKmsEncryptedDataKeyTransformer
    extends DeterministicActionWithResult<
      Types.EncryptedDataKey,
      seq<AwsKmsEdkHelper>,
      Types.Error
    >
  {
    constructor() {}

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<seq<AwsKmsEdkHelper>, Types.Error>
    ) {
      && res.Success?
      ==>
        && |res.value| == 1
        && var matchingEdk := res.value[0];

        // Ensure correct transformation (edks and ARNs match)
        && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
        && var keyId := UTF8.Decode(edk.keyProviderInfo);
        && keyId.Success?
        && var arn := ParseAwsKmsArn(keyId.value);
        && arn.Success?
        && arn.value == matchingEdk.arn
        && matchingEdk.edk == edk
    }

    method Invoke(edk: Types.EncryptedDataKey
    )
      returns (res: Result<seq<AwsKmsEdkHelper>, Types.Error>)
      ensures Ensures(edk, res)
    {
      // This transform only works if the given EDK is a valid AWS KMS-generated EDK
      // Ideally we would add these as pre-conditions on the method, but we're extending the
      // ActionWithResult trait which does not have pre-conditions and we cannot make our
      // implementation more restrictive.
      // TODO: consider updating Actions.ActionWithResult to have an implementable "Requires"
      // method in the same way it has an "Ensures" method
      :- Need(edk.keyProviderId == PROVIDER_ID,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Encrypted data key was not generated by KMS"));
      :- Need(UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid AWS KMS encoding, provider info is not UTF8."));

      var keyId :- UTF8.Decode(edk.keyProviderInfo).MapFailure(WrapStringToError);
      var arn :- ParseAwsKmsArn(keyId).MapFailure(WrapStringToError);

      return Success([AwsKmsEdkHelper(edk, arn)]);
    }
  }

  /*
   * Responsible for executing the actual KMS.Decrypt call on input EDKs,
   * returning decryption materials on success or an error message on failure.
   */
  class AwsKmsEncryptedDataKeyDecryptor
    extends ActionWithResult<
      AwsKmsEdkHelper,
      Materials.SealedDecryptionMaterials,
      Types.Error>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: KMS.IKeyManagementServiceClient
    const grantTokens: KMS.GrantTokenList

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: KMS.IKeyManagementServiceClient,
      grantTokens: KMS.GrantTokenList
    )
      requires client.ValidState()
      ensures
      && this.materials == materials
      && this.client == client
      && this.grantTokens == grantTokens
      ensures Invariant()
    {
      this.materials := materials;
      this.client := client;
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
      attemptsState: seq<ActionInvoke<AwsKmsEdkHelper, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
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
        && var keyArn := helper.arn.ToString();
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
          //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
          //= type=implication
          //# *  The "KeyId" field in the response MUST equal the AWS KMS ARN from
          //# the provider info
          && returnedKeyId == Option.Some(keyArn)
    }

    method Invoke(
      helper: AwsKmsEdkHelper,
      ghost attemptsState: seq<ActionInvoke<AwsKmsEdkHelper, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(helper, res, attemptsState)
    {

      var awsKmsKey := helper.arn.ToString();

      :- Need(KMS.IsValid_CiphertextType(helper.edk.ciphertext),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Ciphertext length invalid"));
      :- Need(KMS.IsValid_KeyIdType(awsKmsKey),
        Types.AwsCryptographicMaterialProvidersException(
          message := "KMS key arn invalid"));
      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);

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
      :- Need(
        //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
        //# *  The "KeyId" field in the response MUST equal the AWS KMS ARN from
        //# the provider info
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && AlgorithmSuites.GetEncryptKeyLength(algId) as nat == |decryptResponse.Plaintext.value|
        , Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from KMS Decrypt"));

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value);
      return Success(result);
    }
  }

  function method DiscoveryMatch(
    arn: AwsKmsArn,
    discoveryFilter: Option<Types.DiscoveryFilter>
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
}
