// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../StandardLibrary/Actions.dfy"
include "Constants.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring"}
  MaterialProviders.AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Actions
  import opened Constants
  import AlgorithmSuites
  import Keyring
  import Materials
  import opened KMSUtils
  import UTF8

  datatype DiscoveryFilter = DiscoveryFilter(
    partition: string,
    accounts: seq<string>
  )

  class AwsKmsMrkAwareSymmetricRegionDiscoveryKeyring
    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.5
    //= type=implication
    //# MUST implement that AWS Encryption SDK Keyring interface (../keyring-
    //# interface.md#interface)
    extends Keyring.VerifiableInterface
  {
    const client: IAmazonKeyManagementService
    const discoveryFilter: Option<DiscoveryFilter>
    const grantTokens: GrantTokens
    const region: string

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
    //= type=implication
    //# On initialization the caller MUST provide:
    constructor (
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
      //= type=implication
      //# However if it can not, then it MUST
      //# NOT create the client itself.
      client: IAmazonKeyManagementService,
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
      //= type=exception
      //# It
      //# SHOULD obtain this information directly from the client as opposed to
      //# having an additional parameter.
      region: string,
      discoveryFilter: Option<DiscoveryFilter>,
      grantTokens: GrantTokens
    )
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
      //= type=implication
      //# It SHOULD have a Region parameter and
      //# SHOULD try to identify mismatched configurations.
      requires ReagionMatch(client, region)
      ensures
        && this.client          == client
        && this.region          == region
        && this.discoveryFilter == discoveryFilter
        && this.grantTokens     == grantTokens
    {
      this.client          := client;
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.6
      //# The keyring MUST know what Region the AWS KMS client is in.
      this.region          := region;
      this.discoveryFilter := discoveryFilter;
      this.grantTokens     := grantTokens;
    }

    method OnEncrypt(
      input: Crypto.OnEncryptInput
    )
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.7
      //= type=implication
      //# This function MUST fail.
      ensures res.Failure?
    {
      return Failure("Encryption is not supported with a Discovery Keyring.");
    }

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
    //= type=implication
    //# OnDecrypt MUST take decryption materials (../structures.md#decryption-
    //# materials) and a list of encrypted data keys
    //# (../structures.md#encrypted-data-key) as input.
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

      ensures
        input.materials.plaintextDataKey.Some?
      ==>
        && res.Failure?

      ensures
        && input.materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.materials.plaintextDataKey.Some?
        && exists edk: Crypto.EncryptedDataKey, awsKmsKey: string
        |
          && edk in input.encryptedDataKeys
        ::
          // && edk is EncryptedDataKey
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.keyProviderId == PROVIDER_ID
          && DecryptCalledWith(
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
          //= type=implication
          //# To attempt to decrypt a particular encrypted data key
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
          //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.
            client,
            //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
            //= type=implication
            //# When calling AWS KMS Decrypt
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            DecryptRequest(
              awsKmsKey,
              edk.ciphertext,
              input.materials.encryptionContext,
              grantTokens
            ))
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
          //= type=implication
          //# Since the response does satisfies these requirements then OnDecrypt
          //# MUST do the following with the response:
          //#*  set the plaintext data key on the decryption materials
          //#   (../structures.md#decryption-materials) as the response "Plaintext".
          && DecryptResult(
            awsKmsKey,
            res.value.materials.plaintextDataKey.value)
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
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

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var edkFilterTransform : OnDecryptMRKEncryptedDataKeyFilterMap := new OnDecryptMRKEncryptedDataKeyFilterMap(region, discoveryFilter);
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
          LemmaMultisetSubMemebership(parts[i], edksToAttempt);
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

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# For each encrypted data key in the filtered set, one at a time, the
      //# OnDecrypt MUST attempt to decrypt the data key.
      var decryptAction: DecryptSingleEncryptedDataKey := new DecryptSingleEncryptedDataKey(
        materials,
        client,
        region,
        grantTokens
      );
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# If the response does not satisfies these requirements then an error
      //# is collected and the next encrypted data key in the filtered set MUST
      //# be attempted.
      var outcome := Actions.ReduceToSuccess(
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
            && decryptAction.Ensures(helper, Success(mat));

          Success(Crypto.OnDecryptOutput(materials := mat))
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
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

  class OnDecryptMRKEncryptedDataKeyFilterMap
    extends ActionWithResult<
      Crypto.EncryptedDataKey,
      seq<AwsKmsEdkHelper>,
      string
    >
  {
    const region: string
    const discoveryFilter: Option<DiscoveryFilter>
    constructor(
      region: string,
      discoveryFilter: Option<DiscoveryFilter>
    )
      ensures
        && this.region == region
        && this.discoveryFilter == discoveryFilter
    {
      this.region := region;
      this.discoveryFilter := discoveryFilter;
    }

    predicate Ensures(
      edk: Crypto.EncryptedDataKey,
      res: Result<seq<AwsKmsEdkHelper>, string>
    ) {
      && (
        && res.Success?
      ==>
        if |res.value| == 1 then
          && var h := res.value[0];
          && h.edk.keyProviderId == PROVIDER_ID
          && h.edk == edk
          && h.arn.resource.resourceType == "key"
          && DiscoveryMatch(h.arn, discoveryFilter, region)
        else
          && |res.value| == 0
      )
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

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
      //# OnDecrypt MUST fail.
      :- Need(arn.resource.resourceType == "key", "Only AWS KMS Keys supported");

      if !DiscoveryMatch(arn, discoveryFilter, region) {
        return Success([]);
      }

      return Success([
        AwsKmsEdkHelper(edk, arn)
      ]);
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      AwsKmsEdkHelper,
      Materials.SealedDecryptionMaterials,
      string>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: IAmazonKeyManagementService
    const region : string
    const grantTokens: GrantTokens

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: IAmazonKeyManagementService,
      region : string,
      grantTokens: GrantTokens
    )
      ensures
      && this.materials == materials
      && this.client == client
      && this.region == region
      && this.grantTokens == grantTokens
    {
      this.materials := materials;
      this.client := client;
      this.region := region;
      this.grantTokens := grantTokens;
    }

    predicate Ensures(
      helper: AwsKmsEdkHelper,
      res: Result<Materials.SealedDecryptionMaterials, string>
    ) {
        res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var awsKmsKey := ToStringForRegion(helper.arn, region);
        && DecryptCalledWith(
          client,
          DecryptRequest(
            awsKmsKey,
            helper.edk.ciphertext,
            materials.encryptionContext,
            grantTokens
          )
        )
        && DecryptResult(awsKmsKey, res.value.plaintextDataKey.value)
    }

    method Invoke(
      helper: AwsKmsEdkHelper
    )
      returns (res: Result<Materials.SealedDecryptionMaterials, string>)
      ensures Ensures(helper, res)
    {

      var awsKmsKey := ToStringForRegion(helper.arn, region);

      var decryptRequest := KMSUtils.DecryptRequest(
        awsKmsKey,
        helper.edk.ciphertext,
        materials.encryptionContext,
        grantTokens
      );

      var decryptResponse :- KMSUtils.Decrypt(client, decryptRequest);

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# *  The "KeyId" field in the response MUST equal the requested "KeyId"
      :- Need(
        && decryptResponse.keyID == awsKmsKey
        , "Invalid response from KMS Decrypt");

      var result :-  Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.plaintext);
      return Success(result);
    }
  }

  function method ToStringForRegion(
    arn: AwsKmsArn,
    region: string
  ): (res: string) {
    if IsMultiRegionAwsKmsArn(arn) then
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# *  "KeyId": If the provider info's resource type is "key" and its
      //# resource is a multi-Region key then a new ARN MUST be created
      //# where the region part MUST equal the AWS KMS client region and
      //# every other part MUST equal the provider info.
      arn.ToArnString(Some(region))
    else
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //# Otherwise it MUST
      //# be the provider info.
      arn.ToString()
  }

  function method DiscoveryMatch(
    arn: AwsKmsArn,
    discoveryFilter: Option<DiscoveryFilter>,
    region:string
  ):
    (res: bool)
    ensures
      && discoveryFilter.Some?
      && res
    ==>
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //= type=implication
      //# *  If a discovery filter is configured, its partition and the
      //# provider info partition MUST match.
      && discoveryFilter.value.partition == arn.partition
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
      //= type=implication
      //# *  If a discovery filter is configured, its set of accounts MUST
      //# contain the provider info account.
      && discoveryFilter.value.accounts <= [arn.account]
    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-region-discovery-keyring.txt#2.8
    //= type=implication
    //# *  If the provider info is not identified as a multi-Region key (aws-
    //# kms-key-arn.md#identifying-an-aws-kms-multi-region-key), then the
    //# provider info's Region MUST match the AWS KMS client region.
    ensures
      && !IsMultiRegionAwsKmsArn(arn)
      && res
    ==>
      arn.region == region
  {
    && match discoveryFilter {
      case Some(filter) =>
        && filter.partition == arn.partition
        && filter.accounts <= [arn.account]
      case None() => true
    }
    && if !IsMultiRegionAwsKmsArn(arn) then
      region == arn.region
    else
      true
  }

  lemma LemmaMultisetSubMemebership<T>(a: seq<T>, b: seq<T>)
    requires multiset(a) <= multiset(b)
    ensures forall i | i in a :: i in b
  {
    if |a| == 0 {
    } else {
      assert multiset([Seq.First(a)]) <= multiset(b);
      assert Seq.First(a) in b;
      assert a == [Seq.First(a)] + a[1..];
      LemmaMultisetSubMemebership(a[1..], b);
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
