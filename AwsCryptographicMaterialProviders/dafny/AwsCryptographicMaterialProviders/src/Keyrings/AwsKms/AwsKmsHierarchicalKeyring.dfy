// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../CanonicalEncryptionContext.dfy"
include "../../KeyWrapping/EdkWrapping.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsUtils.dfy"
include "../../CMCs/LocalCMC.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsHierarchicalKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import opened L = LocalCMC
  import opened AlgorithmSuites
  import EdkWrapping
  import MaterialWrapping
  import CanonicalEncryptionContext
  import Keyring
  import Materials
  import Time
  import Random
  import Digest
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KeyStore = AwsCryptographyKeyStoreTypes 
  import UTF8
  import UUID
  import HKDF
  import HMAC
  import opened AESEncryption
  import Aws.Cryptography.Primitives
  
  const BRANCH_KEY_STORE_GSI := "Active-Keys";
  const BRANCH_KEY_FIELD := "enc";
  const VERSION_FIELD := "version";
  const BRANCH_KEY_IDENTIFIER_FIELD := "branch-key-id";
  
  const KEY_CONDITION_EXPRESSION := "#status = :status and #branch_key_id = :branch_key_id";
  const EXPRESSION_ATTRIBUTE_NAMES := map[
    "#status"       := "status",
    "#branch_key_id" := "branch-key-id"
  ];
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := ":status";
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE := "ACTIVE";
  const EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := ":branch_key_id";
  
  const H_WRAP_SALT_LEN: Types.PositiveInteger := 16;
  const H_WRAP_NONCE_LEN: Types.PositiveInteger := 12;
  const DERIVED_BRANCH_KEY_EXPECTED_LENGTH: Types.PositiveInteger := 32;
  const AES_256_ENC_KEY_LENGTH: int32 := 32;
  const AES_256_ENC_TAG_LENGTH: int32 := 16;
  const AES_256_ENC_IV_LENGTH: int32 := 12;
  const AES_256_ENC_ALG := Crypto.AES_GCM(
    keyLength := AES_256_ENC_KEY_LENGTH,
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
    //= type=implication
    //# MUST use an authentication tag byte of length 16.
    tagLength := AES_256_ENC_TAG_LENGTH,
    ivLength := AES_256_ENC_IV_LENGTH
  );

  const EXPECTED_EDK_CIPHERTEXT_LENGTH := 92;
  const EDK_CIPHERTEXT_VERSION_LENGTH: int32 := 16;
  const EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX := H_WRAP_SALT_LEN + H_WRAP_NONCE_LEN; 
  const EDK_CIPHERTEXT_VERSION_INDEX := EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX + EDK_CIPHERTEXT_VERSION_LENGTH;
  const EDK_CIPHERTEXT_KEY_INDEX := EDK_CIPHERTEXT_VERSION_INDEX + AES_256_ENC_KEY_LENGTH;

  // We add this axiom here because verifying the mutability of the share state of the 
  // cache. Dafny does not support concurrency and proving the state of mutable frames 
  // is complicated.  
  lemma {:axiom} verifyValidStateCache (cmc: LocalCMC) ensures cmc.ValidState()

  method getEntry(cmc: LocalCMC, input: Types.GetCacheEntryInput) returns (res: Result<Types.GetCacheEntryOutput, Types.Error>)
    requires cmc.ValidState()
    ensures cmc.ValidState()
    ensures cmc.GetCacheEntryEnsuresPublicly(input, res)
    ensures unchanged(cmc.History)
  {
    // Because of the mutable state of the cache you may not know if you have an entry in cache 
    // at this point in execution; assuming we have not modified it allows dafny to verify that it can get an entry.
    assume {:axiom} cmc.Modifies == {};
    res := cmc.GetCacheEntry(input);
  }

  method putEntry(cmc: LocalCMC, input: Types.PutCacheEntryInput) returns (res: Result<(), Types.Error>)
    requires cmc.ValidState()
    ensures cmc.ValidState()
    ensures cmc.PutCacheEntryEnsuresPublicly(input, res)
    ensures unchanged(cmc.History)
  {
    // Because of the mutable state of the cache you may not know if you have an entry in cache 
    // at this point in execution; assuming we have not modified it allows dafny to verify that it can put an entry.
    assume {:axiom} cmc.Modifies == {};
    res := cmc.PutCacheEntry(input);
  }

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#interface
  //= type=implication
  //# MUST implement the [AWS Encryption SDK Keyring interface](../keyring-interface.md#interface)
  class AwsKmsHierarchicalKeyring
    extends Keyring.VerifiableInterface
  {
    const branchKeyId: Option<string>
    const branchKeyIdSupplier: Option<Types.IBranchKeyIdSupplier>
    const keyStore: KeyStore.IKeyStoreClient
    const ttlSeconds: Types.PositiveLong
    const maxCacheSize: Types.PositiveInteger
    const grantTokens: KMS.GrantTokenList
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const cache: LocalCMC

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && keyStore.ValidState()
      && cryptoPrimitives.ValidState()
      && (branchKeyIdSupplier.Some? ==> branchKeyIdSupplier.value.ValidState())
      && keyStore.Modifies <= Modifies
      && cryptoPrimitives.Modifies <= Modifies
      && (branchKeyIdSupplier.Some? ==> branchKeyIdSupplier.value.Modifies <= Modifies)
      && History !in keyStore.Modifies
      && History !in cryptoPrimitives.Modifies
      && (branchKeyIdSupplier.Some? ==> History !in branchKeyIdSupplier.value.Modifies)
      // TODO this should eventually be Valid branch key store arn
      && (branchKeyIdSupplier.Some? || branchKeyId.Some?)
      && (branchKeyIdSupplier.None? || branchKeyId.None?)
    }

    constructor (
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide a [KeyStore](../branch-key-store.md)
      keyStore: KeyStore.IKeyStoreClient,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MAY provide a list of Grant Tokens
      grantTokens: KMS.GrantTokenList,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide either a Branch Key Identifier or a [Branch Key Supplier](#branch-key-supplier)
      branchKeyId: Option<string>,
      branchKeyIdSupplier: Option<Types.IBranchKeyIdSupplier>,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide a cache limit TTL
      ttlSeconds: Types.PositiveLong,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MAY provide a max cache size
      maxCacheSize: Types.PositiveInteger,
      cryptoPrimitives : Primitives.AtomicPrimitivesClient
    )
      requires maxCacheSize >= 1
      requires ttlSeconds >= 0
      requires keyStore.ValidState() && cryptoPrimitives.ValidState()
      requires branchKeyIdSupplier.Some? ==> branchKeyIdSupplier.value.ValidState()
      requires (branchKeyIdSupplier.Some? || branchKeyId.Some?)
      requires (branchKeyIdSupplier.None? || branchKeyId.None?)
      ensures
        && this.grantTokens  == grantTokens
        && this.keyStore     == keyStore
        && this.branchKeyIdSupplier  == branchKeyIdSupplier
        && this.ttlSeconds   == ttlSeconds
        && this.maxCacheSize == maxCacheSize
      ensures
        && ValidState()
        && fresh(this)
        && fresh(History)
        && var maybeSupplierModifies := if branchKeyIdSupplier.Some? then branchKeyIdSupplier.value.Modifies else {};
        && fresh(Modifies - keyStore.Modifies - cryptoPrimitives.Modifies - maybeSupplierModifies)
    {
      var cmc := new LocalCMC(maxCacheSize as nat, 1);

      this.keyStore            := keyStore;
      this.grantTokens         := grantTokens;
      this.branchKeyId         := branchKeyId;
      this.branchKeyIdSupplier := branchKeyIdSupplier;
      this.ttlSeconds          := ttlSeconds;
      this.maxCacheSize        := maxCacheSize;
      this.cryptoPrimitives    := cryptoPrimitives;
      this.cache               := cmc;
      
      History := new Types.IKeyringCallHistory();
      var maybeSupplierModifies := if branchKeyIdSupplier.Some? then branchKeyIdSupplier.value.Modifies else {};
      Modifies := {History} + keyStore.Modifies + cryptoPrimitives.Modifies + maybeSupplierModifies;
    }

    method GetBranchKeyId(context: Types.EncryptionContext) returns (ret: Result<string, Types.Error>)
      requires ValidState()
      modifies if branchKeyIdSupplier.Some? then branchKeyIdSupplier.value.Modifies else {}
      ensures ValidState()
      ensures branchKeyId.Some? ==> ret.Success? && ret.value == branchKeyId.value
    {
      if branchKeyId.Some? {
        return Success(branchKeyId.value);
      } else {
        var GetBranchKeyIdOut :- branchKeyIdSupplier.value.GetBranchKeyId(
          Types.GetBranchKeyIdInput(
            encryptionContext := context
          ));
        return Success(GetBranchKeyIdOut.branchKeyId);
      }
    }

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}
    
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials]
    //# (../structures.md#encryption-materials) as input.
    method {:vcs_split_on_every_assert} OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History) 
      ensures res.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          res.value.materials
        )
    {
      var materials := input.materials;
      var suite := materials.algorithmSuite;

      var branchKeyIdForEncrypt :- GetBranchKeyId(materials.encryptionContext);
      var branchKeyIdUtf8 :- UTF8.Encode(branchKeyIdForEncrypt)
        .MapFailure(WrapStringToError);
      
      var cacheId :- GetActiveCacheId(branchKeyIdForEncrypt, branchKeyIdUtf8, cryptoPrimitives);
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
      //# the hierarchical keyring MUST attempt to obtain the branch key materials
      //# by querying the backing branch keystore specified in 
      //# the [retrieve OnEncrypt branch key materials](#query-branch-keystore-onencrypt) section.
      var hierarchicalMaterials :- GetActiveHierarchicalMaterials(
        branchKeyIdForEncrypt,
        cacheId,
        keyStore
      );
      
      var branchKey := hierarchicalMaterials.branchKey;
      var branchKeyVersion := hierarchicalMaterials.branchKeyVersion;
      var branchKeyVersionAsString :- UTF8.Decode(branchKeyVersion).MapFailure(WrapStringToError);
      var branchKeyVersionAsBytes :- UUID.ToByteArray(branchKeyVersionAsString).MapFailure(WrapStringToError);

      var kmsHierarchyGenerateAndWrap := new KmsHierarchyGenerateAndWrapKeyMaterial(
        hierarchicalMaterials.branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        cryptoPrimitives
      );
      var kmsHierarchyWrap := new KmsHierarchyWrapKeyMaterial(
        hierarchicalMaterials.branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        cryptoPrimitives
      );
      
      var wrapOutput :- EdkWrapping.WrapEdkMaterial<HierarchyWrapInfo>(
        encryptionMaterials := materials,
        wrap := kmsHierarchyWrap,
        generateAndWrap := kmsHierarchyGenerateAndWrap
      );

      var symmetricSigningKeyList :=
        if wrapOutput.symmetricSigningKey.Some? then
          Some([wrapOutput.symmetricSigningKey.value])
        else
          None;

      var edk := Types.EncryptedDataKey(
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [key provider id](../structures.md#key-provider-id): MUST be UTF8 Encoded "aws-kms-hierarchy"
        keyProviderId := PROVIDER_ID_HIERARCHY,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [key provider info](../structures.md#key-provider-information): MUST be the UTF8 Encoded AWS DDB response `branch-key-id`
        keyProviderInfo := branchKeyIdUtf8,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [ciphertext](../structures.md#ciphertext): MUST be serialized as the [hierarchical keyring ciphertext](#ciphertext)
        ciphertext := wrapOutput.wrappedMaterial
      );

      if (wrapOutput.GenerateAndWrapEdkMaterialOutput?) {
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# OnEncrypt MUST append a new [encrypted data key](../structures.md#encrypted-data-key)
        //# to the encrypted data key list in the [encryption materials](../structures.md#encryption-materials)
        var result :- Materials.EncryptionMaterialAddDataKey(materials, wrapOutput.plaintextDataKey, [edk], symmetricSigningKeyList);
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      } else if (wrapOutput.WrapOnlyEdkMaterialOutput?) {
        var result :- Materials.EncryptionMaterialAddEncryptedDataKeys(
          materials,
          [edk],
          symmetricSigningKeyList
        );
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      }
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}
    method OnDecrypt'(input: Types.OnDecryptInput)
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
          res.value.materials)
    {
      var materials := input.materials;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        E("Keyring received decryption materials that already contain a plaintext data key.")
      );

      // Determine branch key ID
      var branchKeyIdForDecrypt :- GetBranchKeyId(materials.encryptionContext);
      
      var filter := new OnDecryptHierarchyEncryptedDataKeyFilter(branchKeyIdForDecrypt);
      var edksToAttempt :- FilterWithResult(filter, input.encryptedDataKeys);

      :- Need(
        0 < |edksToAttempt|,
        E("Unable to decrypt data key: No Encrypted Data Keys found to match.")
      );
    
      var decryptClosure := new DecryptSingleEncryptedDataKey(
        materials,
        keyStore,
        cryptoPrimitives,
        branchKeyIdForDecrypt,
        grantTokens,
        ttlSeconds,
        cache
      );

      var outcome, attempts := ReduceToSuccess(
        decryptClosure,
        edksToAttempt
      );

      var SealedDecryptionMaterials :- outcome
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
        //# If OnDecrypt fails to successfully decrypt any [encrypted data key]
        //# (../structures.md#encrypted-data-key), then it MUST yield an error
        //# that includes all the collected errors.
        .MapFailure(errors => Types.CollectionOfErrors( list := errors));
      
      assert decryptClosure.Ensures(Last(attempts).input, Success(SealedDecryptionMaterials), DropLast(attempts));
      return Success(Types.OnDecryptOutput(
        materials := SealedDecryptionMaterials
      ));
    }

    method GetActiveCacheId(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      returns (cacheId: Result<seq<uint8>, Types.Error>)

      requires cryptoPrimitives.ValidState()
      modifies cryptoPrimitives.Modifies
      ensures cryptoPrimitives.ValidState()
      ensures cacheId.Success? ==> |cacheId.value| == 32
    {
      :- Need(
        && UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).Success?
        && var branchKeyId := UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).value;
        && 0 <= |branchKeyId| < UINT32_LIMIT,
        E("Invalid Branch Key ID Length")
      );

      var branchKeyId := UTF8.Decode(branchKeyIdUtf8).value;
      var lenBranchKey := UInt.UInt32ToSeq(|branchKeyId| as uint32);

      var hashAlgorithm := Crypto.DigestAlgorithm.SHA_512;

      var maybeBranchKeyDigest := cryptoPrimitives
        .Digest(Crypto.DigestInput(digestAlgorithm := hashAlgorithm, message := branchKeyIdUtf8));
      var branchKeyDigest :- maybeBranchKeyDigest
        .MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      var activeUtf8 :- UTF8.Encode(EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE)
        .MapFailure(WrapStringToError);
      var identifier := lenBranchKey + branchKeyDigest + [0x00] + activeUtf8;

      var maybeCacheIdDigest := cryptoPrimitives
        .Digest(Crypto.DigestInput(digestAlgorithm := hashAlgorithm, message := identifier));
      var cacheDigest :- maybeCacheIdDigest
        .MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      :- Need(
        |cacheDigest| == Digest.Length(hashAlgorithm),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Digest generated a message not equal to the expected length.")
      );

      return Success(cacheDigest[0..32]);
    }

    method GetActiveHierarchicalMaterials(
      branchKeyId: string,
      cacheId: seq<uint8>,
      keyStore: KeyStore.IKeyStoreClient
    )
      returns (material: Result<Types.BranchKeyMaterials, Types.Error>)
      requires ValidState() 
      requires keyStore.ValidState()
      modifies keyStore.Modifies
      ensures ValidState()
      ensures keyStore.ValidState()
    {
      // call cache
      var getCacheInput := Types.GetCacheEntryInput(identifier := cacheId, bytesUsed := None);
      verifyValidStateCache(cache);
      var getCacheOutput := getEntry(cache, getCacheInput);

      if getCacheOutput.Failure? {
        var maybeRawBranchKeyMaterials := keyStore.GetActiveBranchKey(
          KeyStore.GetActiveBranchKeyInput(
            branchKeyIdentifier := branchKeyId,
            grantTokens := Some(grantTokens)
          )
        );
        var rawBranchKeyMaterials :- maybeRawBranchKeyMaterials
          .MapFailure(e => Types.AwsCryptographyKeyStore(AwsCryptographyKeyStore := e));

        var branchKeyMaterials := Types.BranchKeyMaterials(
          branchKey := rawBranchKeyMaterials.branchKey,
          branchKeyVersion := rawBranchKeyMaterials.branchKeyVersion
        );
        
        var now := Time.GetCurrent();
        :- Need(
          (now as int + ttlSeconds as int) < UInt.INT64_MAX_LIMIT,
          Types.AwsCryptographicMaterialProvidersException(message := "INT64 Overflow when putting cache entry.")
        );

        var putCacheEntryInput:= Types.PutCacheEntryInput(
          identifier := cacheId,
          materials := Types.Materials.BranchKey(branchKeyMaterials),
          creationTime := now,
          expiryTime := ttlSeconds + now,
          messagesUsed := None,
          bytesUsed := None
        );

        verifyValidStateCache(cache);
        var _ :- putEntry(cache, putCacheEntryInput);

        return Success(branchKeyMaterials);
      } else {
        :- Need(
          && getCacheOutput.value.materials.BranchKey?
          && getCacheOutput.value.materials == Types.Materials.BranchKey(getCacheOutput.value.materials.BranchKey),
          E("Invalid Material Type.")
        );
        return Success(getCacheOutput.value.materials.BranchKey);
      }
    }
  }

  method DeriveEncryptionKeyFromBranchKey(
    branchKey: seq<uint8>,
    salt: seq<uint8>,
    purpose: Option<seq<uint8>>,
    cryptoPrimitives: Primitives.AtomicPrimitivesClient
  )
    returns (output: Result<seq<uint8>, Types.Error>)

    requires cryptoPrimitives.ValidState()
    modifies cryptoPrimitives.Modifies
    ensures cryptoPrimitives.ValidState()
    ensures output.Success? ==> |output.value| == 32
    ensures |cryptoPrimitives.History.GenerateRandomBytes| == old(|cryptoPrimitives.History.GenerateRandomBytes|)
    ensures |cryptoPrimitives.History.KdfCounterMode| > 0
  {
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
    //# 3. Use a [KDF in Counter Mode with a Pseudo Random Function with HMAC SHA 256]
    //# (https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-108r1.pdf) 
    var maybeDerivedBranchKey := cryptoPrimitives.KdfCounterMode(
      Crypto.KdfCtrInput(
        digestAlgorithm := Crypto.DigestAlgorithm.SHA_256,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# - Use the branch key as the `key`.
        ikm := branchKey,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# to derive a 32 byte `derivedBranchKey`
        expectedLength := DERIVED_BRANCH_KEY_EXPECTED_LENGTH,
        // TODO: change name to label
        purpose := purpose,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# - Use the `salt` as the salt.
        nonce := Some(salt)
      )
    );
    var derivedBranchKey :- maybeDerivedBranchKey.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
    output := Success(derivedBranchKey);
  }

  function method WrappingAad(
    branchKeyId: seq<uint8>,
    branchKeyVersion: seq<uint8>,
    aad: seq<uint8>
  ): (res : seq<uint8>)
    requires UTF8.ValidUTF8Seq(branchKeyId)
    // TODO right now branchKeyVersion is stored as UTF8 Bytes in the materials
    // I either have to 1) decode the version every single time to get the raw uuid
    // or 2). store it as raw bytes in the materials so that I can encode it once per call.
  {
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping-and-unwrapping-aad
      //# To construct the AAD, the keyring MUST concatenate the following values
      // (blank line for duvet)
      //# 1. "aws-kms-hierarchy" as UTF8 Bytes
      //# 1. Value of `branch-key-id` as UTF8 Bytes
      //# 1. [version](../structures.md#branch-key-version) as Bytes
      //# 1. [encryption context](structures.md#encryption-context-1) from the input
      //# [encryption materials](../structures.md#encryption-materials) in the same format as the serialization of
      //# [message header AAD key value pairs](../../data-format/message-header.md#key-value-pairs).
      PROVIDER_ID_HIERARCHY + branchKeyId + branchKeyVersion + aad
  }
  
  class OnDecryptHierarchyEncryptedDataKeyFilter
    extends DeterministicActionWithResult<Types.EncryptedDataKey, bool, Types.Error>
  {
    const branchKeyId: string

    constructor(
      branchKeyId: string
    )
    {
      this.branchKeyId := branchKeyId;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<bool, Types.Error>
    ) {
      && (
          && res.Success?
          && res.value
        ==>
          edk.keyProviderId == PROVIDER_ID_HIERARCHY)
    }

    method Invoke(edk: Types.EncryptedDataKey)
      returns (res: Result<bool, Types.Error>)
      ensures Ensures(edk, res)
    {
      var providerInfo := edk.keyProviderInfo;
      var providerId := edk.keyProviderId;

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //# - Its provider ID MUST match the UTF8 Encoded value of “aws-kms-hierarchy”.
      if providerId != PROVIDER_ID_HIERARCHY {
        return Success(false);
      }
      
      if !UTF8.ValidUTF8Seq(providerInfo) {
        // The Keyring produces UTF8 keyProviderInfo.
        // If an `aws-kms-hierarchy` encrypted data key's keyProviderInfo is not UTF8
        // this is an error, not simply an EDK to filter out.
        return Failure(E("Invalid encoding, provider info is not UTF8."));
      }

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //# -- The deserialized key provider info MUST be UTF8 Decoded
      var branchKeyId :- UTF8.Decode(providerInfo).MapFailure(WrapStringToError);
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //#  MUST match this keyring's configured `Branch Key Identifier`.
      return Success(this.branchKeyId == branchKeyId);
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      Types.EncryptedDataKey,
      Materials.SealedDecryptionMaterials,
      Types.Error>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const keyStore: KeyStore.IKeyStoreClient
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const branchKeyId: string
    const grantTokens: KMS.GrantTokenList
    const ttlSeconds: Types.PositiveLong
    const cache: L.LocalCMC

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      keyStore: KeyStore.IKeyStoreClient,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient,
      branchKeyId: string,
      grantTokens: KMS.GrantTokenList,
      ttlSeconds: Types.PositiveLong,
      cache: L.LocalCMC
    )
      requires keyStore.ValidState() && cryptoPrimitives.ValidState()
      ensures
      && this.materials == materials
      && this.keyStore == keyStore
      && this.cryptoPrimitives == cryptoPrimitives
      && this.branchKeyId == branchKeyId
      && this.grantTokens == grantTokens
      && this.ttlSeconds == ttlSeconds
      && this.cache == cache
      ensures Invariant()
    {
      this.materials := materials;
      this.keyStore := keyStore;
      this.cryptoPrimitives := cryptoPrimitives;
      this.branchKeyId := branchKeyId;
      this.grantTokens := grantTokens;
      this.ttlSeconds := ttlSeconds;
      this.cache := cache;
      Modifies := keyStore.Modifies + cryptoPrimitives.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && keyStore.ValidState()
      && cryptoPrimitives.ValidState()
      && keyStore.Modifies + cryptoPrimitives.Modifies == Modifies
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<Materials.SealedDecryptionMaterials, Types.Error>,
      attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      // TODO look at the KMS keyring to see how we ensure that the call
      // to KMS was done correctly; this might be hard to prove once we add the cache
      // but we should be able to do it.
        res.Success?
      ==>
        && Invariant()
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)

    }
    method Invoke(
      edk: Types.EncryptedDataKey,
      ghost attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    ) returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(edk, res, attemptsState)
    {
      :- Need (
        UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException(message := "Received invalid EDK provider info for Hierarchical Keyring")
      );

      var suite := materials.algorithmSuite;
      var keyProviderId := edk.keyProviderId;
      var branchKeyIdUtf8 := edk.keyProviderInfo;
      var ciphertext := edk.ciphertext;

      var providerWrappedMaterial :- EdkWrapping.GetProviderWrappedMaterial(ciphertext, suite);
      :- Need (
        |providerWrappedMaterial| >= EDK_CIPHERTEXT_VERSION_INDEX as nat,
        Types.AwsCryptographicMaterialProvidersException(message := "Received EDK Ciphertext of incorrect length.")
      );
      var branchKeyVersionUuid := providerWrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
      var version :- UUID.FromByteArray(branchKeyVersionUuid).MapFailure(WrapStringToError);
      
      var cacheId :- GetVersionCacheId(branchKeyIdUtf8, version, cryptoPrimitives);
      var hierarchicalMaterials :- GetHierarchicalMaterialsVersion(branchKeyId, branchKeyIdUtf8, version, cacheId);
      var branchKey := hierarchicalMaterials.branchKey;
      var branchKeyVersion := hierarchicalMaterials.branchKeyVersion;
      var branchKeyVersionAsString :- UTF8.Decode(branchKeyVersion).MapFailure(WrapStringToError);
      var branchKeyVersionAsBytes :- UUID.ToByteArray(branchKeyVersionAsString).MapFailure(WrapStringToError);

      // We need to create a new client here so that we can reason about the state of the client
      // down the line. This is ok because the only state tracked is the client's history.
      var maybeCrypto := Primitives.AtomicPrimitives();
      var crypto :- maybeCrypto
        .MapFailure(e => Types.AwsCryptographyPrimitives(e));

      var kmsHierarchyUnwrap := new KmsHierarchyUnwrapKeyMaterial(
        branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        crypto
      );
      
      var unwrapOutputRes := EdkWrapping.UnwrapEdkMaterial(
          edk.ciphertext,
          materials,
          kmsHierarchyUnwrap
      ); 

      var unwrapOutput :- unwrapOutputRes; 

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, unwrapOutput.plaintextDataKey, unwrapOutput.symmetricSigningKey);
      return Success(result);
    }

     method GetVersionCacheId(
      branchKeyIdUtf8: seq<uint8>, // The branch key as Bytes
      branchKeyVersion: string,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      returns (cacheId: Result<seq<uint8>, Types.Error>)
      ensures cacheId.Success? ==> |cacheId.value| == 32
    {
      :- Need(
        && UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).Success?
        && var branchKeyId := UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).value;
        && 0 <= |branchKeyId| < UINT32_LIMIT,
        E("Invalid Branch Key ID Length")
      );

      var branchKeyId := UTF8.Decode(branchKeyIdUtf8).value;
      var lenBranchKey := UInt.UInt32ToSeq(|branchKeyId| as uint32);
      :- Need(
        UTF8.IsASCIIString(branchKeyVersion),
        E("Unable to represent as an ASCII string.")
      );
      var versionBytes := UTF8.EncodeAscii(branchKeyVersion);

      var identifier := lenBranchKey + branchKeyIdUtf8 + [0x00 as uint8] + versionBytes;
      var identifierDigestInput := Crypto.DigestInput(
        digestAlgorithm := Crypto.DigestAlgorithm.SHA_512, message := identifier
      );
      var maybeCacheDigest := Digest.Digest(identifierDigestInput);
      var cacheDigest :- maybeCacheDigest.MapFailure(e => Types.AwsCryptographyPrimitives(e));

      return Success(cacheDigest[0..32]);
    }

    method GetHierarchicalMaterialsVersion(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>,
      version: string,
      cacheId: seq<uint8>
    )
      returns (material: Result<Types.BranchKeyMaterials, Types.Error>)
      // TODO Define valid HierarchicalMaterials such that we can ensure they are correct
      requires Invariant()
      requires keyStore.ValidState()
      modifies keyStore.Modifies
      ensures keyStore.ValidState()
    {
      // call cache
      var getCacheInput := Types.GetCacheEntryInput(identifier := cacheId, bytesUsed := None);
      verifyValidStateCache(cache);
      var getCacheOutput := getEntry(cache, getCacheInput);

      if getCacheOutput.Failure? {
        var maybeRawBranchKeyMaterials := keyStore.GetBranchKeyVersion(
          KeyStore.GetBranchKeyVersionInput(
            branchKeyIdentifier := branchKeyId,
            branchKeyVersion := version,
            grantTokens := Some(grantTokens)
          )
        );
        
        var rawBranchKeyMaterials :- maybeRawBranchKeyMaterials
          .MapFailure(e => Types.AwsCryptographyKeyStore(AwsCryptographyKeyStore := e));

        var branchKeyMaterials := Types.BranchKeyMaterials(
          branchKey := rawBranchKeyMaterials.branchKey,
          branchKeyVersion := rawBranchKeyMaterials.branchKeyVersion
        );
        
        var now := Time.GetCurrent();
        :- Need(
          (now as int + ttlSeconds as int) < UInt.INT64_MAX_LIMIT,
          Types.AwsCryptographicMaterialProvidersException(message := "INT64 Overflow when putting cache entry.")
        );

        var putCacheEntryInput:= Types.PutCacheEntryInput(
          identifier := cacheId,
          materials := Types.Materials.BranchKey(branchKeyMaterials),
          creationTime := now,
          expiryTime := ttlSeconds + now,
          messagesUsed := None,
          bytesUsed := None
        );

        verifyValidStateCache(cache);
        var _ :- putEntry(cache, putCacheEntryInput);

        return Success(branchKeyMaterials);
      } else {
        :- Need(
          && getCacheOutput.value.materials.BranchKey?
          && getCacheOutput.value.materials == Types.Materials.BranchKey(getCacheOutput.value.materials.BranchKey),
          E("Invalid Material Type.")
        );
        return Success(getCacheOutput.value.materials.BranchKey);
      }
    }
  }

  datatype HierarchyUnwrapInfo = HierarchyUnwrapInfo()
  datatype HierarchyWrapInfo = HierarchyWrapInfo()
  
  class KmsHierarchyUnwrapKeyMaterial
    extends MaterialWrapping.UnwrapMaterial<HierarchyUnwrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
     constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8: UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
        && this.branchKey == branchKey
        && this.branchKeyIdUtf8 == branchKeyIdUtf8
        && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
        && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.UnwrapInput,
      res: Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && |input.wrappedMaterial| == EXPECTED_EDK_CIPHERTEXT_LENGTH
        && |crypto.History.AESDecrypt| > 0
        && Seq.Last(crypto.History.AESDecrypt).output.Success?
        && var AESDecryptInput := Seq.Last(crypto.History.AESDecrypt).input;
        && var AESDecryptOutput := Seq.Last(crypto.History.AESDecrypt).output.value;
        && var wrappedMaterial := input.wrappedMaterial;
        && var aad := input.encryptionContext;
        && var salt := wrappedMaterial[0..H_WRAP_SALT_LEN];
        && var iv := wrappedMaterial[H_WRAP_SALT_LEN..EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX];
        && var branchKeyVersionUuid := wrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
        && var wrappedKey := wrappedMaterial[EDK_CIPHERTEXT_VERSION_INDEX..EDK_CIPHERTEXT_KEY_INDEX];
        && var authTag := wrappedMaterial[EDK_CIPHERTEXT_KEY_INDEX..];
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && var serializedEC := CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).value;
        && var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);
        // Since we can't call a method here in the predicate we can't derive the key here
        // but we can make sure that the rest of the construction is correct.
        && AESDecryptInput.encAlg == AES_256_ENC_ALG
        && AESDecryptInput.cipherTxt == wrappedKey
        && AESDecryptInput.authTag == authTag
        && AESDecryptInput.iv == iv 
        && AESDecryptInput.aad == wrappingAad
        && AESDecryptOutput == res.value.unwrappedMaterial
    }
    
    method Invoke(
      input: MaterialWrapping.UnwrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==>
        |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      var suite := input.algorithmSuite;
      var wrappedMaterial := input.wrappedMaterial;
      var aad := input.encryptionContext;
      
      :- Need (
        // Salt = 16, IV = 12, Version = 16, Encrypted Key = 32, Authentication Tag = 16
        |wrappedMaterial| == EXPECTED_EDK_CIPHERTEXT_LENGTH,
        Types.AwsCryptographicMaterialProvidersException(message := "Received EDK Ciphertext of incorrect length.")
      );

      var salt := wrappedMaterial[0..H_WRAP_SALT_LEN];
      var iv := wrappedMaterial[H_WRAP_SALT_LEN..EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX];
      var branchKeyVersionUuid := wrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
      var wrappedKey := wrappedMaterial[EDK_CIPHERTEXT_VERSION_INDEX..EDK_CIPHERTEXT_KEY_INDEX];
      var authTag := wrappedMaterial[EDK_CIPHERTEXT_KEY_INDEX..];

      var serializedEC :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
      var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);
      var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
        branchKey,
        salt,
        Some(PROVIDER_ID_HIERARCHY),
        crypto
      );

      var maybeUnwrappedPdk :=  crypto.AESDecrypt(
        Crypto.AESDecryptInput(
          encAlg := AES_256_ENC_ALG,
          key := derivedBranchKey,
          cipherTxt := wrappedKey,
          authTag := authTag, 
          iv := iv,
          aad := wrappingAad
        )
      );
      var unwrappedPdk :- maybeUnwrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      :- Need(
        |unwrappedPdk| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat,
        E("Invalid Key Length")
      );

      var output := MaterialWrapping.UnwrapOutput(
        unwrappedMaterial := unwrappedPdk,
        unwrapInfo := HierarchyUnwrapInfo()
      );

      return Success(output);
    }
  }

  class KmsHierarchyGenerateAndWrapKeyMaterial
    extends MaterialWrapping.GenerateAndWrapMaterial<HierarchyWrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
    constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8 : UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
      && this.branchKey == branchKey
      && this.branchKeyIdUtf8 == branchKeyIdUtf8
      && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
      && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.GenerateAndWrapInput,
      res: Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) 
      reads Modifies
      decreases Modifies
    {
      res.Success?
        ==>
      && Invariant()
    }

    method Invoke(
      input: MaterialWrapping.GenerateAndWrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.plaintextMaterial| == input.algorithmSuite.encrypt.AES_GCM.keyLength as nat
    {
      var suite := input.algorithmSuite;
      var pdkResult := crypto
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(suite)));
      var pdk :- pdkResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e)); 

      var wrap := new KmsHierarchyWrapKeyMaterial(
        branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        crypto
      );

      var wrapOutput: MaterialWrapping.WrapOutput<HierarchyWrapInfo> :- wrap.Invoke(
        MaterialWrapping.WrapInput(
          plaintextMaterial := pdk,
          algorithmSuite := input.algorithmSuite,
          encryptionContext := input.encryptionContext
        ), []);

      var output := MaterialWrapping.GenerateAndWrapOutput(
        plaintextMaterial := pdk,
        wrappedMaterial := wrapOutput.wrappedMaterial,
        wrapInfo := HierarchyWrapInfo()
      );
      return Success(output);
    }

  }

  class KmsHierarchyWrapKeyMaterial
    extends MaterialWrapping.WrapMaterial<HierarchyWrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
    constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8 : UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
      && this.branchKey == branchKey
      && this.branchKeyIdUtf8 == branchKeyIdUtf8
      && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
      && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.WrapInput,
      res: Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && (
        res.Success?
          ==>
        && Invariant()
        && 0 < |crypto.History.AESEncrypt|
        && Seq.Last(crypto.History.AESEncrypt).output.Success?
        && var AESEncryptInput := Seq.Last(crypto.History.AESEncrypt).input;
        && var AESEncryptOutput := Seq.Last(crypto.History.AESEncrypt).output.value;
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && var serializedEC := CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
        && var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC.value);
        && AESEncryptInput.encAlg == AES_256_ENC_ALG 
        && AESEncryptInput.msg == input.plaintextMaterial
        && AESEncryptInput.aad == wrappingAad
        && |res.value.wrappedMaterial| > |AESEncryptOutput.cipherText| + |AESEncryptOutput.authTag|
        && res.value.wrapInfo == HierarchyWrapInfo()
      )
    }

    method Invoke(
      input: MaterialWrapping.WrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      {
        var suite := input.algorithmSuite;

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# The hierarchical keyring MUST:
        // (blank line for duvet)
        //# 1. Generate a 16 byte random salt using a secure source of randomness
        //# 1. Generate a 12 byte random iv using a secure source of randomness
        var maybeNonceSalt := crypto.GenerateRandomBytes(
          Crypto.GenerateRandomBytesInput(length := H_WRAP_SALT_LEN + H_WRAP_NONCE_LEN)
        );
        var saltAndNonce :- maybeNonceSalt.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
        
        assert |crypto.History.GenerateRandomBytes| == old(|crypto.History.GenerateRandomBytes|) + 1;
        assert |saltAndNonce| == (H_WRAP_NONCE_LEN + H_WRAP_SALT_LEN) as int;
        
        var salt := saltAndNonce[0..H_WRAP_SALT_LEN];
        var nonce := saltAndNonce[H_WRAP_SALT_LEN..];
        
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping-and-unwrapping-aad
        //# the keyring MUST include the following values as part of the AAD for the AES Encrypt/Decrypt calls.
        // (blank line for duvet)
        // To construct the AAD, the keyring MUST concatante the following values
        // (blank line for duvet)
        //# 1. "aws-kms-hierarchy" as UTF8 Bytes
        //# 1. Value of `branch-key-id` as UTF8 Bytes
        //# 1. [version](../structures.md#branch-key-version) as Bytes
        //# 1. [encryption context](structures.md#encryption-context-1) from the input
        //#   [encryption materials](../structures.md#encryption-materials) in the same format as the serialization of
        //#   [message header AAD key value pairs](../../data-format/message-header.md#key-value-pairs).
        var serializedEC :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
        var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);

        var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
          branchKey,
          salt,
          Some(PROVIDER_ID_HIERARCHY),
          crypto
        );

        var maybeWrappedPdk := crypto.AESEncrypt(
          Crypto.AESEncryptInput(
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# 1. Encrypt a plaintext data key with the `derivedBranchKey` using
            //# `AES-GCM-256` with the following inputs:
            encAlg := AES_256_ENC_ALG,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the derived `IV` as the AES-GCM IV.  
            iv := nonce,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the `derivedBranchKey` as the AES-GCM cipher key.
            key := derivedBranchKey,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the plain text data key that will be wrapped by the `derivedBranchKey` as the AES-GCM message.
            msg := input.plaintextMaterial,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# - MUST use the serialized [AAD](#branch-key-wrapping-and-unwrapping-aad) as the AES-GCM AAD.
            aad := wrappingAad
          )
        );
        var wrappedPdk :- maybeWrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

        var output := MaterialWrapping.WrapOutput(
          wrappedMaterial := salt + nonce +  branchKeyVersionAsBytes + wrappedPdk.cipherText + wrappedPdk.authTag,
          wrapInfo := HierarchyWrapInfo()
        );
        return Success(output);
      }
  }

  function method SerializeEDKCiphertext(encOutput: Crypto.AESEncryptOutput): (ciphertext: seq<uint8>) {
    encOutput.cipherText + encOutput.authTag
  }

  function method E(s : string) : Types.Error {
    Types.AwsCryptographicMaterialProvidersException(message := s)
  }

}
