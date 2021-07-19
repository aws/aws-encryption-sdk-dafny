// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./Defs.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/KMSUtils.dfy"
include "../../Util/UTF8.dfy"

module {:extern "KMSKeyringDef"} KMSKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import KeyringDefs
  import Mat = Materials
  import KMSUtils
  import UTF8

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s

  function method RegionFromKMSKeyARN(arn: KMSUtils.CustomerMasterKey): Result<string>
  {
    var components := Split(arn, ':');
    if 6 <= |components| && components[0] == "arn" && components[2] == "kms" then Success(components[3]) else Failure("Malformed ARN")
  }

  class KMSKeyring extends KeyringDefs.Keyring {

    const clientSupplier: KMSUtils.DafnyAWSKMSClientSupplier
    const keyIDs: seq<KMSUtils.CustomerMasterKey>
    const generator: Option<KMSUtils.CustomerMasterKey>
    const grantTokens: seq<KMSUtils.GrantToken>
    const isDiscovery: bool

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      && (|keyIDs| == 0 && generator.None? ==> isDiscovery)
      && (clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid())
    }

    constructor (clientSupplier: KMSUtils.DafnyAWSKMSClientSupplier, keyIDs: seq<KMSUtils.CustomerMasterKey>, generator: Option<KMSUtils.CustomerMasterKey>, grantTokens: seq<KMSUtils.GrantToken>)
      requires clientSupplier.Valid()
      requires 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      ensures this.clientSupplier == clientSupplier
      ensures Valid() && fresh(Repr - clientSupplier.Repr)
    {
      this.clientSupplier := clientSupplier;
      this.keyIDs         := keyIDs;
      this.generator      := generator;
      this.grantTokens    := grantTokens;

      this.isDiscovery    := |keyIDs| == 0 && generator.None?;
      Repr := {this} + clientSupplier.Repr;
    }

    method Generate(materials: Mat.ValidEncryptionMaterials) returns (res: Result<Mat.ValidEncryptionMaterials>)
      requires Valid()
      requires generator.Some?
      requires materials.plaintextDataKey.None?
      requires |materials.keyringTrace| == 0
      requires |materials.encryptedDataKeys| == 0
      requires !isDiscovery
      ensures Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && res.value.plaintextDataKey.Some?
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
      ensures res.Success? ==>
          && |res.value.keyringTrace| == |materials.keyringTrace| + 1
          && res.value.keyringTrace[|materials.keyringTrace|].flags == {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT}
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(materials.encryptionContext, grantTokens, generator.get, materials.algorithmSuiteID.KDFInputKeyLength() as int32);
      var regionRes := RegionFromKMSKeyARN(generator.get);
      var regionOpt := regionRes.ToOption();
      var client :- clientSupplier.GetClient(regionOpt);
      var generatorResponse :- KMSUtils.GenerateDataKey(client, generatorRequest);
      if !generatorResponse.IsWellFormed() {
        return Failure("Invalid response from KMS GenerateDataKey");
      }
      var providerInfo :- UTF8.Encode(generatorResponse.keyID);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure("providerInfo exceeds maximum length");
      }
      var encryptedDataKey := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, generatorResponse.ciphertextBlob);
      var keyID := generatorResponse.keyID;
      var plaintextDataKey := generatorResponse.plaintext;

      if !materials.algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
        return Failure("Invalid response from KMS GenerateDataKey: Invalid key");
      }

      var encodedGenerator :- UTF8.Encode(generator.get);
      var generateTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, encodedGenerator, {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
      var newTraceEntries := [generateTraceEntry];
      var newEncryptedDataKeys := [encryptedDataKey];
      var result := materials.WithKeys(Some(plaintextDataKey), newEncryptedDataKeys, newTraceEntries);
      return Success(result);
    }

    method OnEncrypt(materials: Mat.ValidEncryptionMaterials) returns (res: Result<Mat.ValidEncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
      ensures isDiscovery ==> res.Success? && res.value == materials
    {
      if isDiscovery {
        return Success(materials);
      } else if materials.plaintextDataKey.None? && generator.None? {
        return Failure("No plaintext datakey or generator defined");
      }

      var encryptCMKs := keyIDs;
      var resultMaterials: Mat.ValidEncryptionMaterials;
      if generator.Some? {
        if materials.plaintextDataKey.None? {
          resultMaterials :- Generate(materials);
          assert resultMaterials.plaintextDataKey.Some?;
        } else {
          resultMaterials := materials;
          encryptCMKs := encryptCMKs + [generator.get];
        }
      } else {
        resultMaterials := materials;
      }
      assert resultMaterials.plaintextDataKey.Some?;
      assert materials.plaintextDataKey.Some? ==> resultMaterials.plaintextDataKey == materials.plaintextDataKey;

      var i := 0;
      while i < |encryptCMKs|
          invariant resultMaterials.plaintextDataKey.Some?
          invariant materials.encryptionContext == resultMaterials.encryptionContext
          invariant materials.algorithmSuiteID == resultMaterials.algorithmSuiteID
          invariant materials.plaintextDataKey.Some? ==> resultMaterials.plaintextDataKey == materials.plaintextDataKey
          invariant materials.keyringTrace <= resultMaterials.keyringTrace
          invariant materials.encryptedDataKeys <= resultMaterials.encryptedDataKeys
          invariant materials.signingKey == resultMaterials.signingKey
      {
        var encryptRequest := KMSUtils.EncryptRequest(materials.encryptionContext, grantTokens, encryptCMKs[i], resultMaterials.plaintextDataKey.get);
        var regionRes := RegionFromKMSKeyARN(encryptCMKs[i]);
        var regionOpt := regionRes.ToOption();
        var client :- clientSupplier.GetClient(regionOpt);
        var encryptResponse :- KMSUtils.Encrypt(client, encryptRequest);
        if encryptResponse.IsWellFormed() {
          var providerInfo :- UTF8.Encode(encryptResponse.keyID);
          if UINT16_LIMIT <= |providerInfo| {
            return Failure("providerInfo exceeds maximum length");
          }
          var edk := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, encryptResponse.ciphertextBlob);
          var encodedEncryptCMK :- UTF8.Encode(encryptCMKs[i]);
          var encryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, encodedEncryptCMK, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
          FilterIsDistributive(resultMaterials.keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
          resultMaterials := resultMaterials.WithKeys(resultMaterials.plaintextDataKey, [edk], [encryptTraceEntry]);
        } else {
          return Failure("Invalid response from KMS Encrypt");
        }
        i := i + 1;
      }
      return Success(resultMaterials);
    }

    predicate method ShouldAttemptDecryption(providerInfo: string)
    {
      var keys := if generator.Some? then keyIDs + [generator.get] else keyIDs;
      KMSUtils.ValidFormatCMK(providerInfo)
        && (isDiscovery || providerInfo in keys)
    }

    method OnDecrypt(materials: Mat.ValidDecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.verificationKey == res.value.verificationKey
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
    {
      if |edks| == 0 || materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      var i := 0;
      while i < |edks| {
        var edk := edks[i];
        var providerInfo := Failure("Not UTF8");
        if UTF8.ValidUTF8Seq(edk.providerInfo) && edk.providerID == PROVIDER_ID {
          providerInfo := UTF8.Decode(edk.providerInfo);
        }
        if providerInfo.Success? && ShouldAttemptDecryption(providerInfo.value) {
          var decryptRequest := KMSUtils.DecryptRequest(edk.ciphertext, materials.encryptionContext, grantTokens);
          var regionRes := RegionFromKMSKeyARN(providerInfo.value);
          var regionOpt := regionRes.ToOption();
          var clientRes := clientSupplier.GetClient(regionOpt);
          if clientRes.Success? {
            var client := clientRes.value;
            var decryptResponseResult := KMSUtils.Decrypt(client, decryptRequest);
            if decryptResponseResult.Success? {
              var decryptResponse := decryptResponseResult.value;
              if (decryptResponse.keyID != providerInfo.value)
                  || !materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext) {
                return Failure("Invalid response from KMS Decrypt");
              } else {
                var decryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, edk.providerInfo, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT});
                var result := materials.WithPlaintextDataKey(decryptResponse.plaintext, [decryptTraceEntry]);
                return Success(result);
              }
            }
          }
        }
        i := i + 1;
      }
      return Success(materials);
    }
  }
}
