include "./Defs.dfy"
include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/KMSUtils.dfy"

module KMSKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KeyringDefs
  import Mat = Materials
  import KMSUtils

  class KMSKeyring extends KeyringDefs.Keyring {

    const clientSupplier: string -> KMSUtils.KMSClient
    const keyIDs: seq<string>
    const generator: Option<string>
    const grantTokens: seq<string>
    const isDiscovery: bool

    /*
    * Does not correctly handle alias strings.
    * Also it could probably be a function
    */
    method RegionFromKMSKeyARN(arn: string) returns (res: Result<string>) {
      // arn:aws:kms:us-east-1:999999999999:key/01234567-89ab-cdef-fedc-ba9876543210
      if ':' !in arn {
        return Failure("Malformed ARN");
      }

      var start, end := 0, 0;
      end := StringFind(arn, ':', start);
      if arn[start..end] != "arn" {
        return Failure("Malformed ARN");
      }
      start := end + 1;

      if ':' !in arn[start..] {
        return Failure("Malformed ARN");
      }

      end := StringFind(arn, ':', start);
      start := end + 1;

      if ':' !in arn[start..] {
        return Failure("Malformed ARN");
      }

      end := StringFind(arn, ':', start);
      if arn[start..end] != "kms" {
        return Failure("Malformed ARN");
      }
      start := end + 1;

      if ':' !in arn[start..] {
        return Failure("Malformed ARN");
      }

      end := StringFind(arn, ':', start);
      return Success(arn[start..end]);
    }

    predicate Valid() reads this, Repr {
      Repr == {this} &&
      |keyIDs| == 0 && generator.None? ==> isDiscovery
    }

    constructor(clientSupplier: string -> KMSUtils.KMSClient, keyIDs: seq<string>, generator: Option<string>, grantTokens: seq<string>)
      ensures Valid()
    {
      this.clientSupplier := clientSupplier;
      this.keyIDs         := keyIDs;
      this.generator      := generator;
      this.grantTokens    := grantTokens;

      this.isDiscovery    := |keyIDs| == 0 && generator.None?;
    }

    method GenerateAndSetKey(encMat: Mat.EncryptionMaterials) returns (res: Result<()>)
      requires Valid()
      requires encMat.Valid()
      requires encMat.plaintextDataKey.None?
      requires generator.Some?
      requires !isDiscovery
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys
      ensures Valid()
      ensures res.Success? ==> encMat.Valid() && encMat.plaintextDataKey.Some? && |encMat.encryptedDataKeys| > 0 &&
                               encMat.encryptedDataKeys[..|encMat.encryptedDataKeys| - 1] == old(encMat.encryptedDataKeys)
      // TODO: ensure GENERATED_DATA_KEY flag
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(encMat.encryptionContext, grantTokens, generator.get, encMat.algorithmSuiteID.KeyLength() as int32);
      var region :- RegionFromKMSKeyARN(generator.get);
      var client := clientSupplier(region);
      var generatorResponse :- client.GenerateDataKey(generatorRequest);
      if !generatorResponse.IsWellFormed() {
        return Failure("Invalid response from KMS GenerateDataKey");
      }
      var encryptedDataKey := generatorResponse.ciphertextBlob;
      var keyID := generatorResponse.keyID;
      var plaintextDataKey := generatorResponse.plaintext;

      if |plaintextDataKey| != encMat.algorithmSuiteID.KeyLength() {
        return Failure("Invalid response from KMS GenerateDataKey: bad key length");
      }

      encMat.SetPlaintextDataKey(plaintextDataKey);
      encMat.AppendEncryptedDataKey(Mat.EncryptedDataKey(KMSUtils.PROVIDER_ID, StringToByteSeq(keyID), encryptedDataKey));
      return Success(());
    }

    method OnEncrypt(encMat: Mat.EncryptionMaterials) returns (res: Result<Mat.EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys
      ensures Valid()
      ensures isDiscovery ==> res.Success? && unchanged(res.value)
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      // ensures res.Failure? ==> unchanged(encMat)
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance
    {
      var encryptCMKs := keyIDs;

      if isDiscovery {
        return Success(encMat);
      } else if encMat.plaintextDataKey.None? && generator.None? {
        return Failure("No plaintext datakey or generator defined");
      }

      if generator.Some? {
        if encMat.plaintextDataKey.None? {
          var _ :- GenerateAndSetKey(encMat);
        } else {
          encryptCMKs := encryptCMKs + [generator.get];
        }
      }

      ghost var oldPlaintextDataKey := encMat.plaintextDataKey.get;
      var i := 0;
      while i < |encryptCMKs|
        invariant encMat.plaintextDataKey.Some?
        invariant encMat.plaintextDataKey.get == oldPlaintextDataKey
        invariant encMat.Valid()
      {
        var encryptRequest := KMSUtils.EncryptRequest(encMat.encryptionContext, grantTokens, encryptCMKs[i], encMat.plaintextDataKey.get);
        var region :- RegionFromKMSKeyARN(encryptCMKs[i]);
        var client := clientSupplier(region);
        var encryptResponse :- client.Encrypt(encryptRequest);
        if encryptResponse.IsWellFormed() {
          encMat.AppendEncryptedDataKey(Mat.EncryptedDataKey(KMSUtils.PROVIDER_ID, StringToByteSeq(encryptResponse.keyID), encryptResponse.ciphertextBlob));
        } else {
          return Failure("Invalid response from KMS Encrypt");
        }
        i := i + 1;
      }
      return Success(encMat);
    }

    predicate method DecryptableEDK(edk: Mat.EncryptedDataKey)
    {
      edk.providerID == KMSUtils.PROVIDER_ID &&
      (isDiscovery || ByteSeqToString(edk.providerInfo) in keyIDs)
    }

    method OnDecrypt(decMat: Mat.DecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.DecryptionMaterials>)
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey
      ensures Valid()
      ensures decMat.Valid()
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
      {
        if |edks| == 0 || decMat.plaintextDataKey.Some? {
          return Success(decMat);
        }
        var decryptableEDKs := Filter(edks, DecryptableEDK);
        var i := 0;
        while i < |decryptableEDKs|
          invariant unchanged(decMat)
        {
          var edk := decryptableEDKs[i];
          var decryptRequest := KMSUtils.DecryptRequest(edk.ciphertext, decMat.encryptionContext, grantTokens);
          var region :- RegionFromKMSKeyARN(ByteSeqToString(edk.providerInfo));
          var client := clientSupplier(region);
          var decryptResponseResult := client.Decrypt(decryptRequest);
          if decryptResponseResult.Success? {
            var decryptResponse := decryptResponseResult.value;
            if decryptResponse.keyID != ByteSeqToString(edk.providerInfo) || |decryptResponse.plaintext| != decMat.algorithmSuiteID.KeyLength() {
              return Failure("Invalid response from KMS Decrypt");
            } else {
              decMat.setPlaintextDataKey(decryptResponse.plaintext);
              return Success(decMat);
            }
          }
          i := i + 1;
        }
        return Success(decMat);
      }
  }
}
