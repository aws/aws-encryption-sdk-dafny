include "./Defs.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/KMSUtils.dfy"
include "../../Util/UTF8.dfy"

module KMSKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import KeyringDefs
  import Mat = Materials
  import KMSUtils
  import UTF8

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

    method Generate(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext) returns (res: Result<(seq<uint8>, Mat.EncryptedDataKey)>)
      requires Valid()
      requires generator.Some?
      requires !isDiscovery
      ensures Valid()
      ensures res.Success? ==> algorithmSuiteID.ValidPlaintextDataKey(res.value.0) && res.value.1.Valid()
      // TODO: ensure GENERATED_DATA_KEY flag
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(encryptionContext, grantTokens, generator.get, algorithmSuiteID.KeyLength() as int32);
      var region :- RegionFromKMSKeyARN(generator.get);
      var client := clientSupplier(region);
      var generatorResponse :- client.GenerateDataKey(generatorRequest);
      if !generatorResponse.IsWellFormed() {
        return Failure("Invalid response from KMS GenerateDataKey");
      }
      var providerInfo :- UTF8.Encode(generatorResponse.keyID);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure("providerInfo exceeds maximum length");
      }
      var encryptedDataKey := Mat.EncryptedDataKey(KMSUtils.ProviderID(), providerInfo, generatorResponse.ciphertextBlob);
      var keyID := generatorResponse.keyID;
      var plaintextDataKey := generatorResponse.plaintext;

      if |plaintextDataKey| != algorithmSuiteID.KeyLength() {
        return Failure("Invalid response from KMS GenerateDataKey: bad key length");
      }

      return Success((plaintextDataKey, encryptedDataKey));
    }

    method OnEncrypt(algorithmSuiteID: Mat.AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Mat.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures isDiscovery ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==>
          algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==>
          plaintextDataKey.get == res.value.get.plaintextDataKey
      // TODO: keyring trace GENERATED_DATA_KEY flag assurance
      // TODO: keyring trace ENCRYPTED_DATA_KEY flag assurance
    {
      if isDiscovery {
        return Success(None);
      } else if plaintextDataKey.None? && generator.None? {
        return Failure("No plaintext datakey or generator defined");
      }

      var encryptCMKs := keyIDs;
      var edks: seq<Mat.EncryptedDataKey> := [];
      var ptdk: seq<uint8>;

      if generator.Some? {
        if plaintextDataKey.None? {
          var resTuple :- Generate(algorithmSuiteID, encryptionContext);
          ptdk := resTuple.0;
          edks := [resTuple.1];
        } else {
          ptdk := plaintextDataKey.get;
          encryptCMKs := encryptCMKs + [generator.get];
        }
      } else {
        ptdk := plaintextDataKey.get;
      }

      var i := 0;
      while i < |encryptCMKs|
        invariant plaintextDataKey.Some? ==> ptdk == plaintextDataKey.get
        invariant forall edk :: edk in edks ==> edk.Valid()
      {
        var encryptRequest := KMSUtils.EncryptRequest(encryptionContext, grantTokens, encryptCMKs[i], ptdk);
        var region :- RegionFromKMSKeyARN(encryptCMKs[i]);
        var client := clientSupplier(region);
        var encryptResponse :- client.Encrypt(encryptRequest);
        if encryptResponse.IsWellFormed() {
          var providerInfo :- UTF8.Encode(encryptResponse.keyID);
          if UINT16_LIMIT <= |providerInfo| {
            return Failure("providerInfo exceeds maximum length");
          }
          var edk := Mat.EncryptedDataKey(KMSUtils.ProviderID(), providerInfo, encryptResponse.ciphertextBlob);
          edks := edks + [edk];
        } else {
          return Failure("Invalid response from KMS Encrypt");
        }
        i := i + 1;
      }
      var datakeyMat := Mat.DataKeyMaterials(algorithmSuiteID, ptdk, edks);
      assert datakeyMat.Valid();
      return Success(Some(datakeyMat));
    }

    predicate method DecryptableEDK(edk: Mat.EncryptedDataKey)
    {
      var keys := if generator.Some? then keyIDs + [generator.get]
                  else keyIDs;
      edk.providerID == KMSUtils.ProviderID() &&
      UTF8.ValidUTF8Seq(edk.providerInfo) && UTF8.Decode(edk.providerInfo).Success? &&
      (isDiscovery || UTF8.Decode(edk.providerInfo).value in keys)
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Option<seq<uint8>>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(res.value.get)
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
      {
        if |edks| == 0 {
          return Success(None);
        }
        var decryptableEDKs := Filter(edks, DecryptableEDK);
        var i := 0;
        while i < |decryptableEDKs| {
          var edk := decryptableEDKs[i];
          var decryptRequest := KMSUtils.DecryptRequest(edk.ciphertext, encryptionContext, grantTokens);
          var providerInfo :- UTF8.Decode(edk.providerInfo);
          var region :- RegionFromKMSKeyARN(providerInfo);
          var client := clientSupplier(region);
          var decryptResponseResult := client.Decrypt(decryptRequest);
          if decryptResponseResult.Success? {
            var decryptResponse := decryptResponseResult.value;
            if (UTF8.Decode(edk.providerInfo).Success? && decryptResponse.keyID != UTF8.Decode(edk.providerInfo).value)
               || |decryptResponse.plaintext| != algorithmSuiteID.KeyLength() {
              return Failure("Invalid response from KMS Decrypt");
            } else {
              return Success(Some(decryptResponse.plaintext));
            }
          }
          i := i + 1;
        }
        return Success(None);
      }
  }
}
