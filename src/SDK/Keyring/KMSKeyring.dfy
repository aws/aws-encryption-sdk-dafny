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

  function method RegionFromKMSKeyARN(arn: string): Result<string>
  {
    var components := Split(arn, ':');
    if 6 <= |components| && components[0] == "arn" && components[2] == "kms" then Success(components[3]) else Failure("Malformed ARN")
  }

  class KMSKeyring extends KeyringDefs.Keyring {

    const clientSupplier: KMSUtils.ClientSupplier
    const keyIDs: seq<string>
    const generator: Option<string>
    const grantTokens: seq<string>
    const isDiscovery: bool

    predicate Valid() reads this, Repr {
      Repr == {this} &&
      |keyIDs| == 0 && generator.None? ==> isDiscovery
    }

    constructor(clientSupplier: KMSUtils.ClientSupplier, keyIDs: seq<string>, generator: Option<string>, grantTokens: seq<string>)
      ensures Valid()
    {
      this.clientSupplier := clientSupplier;
      this.keyIDs         := keyIDs;
      this.generator      := generator;
      this.grantTokens    := grantTokens;

      this.isDiscovery    := |keyIDs| == 0 && generator.None?;
    }

    method Generate(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext) returns (res: Result<Mat.ValidDataKeyMaterials>)
      requires Valid()
      requires generator.Some?
      requires !isDiscovery
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID == algorithmSuiteID
      // TODO: ensure GENERATED_DATA_KEY flag
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(encryptionContext, grantTokens, generator.get, algorithmSuiteID.KeyLength() as int32);
      var regionRes := RegionFromKMSKeyARN(generator.get);
      var regionOpt := regionRes.ToOption();
      var client :- clientSupplier.GetClient(regionOpt);
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

      if !algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
        return Failure("Invalid response from KMS GenerateDataKey: bad key length");
      }

      return Success(Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey, [encryptedDataKey]));
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
      var edks: seq<Mat.ValidEncryptedDataKey> := [];
      var ptdk: seq<uint8>;

      if generator.Some? {
        if plaintextDataKey.None? {
          var generatedMaterials :- Generate(algorithmSuiteID, encryptionContext);
          ptdk := generatedMaterials.plaintextDataKey;
          edks := generatedMaterials.encryptedDataKeys;
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
      {
        var encryptRequest := KMSUtils.EncryptRequest(encryptionContext, grantTokens, encryptCMKs[i], ptdk);
        var regionRes := RegionFromKMSKeyARN(encryptCMKs[i]);
        var regionOpt := regionRes.ToOption();
        var client :- clientSupplier.GetClient(regionOpt);
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
      var keys := if generator.Some? then keyIDs + [generator.get] else keyIDs;
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
          var providerInfo := UTF8.Decode(edk.providerInfo).value;
          var regionRes := RegionFromKMSKeyARN(providerInfo);
          var regionOpt := regionRes.ToOption();
          var client :- clientSupplier.GetClient(regionOpt);
          var decryptResponseResult := client.Decrypt(decryptRequest);
          if decryptResponseResult.Success? {
            var decryptResponse := decryptResponseResult.value;
            if (UTF8.Decode(edk.providerInfo).Success? && decryptResponse.keyID != UTF8.Decode(edk.providerInfo).value)
               || !algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext) {
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
