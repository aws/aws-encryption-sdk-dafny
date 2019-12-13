include "./Defs.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/KMSUtils.dfy"
include "../../Util/UTF8.dfy"

module {:extern "KMSKeyringDefs"} KMSKeyringDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import KeyringDefs
  import Mat = Materials
  import KMSUtils
  import UTF8

  const PROVIDER_ID := UTF8.Encode("aws-kms").value

  function method RegionFromKMSKeyARN(arn: KMSUtils.CustomerMasterKey): Result<string>
  {
    var components := Split(arn, ':');
    if 6 <= |components| && components[0] == "arn" && components[2] == "kms" then Success(components[3]) else Failure("Malformed ARN")
  }

  class KMSKeyring extends KeyringDefs.Keyring {

    const clientSupplier: KMSUtils.ClientSupplier
    const keyIDs: seq<KMSUtils.CustomerMasterKey>
    const generator: Option<KMSUtils.CustomerMasterKey>
    const grantTokens: seq<KMSUtils.GrantToken>
    const isDiscovery: bool

    predicate Valid() reads this, Repr {
      && Repr == {this}
      && (0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS)
      && (|keyIDs| == 0 && generator.None? ==> isDiscovery)
    }

    constructor(clientSupplier: KMSUtils.ClientSupplier, keyIDs: seq<KMSUtils.CustomerMasterKey>, generator: Option<KMSUtils.CustomerMasterKey>, grantTokens: seq<KMSUtils.GrantToken>)
      requires 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      ensures Valid()
    {
      Repr := {this};

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
                               && |res.value.keyringTrace| == 1
                               && res.value.keyringTrace[0].flags == {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT}
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(encryptionContext, grantTokens, generator.get, algorithmSuiteID.KDFInputKeyLength() as int32);
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
      var encryptedDataKey := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, generatorResponse.ciphertextBlob);
      var keyID := generatorResponse.keyID;
      var plaintextDataKey := generatorResponse.plaintext;

      if !algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
        return Failure("Invalid response from KMS GenerateDataKey: Invalid key");
      }

      var generateTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, UTF8.Encode(generator.get).value, {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
      var datakeyMaterials := Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey, [encryptedDataKey], [generateTraceEntry]);
      assert datakeyMaterials.Valid();
      return Success(datakeyMaterials);
    }

    method OnEncrypt(algorithmSuiteID: AlgorithmSuite.ID,
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
      ensures res.Success? && res.value.Some? ==>
        var generateTraces := Filter(res.value.get.keyringTrace, Mat.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0
    {
      if isDiscovery {
        return Success(None);
      } else if plaintextDataKey.None? && generator.None? {
        return Failure("No plaintext datakey or generator defined");
      }

      var encryptCMKs := keyIDs;
      var edks: seq<Mat.ValidEncryptedDataKey> := [];
      var keyringTrace := [];
      var ptdk: seq<uint8>;

      if generator.Some? {
        if plaintextDataKey.None? {
          var generatedMaterials :- Generate(algorithmSuiteID, encryptionContext);
          ptdk := generatedMaterials.plaintextDataKey;
          edks := generatedMaterials.encryptedDataKeys;
          keyringTrace := generatedMaterials.keyringTrace;
        } else {
          ptdk := plaintextDataKey.get;
          encryptCMKs := encryptCMKs + [generator.get];
        }
      } else {
        ptdk := plaintextDataKey.get;
      }

      var i := 0;
      while i < |encryptCMKs|
        invariant forall entry :: entry in keyringTrace ==> entry.flags <= Mat.ValidEncryptionMaterialFlags
        invariant forall entry :: entry in keyringTrace ==> Mat.IsGenerateTraceEntry(entry) || Mat.IsEncryptTraceEntry(entry)
        invariant |edks| == |Filter(keyringTrace, Mat.IsEncryptTraceEntry)|
        invariant |Filter(keyringTrace, Mat.IsGenerateTraceEntry)| == 1 ==> keyringTrace[0] == Filter(keyringTrace, Mat.IsGenerateTraceEntry)[0]
        invariant |Filter(keyringTrace, Mat.IsGenerateTraceEntry)| == if plaintextDataKey.None? then 1 else 0;
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
          var edk := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, encryptResponse.ciphertextBlob);
          var encryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, UTF8.Encode(encryptCMKs[i]).value, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
          edks := edks + [edk];
          FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
          FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsEncryptTraceEntry);
          keyringTrace := keyringTrace + [encryptTraceEntry];
        } else {
          return Failure("Invalid response from KMS Encrypt");
        }
        i := i + 1;
      }
      var datakeyMat := Mat.DataKeyMaterials(algorithmSuiteID, ptdk, edks, keyringTrace);
      assert datakeyMat.Valid();
      return Success(Some(datakeyMat));
    }

    predicate method ShouldAttemptDecryption(edk: Mat.EncryptedDataKey)
    {
      var keys := if generator.Some? then keyIDs + [generator.get] else keyIDs;
      edk.providerID == PROVIDER_ID &&
      UTF8.ValidUTF8Seq(edk.providerInfo) && UTF8.Decode(edk.providerInfo).Success? &&
      KMSUtils.ValidFormatCMK(UTF8.Decode(edk.providerInfo).value) &&
      (isDiscovery || UTF8.Decode(edk.providerInfo).value in keys)
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Option<Mat.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      // TODO: keyring trace DECRYPTED_DATA_KEY flag assurance
    {
      if |edks| == 0 {
        return Success(None);
      }
      var i := 0;
      while i < |edks| {
        var edk := edks[i];
        if ShouldAttemptDecryption(edk) {
          var decryptRequest := KMSUtils.DecryptRequest(edk.ciphertext, encryptionContext, grantTokens);
          var providerInfo := UTF8.Decode(edk.providerInfo).value;
          var regionRes := RegionFromKMSKeyARN(providerInfo);
          var regionOpt := regionRes.ToOption();
          var clientRes := clientSupplier.GetClient(regionOpt);
          if clientRes.Success? {
            var client := clientRes.value;
            var decryptResponseResult := client.Decrypt(decryptRequest);
            if decryptResponseResult.Success? {
              var decryptResponse := decryptResponseResult.value;
              if (decryptResponse.keyID != UTF8.Decode(edk.providerInfo).value)
                  || !algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext) {
                return Failure("Invalid response from KMS Decrypt");
              } else {
                var decryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, edk.providerInfo, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT});
                return Success(Some(Mat.OnDecryptResult(algorithmSuiteID, decryptResponse.plaintext, [decryptTraceEntry])));
              }
            }
          }
        }
        i := i + 1;
      }
      return Success(None);
    }
  }
}
