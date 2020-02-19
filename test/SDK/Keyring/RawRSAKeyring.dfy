include "../../../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/RSAEncryption.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestRSAKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RSA = RSAEncryption
  import RawRSAKeyringDef
  import AlgorithmSuite
  import UTF8
  import Materials

  const allPaddingModes := {RSA.PKCS1, RSA.OAEP_SHA1, RSA.OAEP_SHA256, RSA.OAEP_SHA384, RSA.OAEP_SHA512}

  method {:test} TestOnEncryptOnDecryptGenerateDataKey() returns (r: Result<()>)
  {
    var remainingPaddingModes := allPaddingModes;
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    while remainingPaddingModes != {}
      decreases remainingPaddingModes
    {
      var paddingMode :| paddingMode in remainingPaddingModes;
      remainingPaddingModes := remainingPaddingModes - {paddingMode};
      // Verify key generation for a given padding mode
      var publicKey, privateKey := RSA.GenerateKeyPair(2048, paddingMode);
      var rawRSAKeyring := new RawRSAKeyringDef.RawRSAKeyring(name, namespace, paddingMode, Some(publicKey), Some(privateKey));

      // Verify encoding
      var keyA :- UTF8.Encode("keyA");
      var valA :- UTF8.Encode("valA");
      var encryptionContext := map[keyA := valA];
      var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      var signingKey := seq(32, i => 0);
      var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey));
      var encryptionMaterialsOut :- rawRSAKeyring.OnEncrypt(encryptionMaterialsIn);
      var _ :- Require(encryptionMaterialsOut.plaintextDataKey.Some? &&
        |encryptionMaterialsOut.encryptedDataKeys| == 1 &&
        |encryptionMaterialsOut.keyringTrace| == 2);
      var plaintextDataKey := encryptionMaterialsOut.plaintextDataKey;
      var encryptedDataKey := encryptionMaterialsOut.encryptedDataKeys[0];

      // Verify decoding
      var verificationKey := seq(32, i => 0);
      var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
      var decryptionMaterialsOut :- rawRSAKeyring.OnDecrypt(decryptionMaterialsIn, [encryptedDataKey]);
      var _ :- Require(encryptionMaterialsOut.plaintextDataKey == plaintextDataKey);
    }
    return Success(());
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: Result<()>)
  {
    var remainingPaddingModes := allPaddingModes;
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    while remainingPaddingModes != {}
      decreases remainingPaddingModes
    {
      var paddingMode :| paddingMode in remainingPaddingModes;
      remainingPaddingModes := remainingPaddingModes - {paddingMode};
      // Verify key generation for a given padding mode
      var publicKey, privateKey := RSA.GenerateKeyPair(2048, paddingMode);
      var rawRSAKeyring := new RawRSAKeyringDef.RawRSAKeyring(name, namespace, paddingMode, Some(publicKey), Some(privateKey));

      // Verify encoding
      var keyA :- UTF8.Encode("keyA");
      var valA :- UTF8.Encode("valA");
      var encryptionContext := map[keyA := valA];
      var plaintextDataKey := seq(32, i => 0);
      var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      var signingKey := seq(32, i => 0);
      var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey))
                                                                .WithKeys(Some(plaintextDataKey), [], []);
      var encryptionMaterialsOut :- rawRSAKeyring.OnEncrypt(encryptionMaterialsIn);
      var _ :- Require(encryptionMaterialsOut.plaintextDataKey.Some? &&
        |encryptionMaterialsOut.encryptedDataKeys| == 1 &&
        encryptionMaterialsOut.plaintextDataKey.get == plaintextDataKey &&
        |encryptionMaterialsOut.keyringTrace| == 1);
      var encryptedDataKey := encryptionMaterialsOut.encryptedDataKeys[0];

      // Verify decoding
      var verificationKey := seq(32, i => 0);
      var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
      var decryptionMaterialsOut :- rawRSAKeyring.OnDecrypt(decryptionMaterialsIn, [encryptedDataKey]);
      r := Require(decryptionMaterialsOut.plaintextDataKey.Some? && decryptionMaterialsOut.plaintextDataKey.get == plaintextDataKey);
    }
  }
}
