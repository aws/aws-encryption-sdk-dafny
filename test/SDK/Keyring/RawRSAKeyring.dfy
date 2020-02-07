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

  const allPaddingModes := {RSA.PKCS1, RSA.OAEP_SHA1, RSA.OAEP_SHA256, RSA.OAEP_SHA384, RSA.OAEP_SHA512}

  method {:test} TestOnEncryptOnDecryptGenerateDataKey() returns (r: TestResult)
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
      var encryptionContext := [(keyA, valA)];
      var onEncryptResult :- rawRSAKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, None);
      :- Require(onEncryptResult.Some? &&
        |onEncryptResult.get.encryptedDataKeys| == 1 &&
        |onEncryptResult.get.keyringTrace| == 2);
      var plaintextDataKey := onEncryptResult.get.plaintextDataKey;
      var encryptedDataKey := onEncryptResult.get.encryptedDataKeys[0];

      // Verify decoding
      var res :- rawRSAKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [encryptedDataKey]);
      :- Require(res.Some? && res.get.plaintextDataKey == plaintextDataKey);
    }
    return TestSuccess;
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: TestResult)
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
      var encryptionContext := [(keyA, valA)];
      var plaintextDataKey := seq(32, i => 0);
      var onEncryptResult :- rawRSAKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, Some(plaintextDataKey));
      :- Require(onEncryptResult.Some? &&
        |onEncryptResult.get.encryptedDataKeys| == 1 &&
        onEncryptResult.get.plaintextDataKey == plaintextDataKey &&
        |onEncryptResult.get.keyringTrace| == 1);
      var encryptedDataKey := onEncryptResult.get.encryptedDataKeys[0];

      // Verify decoding
      var res :- rawRSAKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [encryptedDataKey]);
      r := Require(res.Some? && res.get.plaintextDataKey == plaintextDataKey);
    }
  }
}
