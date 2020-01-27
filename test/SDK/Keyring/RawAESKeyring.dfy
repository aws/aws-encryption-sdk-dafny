include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/SDK/MessageHeader.dfy"
include "../../../src/SDK/Materials.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/Crypto/AESEncryption.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import RawAESKeyringDef
  import MessageHeader
  import Materials
  import EncryptionSuites
  import AlgorithmSuite
  import UTF8

  const name := UTF8.Encode("test Name").value;
  const namespace := UTF8.Encode("test Namespace").value;

  method {:test} TestOnEncryptOnDecryptGenerateDataKey() returns (r: Result<()>)
  {
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var _ :- Require(MessageHeader.ValidKVPairs(encryptionContext));

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;

    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, None);
    var _ :- Require(onEncryptResult.Some?);
    var _ :- Require(|onEncryptResult.get.encryptedDataKeys| == 1);
    var _ :- Require(wrappingAlgorithmID.TagLength() as nat <= |onEncryptResult.get.encryptedDataKeys[0].ciphertext|);
    var encOutput := RawAESKeyringDef.DeserializeEDKCiphertext(onEncryptResult.get.encryptedDataKeys[0].ciphertext, wrappingAlgorithmID.TagLength() as nat);

    var pdk := onEncryptResult.get.plaintextDataKey;
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: Result<()>)
  {
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var _ :- Require(MessageHeader.ValidKVPairs(encryptionContext));

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;

    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, Some(pdk));
    var _ :- Require(onEncryptResult.Some?);
    var _ :- Require(|onEncryptResult.get.encryptedDataKeys| == 1);
    var _ :- Require(wrappingAlgorithmID.TagLength() as nat <= |onEncryptResult.get.encryptedDataKeys[0].ciphertext|);
    var encOutput := RawAESKeyringDef.DeserializeEDKCiphertext(onEncryptResult.get.encryptedDataKeys[0].ciphertext, wrappingAlgorithmID.TagLength() as nat);
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }

  method {:test} TestOnDecryptNoEDKs() returns (r: Result<()>)
  {
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, []);
    r := Require(res.None?);
  }

  method {:test} TestOnEncryptUnserializableEC() returns (r: Result<()>)
  {
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    

    var unserializableEncryptionContext := genereateUnserializableEncryptionContext();
    var _ :- Require(!MessageHeader.ValidKVPairs(unserializableEncryptionContext));

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var onEncryptResult := rawAESKeyring.OnEncrypt(wrappingAlgorithmID, unserializableEncryptionContext, None);
    r := Require(onEncryptResult.Failure?);
  }

  method {:test} TestOnDecryptUnserializableEC() returns (r: Result<()>)
  {
    // Set up valid EDK for decryption
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, None);
    var _ :- Require(onEncryptResult.Some?);
    var _ :- Require(|onEncryptResult.get.encryptedDataKeys| == 1);
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := genereateUnserializableEncryptionContext();
    var _ :- Require(!MessageHeader.ValidKVPairs(unserializableEncryptionContext));

    var onDecryptResult := rawAESKeyring.OnDecrypt(wrappingAlgorithmID, unserializableEncryptionContext, [edk]);
    r := Require(onDecryptResult.Failure?);
  }

  // TODO correctly verify UTF8 validity of long sequences
  // This axiom is used only by these tests to skip verification of sequences too
  // long to be serialized. Otherwise we get a false negative for verification of this file.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1_0000
    ensures UTF8.ValidUTF8Seq(s)

  method genereateUnserializableEncryptionContext() returns (encCtx: Materials.EncryptionContext)
  {
    var keyA := UTF8.Encode("keyA").value;
    var invalidVal := Fill<uint8>(0, 0x1_0000);
    AssumeLongSeqIsValidUTF8(invalidVal);
    return [(keyA, invalidVal)];
  }
}
