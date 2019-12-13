include "../../../src/SDK/Keyring/MultiKeyring.dfy"
include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestMultiKeying {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyring
  import EncryptionSuites
  import MultiKeyringDef
  import AlgorithmSuite
  import UTF8

  const name := UTF8.Encode("test Name").value;
  const namespace := UTF8.Encode("test Namespace").value;

  method {:test} TestOnEncryptOnDecryptWithGenerator() returns (r: Result<()>) {
    // TODO: mock children keyrings
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var child1Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child1 Name").value, UTF8.Encode("child1 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child2 Name").value, UTF8.Encode("child2 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyIDs := new [][child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, keyIDs);

    // Encryption
    var onEncryptResult :- multiKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, None);
    // Check EDK list is as expected
    var _ :- Require(onEncryptResult.Some? && |onEncryptResult.get.encryptedDataKeys| == 2);
    // Check keyringTrace is as expected
    var _ :- Require(
       && |onEncryptResult.get.keyringTrace| == 3
       && onEncryptResult.get.keyringTrace[0] == child1Keyring.GenerateTraceEntry()
       && onEncryptResult.get.keyringTrace[1] == child1Keyring.EncryptTraceEntry()
       && onEncryptResult.get.keyringTrace[2] == child2Keyring.EncryptTraceEntry()
    );

    var pdk := onEncryptResult.get.plaintextDataKey;
    var edk1 := onEncryptResult.get.encryptedDataKeys[0];
    var edk2 := onEncryptResult.get.encryptedDataKeys[1];

    // First edk decryption
    var onDecryptResult :- multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk1]);
    // Check plaintextDataKey is as expected
    var _ :- Require(onDecryptResult.Some? && onDecryptResult.get.plaintextDataKey == pdk);
    // Check keyringTrace is as expected
    var _ :- Require(
       && |onDecryptResult.get.keyringTrace| == 1
       && onDecryptResult.get.keyringTrace[0] == child1Keyring.DecryptTraceEntry()
    );

    // Second edk decryption
    onDecryptResult :- multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk2]);
    // Check plaintextDataKey is as expected
    var _ :- Require(onDecryptResult.Some? && onDecryptResult.get.plaintextDataKey == pdk);
    // Check keyringTrace is as expected
    r := Require(
       && |onDecryptResult.get.keyringTrace| == 1
       && onDecryptResult.get.keyringTrace[0] == child2Keyring.DecryptTraceEntry()
    );
  }

  method {:test} TestOnEncryptOnDecryptWithoutGenerator() returns (r: Result<()>) {
    // TODO: mock children keyrings and move encrypt <-> decrypt test into new test
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var child1Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child1 Name").value, UTF8.Encode("child1 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child2 Name").value, UTF8.Encode("child2 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyIDs := new [][child1Keyring, child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, keyIDs);

    var pdk := seq(32, i => 0);

    // Encryption
    var onEncryptResult :- multiKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, Some(pdk));
    // Check plaintextDataKey is as expected
    var _ :- Require(onEncryptResult.Some? && onEncryptResult.get.plaintextDataKey == pdk);
    // Check keyringTrace is as expected
    var _ :- Require(
       && |onEncryptResult.get.keyringTrace| == 2
       && onEncryptResult.get.keyringTrace[0] == child1Keyring.EncryptTraceEntry()
       && onEncryptResult.get.keyringTrace[1] == child2Keyring.EncryptTraceEntry()
    );

    var edk1 := onEncryptResult.get.encryptedDataKeys[0];
    var edk2 := onEncryptResult.get.encryptedDataKeys[1];

    // First EDK decryption
    var onDecryptResult :- multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk1]);
    // Check plaintextDataKey is as expected
    var _ :- Require(onDecryptResult.Some? && onDecryptResult.get.plaintextDataKey == pdk);
    // Check keyringTrace is as expected
    var _ :- Require(
       && |onDecryptResult.get.keyringTrace| == 1
       && onDecryptResult.get.keyringTrace[0] == child1Keyring.DecryptTraceEntry()
    );

    // Second EDK decryption
    onDecryptResult :- multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk2]);
    // Check plaintextDataKey is as expected
    var _ :- Require(onDecryptResult.Some? && onDecryptResult.get.plaintextDataKey == pdk);
    // Check keyringTrace is as expected
    r := Require(
      && |onDecryptResult.get.keyringTrace| == 1
      && onDecryptResult.get.keyringTrace[0] == child2Keyring.DecryptTraceEntry()
    );
  }
}
