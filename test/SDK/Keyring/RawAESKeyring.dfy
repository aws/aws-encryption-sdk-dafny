include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyringDef
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
    var onEncryptResult :- rawAESKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, None);
    var _ :- Require(onEncryptResult.Some? && |onEncryptResult.get.encryptedDataKeys| == 1);

    var pdk := onEncryptResult.get.plaintextDataKey;
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: Result<()>)
  {
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var pdk := seq(32, i => 0);
    var onEncryptResult :- rawAESKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, Some(pdk));
    var _ :- Require(onEncryptResult.Some? && |onEncryptResult.get.encryptedDataKeys| == 1);
    
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }
}
