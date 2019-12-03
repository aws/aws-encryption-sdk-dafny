// RUN: %dafny /out:Output/RawAESKeyring.exe "./RawAESKeyring.dfy" ../../../src/extern/dotnet/UTF8.cs ../../../src/extern/dotnet/Random.cs ../../../src/extern/dotnet/AESEncryption.cs ../%bclib /compile:2
// RUN: cp ../%bclib Output/
// RUN: %mono ./Output/RawAESKeyring.exe > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyring
  import EncryptionSuites
  import AlgorithmSuite
  import UTF8

  const name := UTF8.Encode("test Name").value;
  const namespace := UTF8.Encode("test Namespace").value;

  method TestOnEncryptOnDecryptGenerateDataKey(rawAESKeyring: RawAESKeyring.RawAESKeyring) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var onEncryptResult := rawAESKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, None);
    if onEncryptResult.Failure? || onEncryptResult.value.None? || |onEncryptResult.value.get.encryptedDataKeys| != 1 {
      print "NOT CORRECT\n";
      return;
    }

    var pdk := onEncryptResult.value.get.plaintextDataKey;
    var edk := onEncryptResult.value.get.encryptedDataKeys[0];

    var res := rawAESKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestOnEncryptOnDecryptSuppliedDataKey(rawAESKeyring: RawAESKeyring.RawAESKeyring) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var pdk := seq(32, i => 0);
    var onEncryptResult := rawAESKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, Some(pdk));
    if onEncryptResult.Failure? || onEncryptResult.value.None? || |onEncryptResult.value.get.encryptedDataKeys| != 1 {
      print "NOT CORRECT\n";
      return;
    }
    
    var edk := onEncryptResult.value.get.encryptedDataKeys[0];

    var res := rawAESKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    TestOnEncryptOnDecryptGenerateDataKey(rawAESKeyring);
    TestOnEncryptOnDecryptSuppliedDataKey(rawAESKeyring);
  }
}
