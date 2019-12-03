// RUN: %dafny /out:Output/MultiKeyring.exe "./MultiKeyring.dfy" ../../../src/extern/dotnet/UTF8.cs ../../../src/extern/dotnet/Random.cs ../../../src/extern/dotnet/AESEncryption.cs ../%bclib /compile:2
// RUN: cp ../%bclib Output/
// RUN: %mono ./Output/MultiKeyring.exe > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../../src/SDK/Keyring/MultiKeyring.dfy"
include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

module TestRSAKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyring
  import EncryptionSuites
  import MultiKeyringDef
  import AlgorithmSuite
  import UTF8

  const name := UTF8.Encode("test Name").value;
  const namespace := UTF8.Encode("test Namespace").value;

  method TestOnEncryptOnDecryptWithGenerator() {
    // TODO: mock children keyrings
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var child1Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child1 Name").value, UTF8.Encode("child1 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child2 Name").value, UTF8.Encode("child2 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyIDs := new [][child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, keyIDs);

    var res := multiKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, None);
    if onEncryptResult.Failure? || onEncryptResult.value.None? || |onEncryptResult.value.get.encryptedDataKeys| != 2 {
      print "NOT CORRECT\n";
      return;
    }

    var pdk := onEncryptResult.value.get.plaintextDataKey;
    var edk1 := onEncryptResult.value.get.encryptedDataKeys[0];
    var edk2 := onEncryptResult.value.get.encryptedDataKeys[1];

    var res := multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk1]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }

    res := multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk2]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestOnEncryptOnDecryptWithoutGenerator() {
    // TODO: mock children keyrings and move encrypt <-> decrypt test into new test
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    var child1Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child1 Name").value, UTF8.Encode("child1 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyring.RawAESKeyring(UTF8.Encode("child2 Name").value, UTF8.Encode("child2 Namespace").value, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyIDs := new [][child1Keyring, child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, keyIDs);

    var pdk := seq(32, i => 0);

    var onEncryptResult := multiKeyring.OnEncrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, Some(pdk));
    if onEncryptResult.Failure? || onEncryptResult.value.None? || |onEncryptResult.value.get.encryptedDataKeys| != 2 {
      print "NOT CORRECT\n";
      return;
    }

    var edk1 := onEncryptResult.value.get.encryptedDataKeys[0];
    var edk2 := onEncryptResult.value.get.encryptedDataKeys[1];

    var res := multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk1]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }

    res := multiKeyring.OnDecrypt(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, encryptionContext, [edk2]);
    if res.Success? && res.value.Some? && res.value.get.plaintextDataKey == pdk {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    TestOnEncryptOnDecryptWithGenerator();
    TestOnEncryptOnDecryptWithoutGenerator();
  }
}
