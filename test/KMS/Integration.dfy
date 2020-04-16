include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/KMS/KMSUtils.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"
include "../Util/TestUtils.dfy"

module IntegTestKMS {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened TestUtils
  import CMMDefs
  import DefaultCMMDef
  import KMSUtils
  import KMSKeyringDef
  import Materials
  import Client = ESDKClient
  import EncryptionContext
  import UTF8
  import Base64

  method EncryptDecryptTest(cmm: CMMDefs.CMM, shouldFailGetClient: bool)
    requires cmm.Valid()
    modifies cmm.Repr
    ensures cmm.Valid() && fresh(cmm.Repr - old(cmm.Repr))
  {
    var message := "Hello, World!!";
    var encodeResult := UTF8.Encode(message);
    expect encodeResult.Success?, "Failed to encode :( " + encodeResult.error + "\n";
    var encodedMsg := encodeResult.value;
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    assert EncryptionContext.Serializable(encryptionContext) by {
      // To prove EncryptionContext.Serializable, we need to reveal the definition of that predicate:
      reveal EncryptionContext.Serializable();
      // We also need to help the verifier with proving the KVPairsLength is small:
      calc {
        EncryptionContext.Length(encryptionContext);
        var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
        var kvPairsSeq := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
        2 + EncryptionContext.LinearLength(kvPairsSeq, 0, |kvPairsSeq|); // 2 bytes for the kvPairsCount field
        2 + 2 + |keyA| + 2 + |valA|; // 2 bytes required for keyLength and valueLength fields
      }
      assert EncryptionContext.Length(encryptionContext) < UINT16_LIMIT;
    }
    var encryptRequest := new Client.EncryptRequest.WithCMM(encodedMsg, cmm);
    encryptRequest.SetEncryptionContext(encryptionContext);
    var e := Client.Encrypt(encryptRequest);
    if shouldFailGetClient {
      expect e.Failure?, "Successfully called GetClient when the call should have failed";
      return;
    }
    expect e.Success?, "Bad encryption :( " + e.error + "\n";

    var decryptRequest := new Client.DecryptRequest.WithCMM(e.value, cmm);
    var d := Client.Decrypt(decryptRequest);
    expect d.Success?, "bad decryption: " + d.error + "\n";

    expect UTF8.ValidUTF8Seq(d.value), "Could not decode Encryption output";
    var res :- expect UTF8.Decode(d.value);
    expect message == res;
  }

  method CreateTestingGenerator() returns (generator: KMSUtils.CustomerMasterKey)
  {
    var generatorStr := SHARED_TEST_KEY_ARN;
    expect KMSUtils.ValidFormatCMK(generatorStr);
    generator := generatorStr;
  }

  method {:test} TestEndToEnd_DefaultClientSupplier() {
    var clientSupplier := new KMSUtils.DefaultClientSupplier();
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_BaseClientSupplier() {
    var clientSupplier := new KMSUtils.BaseClientSupplier();
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingDefaultClientSupplier() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := ["some-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["some-excluded-region"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_NoRegions() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := [];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_ExcludeRegionsClientSupplier_Failure() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := ["us-west-2"];
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(excludeRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingDefaultClientSupplier() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := ["us-west-2"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_UsingBaseClientSupplier() {
    var baseClientSupplier := new KMSUtils.BaseClientSupplier();
    var regions: seq<string> := ["us-west-2"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(baseClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, false);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_BadRegion() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := ["another-region"];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_NoRegion() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(defaultClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, true);
  }

  method {:test} TestEndToEnd_LimitRegionsClientSupplier_Failure_ConflictingSuppliers() {
    var defaultClientSupplier := new KMSUtils.DefaultClientSupplier();
    var regions: seq<string> := [];
    var limitRegionsClientSupplier := new KMSUtils.LimitRegionsClientSupplier(defaultClientSupplier, regions);
    var excludeRegionsClientSupplier := new KMSUtils.ExcludeRegionsClientSupplier(limitRegionsClientSupplier, regions);
    var generator: KMSUtils.CustomerMasterKey := CreateTestingGenerator();
    var keyring := new KMSKeyringDef.KMSKeyring(limitRegionsClientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    EncryptDecryptTest(cmm, true);
  }
}
