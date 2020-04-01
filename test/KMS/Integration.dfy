include "../../src/SDK/Keyring/KMSKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/MessageHeader.dfy"
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
  import Msg = MessageHeader
  import UTF8
  import Base64

  method EncryptDecryptTest(cmm: CMMDefs.CMM, message: string) returns (res: string)
    requires cmm.Valid()
    modifies cmm.Repr
    ensures cmm.Valid() && fresh(cmm.Repr - old(cmm.Repr))
  {
    var encodedMsg: seq<uint8>;
    var encodeResult := UTF8.Encode(message);
    if encodeResult.Success? {
      encodedMsg := encodeResult.value;
    }
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    assert Msg.ValidAAD(encryptionContext) by {
      // To prove ValidAAD, we need to reveal the definition of ValidAAD:
      reveal Msg.ValidAAD();
      // We also need to help the verifier with proving the KVPairsLength is small:
      calc {
        Msg.KVPairsLength(encryptionContext);
        var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
        var kvPairsSeq := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
        2 + Msg.KVPairEntriesLength(kvPairsSeq, 0, |kvPairsSeq|); // 2 bytes for the kvPairsCount field
        2 + 2 + |keyA| + 2 + |valA|; // 2 bytes required for keyLength and valueLength fields
      }
      assert Msg.KVPairsLength(encryptionContext) < UINT16_LIMIT;
    }
    var encryptRequest := new Client.EncryptRequest.WithCMM(encodedMsg, cmm);
    encryptRequest.SetEncryptionContext(encryptionContext);
    var e := Client.Encrypt(encryptRequest);
    expect e.Success?, "Bad encryption :( " + e.error + "\n";

    var decryptRequest := new Client.DecryptRequest.WithCMM(e.value, cmm);
    var d := Client.Decrypt(decryptRequest);
    expect d.Success?, "bad decryption: " + d.error + "\n";

    expect UTF8.ValidUTF8Seq(d.value), "Could not decode Encryption output";
    res :- expect UTF8.Decode(d.value);
  }

  method {:test} TestEndToEnd() {
    var namespace :- expect UTF8.Encode("namespace");
    var name :- expect UTF8.Encode("MyKeyring");
    var generatorStr := SHARED_TEST_KEY_ARN;
    expect KMSUtils.ValidFormatCMK(generatorStr);
    var generator: KMSUtils.CustomerMasterKey := generatorStr;
    var clientSupplier := new KMSUtils.DefaultClientSupplier();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var message := "Hello, World!!";
    var result := EncryptDecryptTest(cmm, message);
    expect message == result;
  }
}
