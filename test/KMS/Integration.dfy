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

  method EncryptDecryptTest(cmm: CMMDefs.CMM, message: string) returns (res: Result<string>)
    requires cmm.Valid()
  {
    var encodedMsg := UTF8.Encode(message);
    var keyA := UTF8.Encode("keyA");
    var valA := UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    assert Msg.ValidAAD(encryptionContext) by {
      // To prove ValidAAD, we need to reveal the definition of ValidAAD:
      reveal Msg.ValidAAD();
      // We also need to help the verifier with proving the KVPairsLength is small:
      calc {
        Msg.KVPairsLength(encryptionContext);
        2 + Msg.KVPairEntriesLength(encryptionContext, 0, 1);
        2 + 2 + |keyA| + 2 + |valA|;
      }
      assert Msg.KVPairsLength(encryptionContext) < UINT16_LIMIT;
    }
    var e := Client.Encrypt(encodedMsg, cmm, encryptionContext);
    if e.Failure? {
      return Failure("Bad encryption :( " + e.error + "\n");
    }

    var d := Client.Decrypt(e.value, cmm);
    if d.Failure? {
      return Failure("bad decryption: " + d.error + "\n");
    }
    if UTF8.ValidUTF8Seq(d.value) {
      var utf8Encoded := UTF8.Decode(d.value);
      return Success(utf8Encoded);
    } else {
      return Failure("Could not decode Encryption output");
    }
  }

  method {:test} TestEndToEnd() returns (r: Result<()>) {
    var namespace := UTF8.Encode("namespace");
    var name := UTF8.Encode("MyKeyring");
    var generatorStr := SHARED_TEST_KEY_ARN;
    var _ :- Require(KMSUtils.ValidFormatCMK(generatorStr));
    var generator: KMSUtils.CustomerMasterKey := generatorStr;
    var clientSupplier := new KMSUtils.DefaultClientSupplier();
    var keyring := new KMSKeyringDef.KMSKeyring(clientSupplier, [], Some(generator), []);
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var message := "Hello, World!!";
    var result :- EncryptDecryptTest(cmm, message);
    r := RequireEqual(message, result);
  }
}
