include "../src/StandardLibrary/StandardLibrary.dfy"
include "../src/StandardLibrary/UInt.dfy"
include "../src/Util/UTF8.dfy"
include "../src/SDK/Keyring/RawAESKeyring.dfy"
include "../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../src/Crypto/EncryptionSuites.dfy"
include "../src/Crypto/RSAEncryption.dfy"
include "../src/SDK/CMM/DefaultCMM.dfy"
include "../src/SDK/Client.dfy"
include "../src/StandardLibrary/Base64.dfy"
include "../src/KMS/KMSUtils.dfy"
include "../src/SDK/Keyring/KMSKeyring.dfy"

module {:extern "TestVectorExterns"} TestVectors {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import KMSKeyring
  import KMSUtils
  import RawAESKeyring
  import RawRSAKeyringDef
  import RSAEncryption
  import EncryptionSuites
  import DefaultCMMDef
  import Client = ESDKClient
  import Base64
/*
  const key1 := Key(true, true, "aes", "symmetric", 128, "base64", "AAECAwQFBgcICRAREhMUFQ==", "aes-128");

  const privateKey := Key(true, true, "rsa", "private", 4096, "pem",
  "-----BEGIN PRIVATE KEY-----\n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\ndzxtGxpeTBi+KhKlca8SlCdCqYwG6Q==\n-----END PRIVATE KEY-----",
  "rsa-4096-private")

  const publicKey := Key(true, false, "rsa", "public", 4096, "pem",
  "-----BEGIN PUBLIC KEY-----\nMIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs7RoNYEPAIws89VV+kra\nrVv/4wbdmUAaAKWgWuxZi5na9GJSmnhCkqyLRm7wPbQY4LCoa5/IMUxkHLsYDPdu\nudY0Qm0GcoxOlvJKHYo4RjF7HyiS34D6dvyO4Gd3aq0mZHoxSGCxW/7hf03wEMzc\niVJXWHXhaI0lD6nrzIEgLrE4L+3V2LeAQjvZsTKd+bYMqeZOL2syiVVIAU8POwAG\nGVBroJoveFm/SUp6lCiN0M2kTeyQA2ax3QTtZSAa8nwrI7U52XOzVmdMicJsy2Pg\nuW98te3MuODdK24yNkHIkYameP/Umf/SJshUJQd5a/TUp3XE+HhOWAumx22tIDlC\nvZS11cuk2fp0WeHUnXaC19N5qWKfvHEKSugzty/z3lGP7ItFhrF2X1qJHeAAsL11\nkjo6Lc48KsE1vKvbnW4VLyB3wdNiVvmUNO29tPXwaR0Q5Gbr3jk3nUzdkEHouHWQ\n41lubOHCCBN3V13mh/MgtNhESHjfmmOnh54ErD9saA1d7CjTf8g2wqmjEqvGSW6N\nq7zhcWR2tp1olflS7oHzul4/I3hnkfL6Kb2xAWWaQKvg3mtsY2OPlzFEP0tR5UcH\nPfp5CeS1Xzg7hN6vRICW6m4l3u2HJFld2akDMm1vnSz8RCbPW7jp7YBxUkWJmypM\ntG7Yv2aGZXGbUtM8o1cZarECAwEAAQ==\n-----END PUBLIC KEY-----",
  "rsa-4096-public")

  const kmsCMK := Key(true, true, "", "aws-kms", 0, "", "", "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f")

  const masterKey1 := MasterKey("raw", key1, Some("aws-raw-vectors-persistant"), Some("aes"), None(), None());

  const masterKey2 := MasterKey("raw", privateKey, Some("aws-raw-vectors-persistant"), Some("rsa"), Some("pkcs1"), None());
  const masterKey3 := MasterKey("raw", publicKey, Some("aws-raw-vectors-persistant"), Some("rsa"), Some("oaep-mgf1"), Some("sha256"));

  const masterKeyKMS := MasterKey("aws-kms", kmsCMK, None(), None(), None(), None());

  const testCaseKMS := TestCase("file://plaintexts/small", "file://ciphertexts/4c571f2c-ced1-4250-bf63-2206cdb85fe8", [masterKeyKMS])

  const testCase1 := TestCase("file://plaintexts/small", "file://ciphertexts/b84d9ead-2750-4247-a3aa-b3b0b60af267", [masterKey1]);
  const testCase2 := TestCase("file://plaintexts/small", "file://ciphertexts/5af3320a-348e-4722-a24f-a28e9a6e89bc", [masterKey2, masterKey3])
  */
  // TODO better name
  datatype MasterKey = MasterKey(masterKeyType: string,
                                 key: Key, // TODO or does this need to be keyID?
                                 providerID: Option<string>,
                                 encryptionAlgorithm: Option<string>,
                                 paddingAlgorithm: Option<string>,
                                 paddingHash: Option<string>)

  datatype Key = Key(encrypt: bool,
                     decrypt: bool,
                     keyType: string,
                     keyID: string,
                     algorithm: Option<string>,
                     bits: Option<uint16>,
                     encoding: Option<string>,
                     material: Option<string>,
                     keyIndex: string)

  datatype TestCase = TestCase(testID: string,
                               plaintext: string, // uri
                               ciphertext: string,
                               masterKeys: seq<MasterKey>)

  // TODO move into STDLIB
  method {:extern "ReadFile"} ReadFile(path: string) returns (contents: Result<seq<uint8>>)

  // TODO very specific extern should be more general
  // should probably not require the keylist
  method {:extern "ParseManifest"} ParseManifest(contents: string, keyMap: map<string, Key>) returns (testCases: Result<seq<TestCase>>)

  // TODO very specific extern should be more general
  method {:extern "ParseKeys"} ParseKeys(contents: string) returns (keys: Result<seq<Key>>)

  // TODO blech
  function method TestURIToPath(uri: string): (path: string)
    requires |uri| > 7
    //ensures "file://" + path == uri
  {
    uri[7..]
  }

  method LoadManifest(path: string, keys: map<string, Key>) returns (testCases: Result<seq<TestCase>>) {
      var manifestBytes :- ReadFile(path); // oof UTF8
      var manifestText :- UTF8.Decode(manifestBytes);
      var res := ParseManifest(manifestText, keys); // oof error handling
      return res;
  }

  method LoadKeys(path: string) returns (keys: Result<seq<Key>>) {
      var keysBytes :- ReadFile(path); // oof UTF8
      var keysText :- UTF8.Decode(keysBytes);
      var res := ParseKeys(keysText); // oof error handling
      return res;
  }

  /*
  method TestFramedAESKeyringDecrypt() {
    var plaintext := ReadFile(TestURIToPath(testCase1.plaintext));
    if plaintext.Failure? {
        print "Failure reading plaintext: ", plaintext.error, "\n";
        return;
    }

    var ciphertext := ReadFile(TestURIToPath(testCase1.ciphertext));
    if ciphertext.Failure? {
        print "Failure reading ciphertext: ", ciphertext.error, "\n";
        return;
    }

    var masterKey := testCase1.masterKeys[0];

    var namespace := UTF8.Encode(masterKey.providerID.get);
    var name := UTF8.Encode(masterKey.key.keyID);
    if name.Failure? || namespace.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    }

    var keyRawBytes := Base64.Decode(masterKey.key.material);
    if keyRawBytes.Failure? {
      print "Failure decoding raw key material: ", keyRawBytes.error, "\n";
      return;
    }
    print "material: ", masterKey.key.material, "\n";
    print "keyRawBytes: ", keyRawBytes, "\n";
    //keyRawBytes := Success([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);

    var keyring := new RawAESKeyring.RawAESKeyring(namespace.value, name.value, keyRawBytes.value, EncryptionSuites.AES_GCM_128); // TODO need to grab the right encryption suite from the manifest
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var d := Client.Decrypt(ciphertext.value, cmm);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }

    if d.value != plaintext.value {
        print "did not decrypt to expected plaintext: ", d.value, "\n";
        return;
    }

    print "wow it worked!";
  }

  method TestFramedRSAKeyringDecrypt() {
      var plaintext := ReadFile(TestURIToPath(testCase2.plaintext));
    if plaintext.Failure? {
        print "Failure reading plaintext: ", plaintext.error, "\n";
        return;
    }

    var ciphertext := ReadFile(TestURIToPath(testCase2.ciphertext));
    if ciphertext.Failure? {
        print "Failure reading ciphertext: ", ciphertext.error, "\n";
        return;
    }

    var publicMasterKey := testCase2.masterKeys[0];
    var privateMasterKey := testCase2.masterKeys[1];

    var namespace := UTF8.Encode(publicMasterKey.providerID.get);
    var name := UTF8.Encode(publicMasterKey.key.keyID);
    if name.Failure? || namespace.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    }

    var namespace2 := UTF8.Encode(privateMasterKey.providerID.get);
    var name2 := UTF8.Encode(privateMasterKey.key.keyID);
    if name2.Failure? || namespace2.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    } else if namespace2 != namespace {
      print "Failure: incompatable keys: ", name, name2, namespace, namespace2;
      return;
    }

    var privateKeyRawBytes, publicKeyRawBytes := RSAEncryption.RSA.StringToPEM(publicMasterKey.key.material, privateMasterKey.key.material);

    print "privateKeyRawBytes: ", privateKeyRawBytes, "\n";
    print "publicKeyRawBytes: ", publicKeyRawBytes, "\n";

    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace.value, name.value, RSAEncryption.RSAPaddingMode.PKCS1, 2048, Some(publicKeyRawBytes), Some(privateKeyRawBytes)); // TODO need to grab the right encryption suite from the manifest
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var d := Client.Decrypt(ciphertext.value, cmm);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }

    if d.value != plaintext.value {
        print "did not decrypt to expected plaintext: ", d.value, "\n";
        return;
    }

    print "wow it worked!";
  }

  method TestFramedKMSKeyringDecrypt() {
    var plaintext := ReadFile(TestURIToPath(testCaseKMS.plaintext));
    if plaintext.Failure? {
        print "Failure reading plaintext: ", plaintext.error, "\n";
        return;
    }

    var ciphertext := ReadFile(TestURIToPath(testCaseKMS.ciphertext));
    if ciphertext.Failure? {
        print "Failure reading ciphertext: ", ciphertext.error, "\n";
        return;
    }

    var masterKeyKMS := testCaseKMS.masterKeys[0];

    var namespace := UTF8.Encode(masterKeyKMS.providerID.get);
    var name := UTF8.Encode(masterKeyKMS.key.keyID);
    if name.Failure? || namespace.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    }

    var clientSupplier := new KMSUtils.DefaultClientSupplier();

    var keyring := new KMSKeyring.KMSKeyring(clientSupplier, [], Some(masterKeyKMS.key.keyID), []); // TODO need to grab the right encryption suite from the manifest
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var d := Client.Decrypt(ciphertext.value, cmm);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }

    if d.value != plaintext.value {
        print "did not decrypt to expected plaintext: ", d.value, "\n";
        return;
    }

    print "wow it worked! (KMS)";
  }
  */

  // needs to be run in same directory as test vectors right now
  method Main() {
    var keys := LoadKeys("keys.json");
    if keys.Failure? {
        print keys.error;
        return;
    }

    var keyMap : map<string, Key> := map[];
    var i := 0;
    while i < |keys.value| {
        keyMap := keyMap[keys.value[i].keyIndex := keys.value[i]];
        i := i + 1;
    }
    var testVectors := LoadManifest("manifest.json", keyMap);
    if testVectors.Failure? {
        print testVectors.error;
        return;
    }

    var j := 0;
    var failCount := 0;
    var passCount := 0;
    var skipCount := 0;
    while j < |testVectors.value| {

      var toTest := testVectors.value[j];

      var plaintext := ReadFile(TestURIToPath(toTest.plaintext));
      if plaintext.Failure? {
        print "Failure reading plaintext: ", plaintext.error, "\n";
        return;
      }

      var ciphertext := ReadFile(TestURIToPath(toTest.ciphertext));
      if ciphertext.Failure? {
        print "Failure reading ciphertext: ", ciphertext.error, "\n";
        return;
      }

      var keysToTest := toTest.masterKeys;
      
      var allKMS := true;
      var allKMSIndex := 0;
      while allKMSIndex < |keysToTest| {
          if keysToTest[allKMSIndex].masterKeyType != "aws-kms" {
              allKMS := false;
          }
          allKMSIndex := allKMSIndex + 1;
      }

      if !allKMS {
        //print "Skipping non-KMS test case\n";
        skipCount := skipCount + 1;
      } else {

        var masterKeyKMS := keysToTest[0];

        var clientSupplier := new KMSUtils.DefaultClientSupplier();

        var keyring := new KMSKeyring.KMSKeyring(clientSupplier, [], Some(masterKeyKMS.key.keyID), []); // TODO need to grab the right encryption suite from the manifest
        var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

        var d := Client.Decrypt(ciphertext.value, cmm);
        if d.Failure? {
          print toTest.testID, ": FAILED\n";
          failCount := failCount + 1;
        } else if d.value != plaintext.value {
          print toTest.testID, ": FAILED\n";
          failCount := failCount + 1;
        } else {
          passCount := passCount + 1;
        }
      }
      j := j + 1;
    }
    print "Passed: ", passCount, " Failed: ", failCount, " Skipped: ", skipCount, "\n";
  }
}
