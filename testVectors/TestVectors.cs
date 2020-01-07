using System;
using System.Text;
using Newtonsoft.Json.Linq;
using System.Linq;
using System.Collections.Generic;
using System.IO;
using KeyringDefs;
using KMSUtils;
using Newtonsoft.Json;
using Xunit;
using System.Collections;

namespace TestVectorTests {

    public class TestVectorData : IEnumerable<object[]> {

        public static Dictionary<string, Key> ParseKeys(string path) {
            if (!File.Exists(path)) {
                throw new ArgumentException($"Could not find keys file at path: {path}");
            }
            string contents = System.IO.File.ReadAllText(path);
            JObject keyManifest = JObject.Parse(contents);
            JToken keys = keyManifest["keys"];
            if (keys == null) {
                throw new ArgumentException($"Key file malformed: missing \"keys\" field");
            } 
            return keys.ToObject<Dictionary<string, Key>>();
        }

        public static Manifest ParseManifest(string path) {
            if (!File.Exists(path)) {
                throw new ArgumentException($"Could not find manifest file at path: {path}");
            }
            string contents = System.IO.File.ReadAllText(path);
            JObject manifest = JObject.Parse(contents);
            
            JToken tests = manifest["tests"];
            if (tests == null) {
                throw new ArgumentException($"Manifest file malformed: missing \"tests\" field");
            } 

            JToken keys = manifest["keys"];
            if (keys == null) {
                throw new ArgumentException($"Manifest file malformed: missing \"manifest\" field");
            } 

            return new Manifest(tests.ToObject<Dictionary<string, TestVector>>(), keys.ToString());
        }

        public static string ManifestURIToPath(string uri, string manifestPath) {
            // Assumes files referenced in manifests starts with 'file://'
            if (!string.Equals(uri.Substring(0, 7), "file://")) {
                throw new ArgumentException($"Malformed filepath in manifest (needs to start with 'file://'): {uri}");
            }
            string parentDir = Directory.GetParent(manifestPath).ToString();

            return Path.Combine(parentDir, uri.Substring(7));
        }

        public IEnumerator<object[]> GetEnumerator() {
            string manifestPath = Environment.GetEnvironmentVariable("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            if (manifestPath == null) {
                throw new ArgumentException($"Environment Variable DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH must be set");
            }

            Manifest manifest = ParseManifest(manifestPath);
            Dictionary<string, TestVector> vectorMap = manifest.vectorMap;

            string keysPath = ManifestURIToPath(manifest.keys, manifestPath);
            Dictionary<string, Key> keyMap = ParseKeys(keysPath);

            foreach(var vectorEntry in vectorMap) {
                string vectorID = vectorEntry.Key;
                TestVector vector = vectorEntry.Value;
                
                string plaintextPath = ManifestURIToPath(vector.plaintext, manifestPath);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                }
                byte[] plaintext = System.IO.File.ReadAllBytes(plaintextPath);

                string ciphertextPath = ManifestURIToPath(vector.ciphertext, manifestPath);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find ciphertext file at path: {plaintextPath}");
                }
                byte[] ciphertext = System.IO.File.ReadAllBytes(ManifestURIToPath(vector.ciphertext, manifestPath));

                // TODO This is temporary logic to skip non-KMS test cases. Remove once testing all vectors.
                bool isKMSTestVector = false;
                foreach(var masterKey in vector.masterKeys) {
                    if (keyMap[masterKey.key].type == "aws-kms") {
                        isKMSTestVector = true;
                        break;
                    }
                }

                if (!isKMSTestVector) {
                    continue;
                }

                // Construct the KMS Keyring to test
                // TODO This should be more generic. Master keys are set up with decryptable key at index 0 in current set of test vectors
                MasterKey keyToTest = vector.masterKeys[0];
                ClientSupplier clientSupplier = new DefaultClientSupplier();
                Keyring keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                    clientSupplier, Enumerable.Empty<String>(), keyMap[keyToTest.key].ID, Enumerable.Empty<String>());
                CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
                MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                yield return new object[] { cmm, plaintext, ciphertextStream };
            }
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        public bool decrypt { get; set; }
        public bool encrypt { get; set; }
        public string type { get; set; }
        [JsonProperty("key-id")]
        public string ID { get; set; }
        public string algorithm { get; set; }
        public ushort bits { get; set; }
        public string encoding { get; set; }
        public string material { get; set; }
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        public string type { get; set; }
        public string key { get; set; }
        [JsonProperty("provider-id")]
        public string providerID { get; set; }
        [JsonProperty("encryption-algorithm")]
        public string encryptionAlgorithm { get; set; }
        [JsonProperty("padding-algorithm")]
        public string paddingAlgorithm { get; set; }
        [JsonProperty("padding-hash")]
        public string paddingHash { get; set; }
    }

    public class TestVector {
        public string plaintext { get; set; }
        public string ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> masterKeys { get; set; }
    }

    public class Manifest {
        public Dictionary<string, TestVector> vectorMap { get; set; }
        public string keys { get; set; }

        public Manifest(Dictionary<string, TestVector> vectorMap, string keys) {
            this.vectorMap = vectorMap;
            this.keys = keys;
        }
    } 

    public class TestVectorDecryptTests {
        [SkippableTheory]
        [ClassData (typeof(TestVectorData))]
        public void CanDecryptTestVector(CMMDefs.CMM cmm, byte[] expectedPlaintext, MemoryStream ciphertextStream) {
            try {
                MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertextStream, cmm);
                byte[] result = decodedStream.ToArray();
                Assert.Equal(expectedPlaintext, result);
            } catch (Exception e) {
                // TODO While unframed message deserialization is unimplemented, test that the correct error is thrown
                Skip.If(string.Equals(e.Message, "Unframed Message Decryption Unimplemented"));

                // In the case this isn't the skippable error, we still want the error to bubble up
                throw e;
            }
        }
    }
}
