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
            string contents = System.IO.File.ReadAllText(path);
            JObject keyManifest = JObject.Parse(contents);
            return keyManifest["keys"].ToObject<Dictionary<string, Key>>();
        }

        public static Dictionary<string, TestVector> ParseVectors(string path) {
            string contents = System.IO.File.ReadAllText(path);
            JObject manifest = JObject.Parse(contents);
            return manifest["tests"].ToObject<Dictionary<string, TestVector>>();
        }

        public static string TestURIToPath(string uri) {
            // TODO clean up. Currently assumes starts with 'file://' and is relative from bin/Debug/netcoreapp3.0/
            return "../../../" + uri.Substring(7);
        }

        public IEnumerator<object[]> GetEnumerator() {
            Dictionary<string, Key> keyMap = ParseKeys("../../../keys.json"); // TODO should get this from manifest
            Dictionary<string, TestVector> vectorMap = ParseVectors("../../../manifest.json"); // TODO should get this from command line

            foreach(var vectorEntry in vectorMap) {
                string vectorID = vectorEntry.Key;
                TestVector vector = vectorEntry.Value;

                byte[] plaintext = System.IO.File.ReadAllBytes(TestURIToPath(vector.plaintext));
                byte[] ciphertext = System.IO.File.ReadAllBytes(TestURIToPath(vector.ciphertext));

                // TODO This is temporary logic to skip non-KMS test cases. Remove once testing all vectors.
                bool isKMSTestVector = true;
                foreach(var masterKey in vector.masterKeys) {
                    if (keyMap[masterKey.key].type != "aws-kms") {
                        isKMSTestVector = false;
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

                // TODO check all independent
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
