using System;
using System.Text;
using Newtonsoft.Json.Linq;
using System.Linq;
using System.Collections.Generic;
using System.IO;
using KeyringDefs;
using KMSUtils;
using Newtonsoft.Json;

namespace TestVectors {

    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        [JsonProperty("decrypt")]
        public bool decrypt { get; set; }
        [JsonProperty("encrypt")]
        public bool encrypt { get; set; }
        [JsonProperty("type")]
        public string type { get; set; }
        [JsonProperty("key-id")]
        public string ID { get; set; }
        [JsonProperty("algorithm")]
        public string algorithm { get; set; }
        [JsonProperty("bits")]
        public ushort bits { get; set; }
        [JsonProperty("encoding")]
        public string encoding { get; set; }
        [JsonProperty("material")]
        public string material { get; set; }  
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        [JsonProperty("type")]
        public string type { get; set; }
        [JsonProperty("key")]
        public string key { get; set; } // TODO or load Key directly?
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
        [JsonProperty("plaintext")]
        public string plaintext { get; set; }
        [JsonProperty("ciphertext")]
        public string ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> masterKeys { get; set; }
    }

    public partial class __default {

        public static Dictionary<string, Key> ParseKeys(string path) {
            string contents = System.IO.File.ReadAllText(path);
            JObject keyManifest = JObject.Parse(contents);
            return keyManifest["keys"].ToObject<Dictionary<string, Key>>();
        }

        public static Dictionary<string, TestVector> ParseVectorsFromManifest(string path) {
            string contents = System.IO.File.ReadAllText(path);
            JObject manifest = JObject.Parse(contents);
            return manifest["tests"].ToObject<Dictionary<string, TestVector>>();
        }

        public static string TestURIToPath(string uri) {
            // TODO clean up. currently assumes starts with file://
            return uri.Substring(7);
        }

        // TODO sane error handling
        public static void Main() {
            Dictionary<string, Key> keyMap = ParseKeys("keys.json"); // TODO should get this from manifest
            Dictionary<string, TestVector> vectorMap = ParseVectorsFromManifest("manifest.json"); // TODO should get this from command line

            // TODO should collect these and related stats into one object
            int failCount = 0;
            int passCount = 0;
            int skipCount = 0;

            foreach(var vectorEntry in vectorMap) {
                string vectorID = vectorEntry.Key;
                TestVector vector = vectorEntry.Value;

                byte[] plaintext = System.IO.File.ReadAllBytes(TestURIToPath(vector.plaintext));
                byte[] ciphertext = System.IO.File.ReadAllBytes(TestURIToPath(vector.ciphertext));

                // TODO temporary logic to skip non-KMS test cases
                bool isKMSTestVector = true;
                foreach(var masterKey in vector.masterKeys) {
                    if (keyMap[masterKey.key].type != "aws-kms") {
                        isKMSTestVector = false;
                    }
                }

                if (!isKMSTestVector) {
                    skipCount++;
                    continue;
                }

                // TODO master keys set up with decryptable key at index 0 in current set of test vectors
                MasterKey keyToTest = vector.masterKeys[0];

                ClientSupplier clientSupplier = new DefaultClientSupplier();

                Keyring keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                    clientSupplier, Enumerable.Empty<String>(), keyMap[keyToTest.key].ID, Enumerable.Empty<String>());
            
                CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
                MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                byte[] result = new byte[0];
                try {
                    MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertextStream, cmm);
                    result = decodedStream.ToArray();
                } catch (Exception e) {
                    failCount++;
                    Console.WriteLine(vectorID + ": FAILED");
                    continue;
                }
                
                if (!result.SequenceEqual(plaintext)) {
                    failCount++;
                    Console.WriteLine(vectorID + ": FAILED");
                } else {
                    passCount++;
                }
            }
            // TODO make stat tracking sane
            Console.WriteLine("Passed: " + passCount + " Failed: " + failCount + " Skipped: " + skipCount);
        }
    }
}
