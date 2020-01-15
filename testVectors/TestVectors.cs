using System;
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Text;
using AWSEncryptionSDK;
using DefaultCMMDef;
using KeyringDefs;
using KMSUtils;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using RSAEncryption;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Xunit;

namespace TestVectorTests {

    public abstract class TestVectorData : IEnumerable<object[]> {
        protected Dictionary<string, TestVector> vectorMap;
        protected Dictionary<string, Key> keyMap;
        protected string vectorRoot;

        public TestVectorData() {
            this.vectorRoot = GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            Manifest manifest = ParseManifest(vectorRoot);
            this.vectorMap = manifest.vectorMap;
            string keysPath = ManifestURIToPath(manifest.keys, vectorRoot);
            this.keyMap = ParseKeys(keysPath);
        }

        protected static string GetEnvironmentVariableOrError(string key) {
            string nullableResult = Environment.GetEnvironmentVariable(key);
            if (nullableResult == null) {
                throw new ArgumentException($"Environment Variable {key} must be set");
            }
            return nullableResult;
        }

        protected static Dictionary<string, Key> ParseKeys(string path) {
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

        protected static Manifest ParseManifest(string path) {
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
                throw new ArgumentException($"Manifest file malformed: missing \"keys\" field");
            } 

            return new Manifest(tests.ToObject<Dictionary<string, TestVector>>(), keys.ToString());
        }

        protected static string ManifestURIToPath(string uri, string manifestPath) {
            // Assumes files referenced in manifests starts with 'file://'
            if (!string.Equals(uri.Substring(0, 7), "file://")) {
                throw new ArgumentException($"Malformed filepath in manifest (needs to start with 'file://'): {uri}");
            }
            string parentDir = Directory.GetParent(manifestPath).ToString();

            return Path.Combine(parentDir, uri.Substring(7));
        }

        protected bool VectorContainsMasterkeyOfType(TestVector vector, string typeOfKey) {
            foreach(MasterKey masterKey in vector.masterKeys) {
                if (masterKey.type == typeOfKey) {
                    return true;
                }
            }
            return false;
        }

        protected bool VectorContainsRawAESKey(TestVector vector) {
            foreach(MasterKey masterKey in vector.masterKeys) {
                if (keyMap[masterKey.key].algorithm == "aes") {
                    return true;
                }
            }
            return false;
        }

        public abstract IEnumerator<object[]> GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    public class DecryptTestVectors : TestVectorData {
        public override IEnumerator<object[]> GetEnumerator() {
            foreach(var vectorEntry in vectorMap) {
                string vectorID = vectorEntry.Key;
                TestVector vector = vectorEntry.Value;
                
                // TODO: Once we can test the RawRSAKeyring, this should be replaced with VectorContainsRawAESKey.
                // Once we can test the RawAESKeyring, this should be removed.
                if (VectorContainsRawAESKey(vector)) {
                    continue;
                }

                string plaintextPath = ManifestURIToPath(vector.plaintext, vectorRoot);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                }
                byte[] plaintext = System.IO.File.ReadAllBytes(plaintextPath);

                string ciphertextPath = ManifestURIToPath(vector.ciphertext, vectorRoot);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find ciphertext file at path: {plaintextPath}");
                }
                byte[] ciphertext = System.IO.File.ReadAllBytes(ManifestURIToPath(vector.ciphertext, vectorRoot));

                DefaultCMM cmm = CMMFactory.DecryptCMM(vector, keyMap);

                MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                yield return new object[] { vectorID, cmm, plaintext, ciphertextStream };
            }
        }
    }

    public class EncryptTestVectors : TestVectorData {
        public override IEnumerator<object[]> GetEnumerator() {
            string decryptOracle = GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_DECRYPT_ORACLE_URL");
            HttpClient client = new HttpClient();
            client.DefaultRequestHeaders.Add("Accept", "application/octet-stream");
            foreach(var vectorEntry in vectorMap) {
                string vectorID = vectorEntry.Key;
                TestVector vector = vectorEntry.Value;

                if (VectorContainsMasterkeyOfType(vector, "raw")) {
                    continue;
                }

                string plaintextPath = ManifestURIToPath(vector.plaintext, vectorRoot);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                }
                byte[] plaintext = System.IO.File.ReadAllBytes(plaintextPath);

                DefaultCMM cmm = CMMFactory.EncryptCMM(vector, keyMap);

                yield return new object[] { vectorEntry.Key, cmm, plaintext, client, decryptOracle };
            }
        }
    }

    public class CMMFactory {

        public static DefaultCMM DecryptCMM(TestVector vector, Dictionary<string, Key> keys) {
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(CreateDecryptKeyring(vector, keys));
        }

        public static DefaultCMM EncryptCMM(TestVector vector, Dictionary<string, Key> keys) {
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(CreateEncryptKeyring(vector, keys));
        }

        private static MultiKeyring CreateEncryptKeyring(TestVector vector, Dictionary<string, Key> keys) {
            Keyring generator = CreateKeyring(vector.masterKeys[0], keys[vector.masterKeys[0].key]);
            IList<Keyring> children = vector.masterKeys.Skip(1).Select<MasterKey, Keyring>(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.key])).ToList();
            return Keyrings.MakeMultiKeyring(generator, children.ToArray());
        }
        private static MultiKeyring CreateDecryptKeyring(TestVector vector, Dictionary<string, Key> keys) {
            IList<Keyring> children = vector.masterKeys.Select<MasterKey, Keyring>(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.key])).ToList();
            return Keyrings.MakeMultiKeyring(null, children.ToArray());
        }
        private static Keyring CreateKeyring(MasterKey keyInfo, Key key) {
            if (keyInfo.type == "aws-kms") {
                ClientSupplier clientSupplier = new DefaultClientSupplier();
                return Keyrings.MakeKMSKeyring(clientSupplier, Enumerable.Empty<String>(), key.ID, Enumerable.Empty<String>());
            } else if (keyInfo.type == "raw" && keyInfo.encryptionAlgorithm == "aes") {
                throw new NotYetSupportedException("Cannot test AES keys");
            } else if (keyInfo.type == "raw" && keyInfo.encryptionAlgorithm == "rsa") {
                //TODO: Do we need to do anything with the key.bits field?
                return Keyrings.MakeRawRSAKeyring(
                        Encoding.UTF8.GetBytes(keyInfo.providerID),
                        Encoding.UTF8.GetBytes(key.ID),
                        RSAPAddingFromStrings(keyInfo.paddingAlgorithm, keyInfo.paddingHash),
                        key.type == "public" ? RSA.ParsePEMString(key.material) : null,
                        key.type == "private" ? RSA.ParsePEMString(key.material) : null
                        );
            }
            else {
                throw new Exception("Unsupported keyring type!");
            }
        }
        private static DafnyFFI.RSAPaddingModes RSAPAddingFromStrings(string strAlg, string strHash) {
            return (strAlg, strHash) switch {
                ("pkcs1", _) => DafnyFFI.RSAPaddingModes.PKCS1,
                    ("oaep-mgf1", "sha1") => DafnyFFI.RSAPaddingModes.OAEP_SHA1,
                    ("oaep-mgf1", "sha256") => DafnyFFI.RSAPaddingModes.OAEP_SHA256,
                    ("oaep-mgf1", "sha384") => DafnyFFI.RSAPaddingModes.OAEP_SHA384,
                    ("oaep-mgf1", "sha512") => DafnyFFI.RSAPaddingModes.OAEP_SHA512,
                    _ => throw new Exception("Unsupported RSA Padding " + strAlg + strHash)
            };
        }
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
        [ClassData (typeof(DecryptTestVectors))]
        public void CanDecryptTestVector(string vectorID, DefaultCMM cmm, byte[] expectedPlaintext, MemoryStream ciphertextStream) {
            try {
                MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertextStream, cmm);
                byte[] result = decodedStream.ToArray();
                Assert.Equal(expectedPlaintext, result);
            } catch (Exception e) when (string.Equals(e.Message, "Unframed Message Decryption Unimplemented")) {
                // TODO While unframed message deserialization is unimplemented, test that the correct error is thrown
                // TODO Ideally we would check against a specific, user-exposed Error class here
                Skip.If(true);
            }
        }

        [Theory]
        [ClassData (typeof(EncryptTestVectors))]
        public void CanEncryptTestVector(string vectorID, DefaultCMM cmm, byte[] plaintext, HttpClient client, string decryptOracle) {
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(new MemoryStream(plaintext), cmm, new Dictionary<string, string>());

            StreamContent content = new StreamContent(ciphertext);
            content.Headers.Add("Content-Type", "application/octet-stream");

            var response = client.PostAsync(decryptOracle, content).Result;
            Assert.Equal(HttpStatusCode.OK, response.StatusCode);
            Assert.Equal(plaintext, response.Content.ReadAsByteArrayAsync().Result);
        }
    }
}
