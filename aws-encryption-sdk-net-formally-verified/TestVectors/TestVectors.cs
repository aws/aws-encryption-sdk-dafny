// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Http;
using System.Text;
using Amazon;
using Amazon.KeyManagementService;
using RSAEncryption;

using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Xunit;

using Aws.Crypto;
using Aws.Esdk;
using Xunit.Sdk;
using ConfigurationDefaults = Aws.Esdk.ConfigurationDefaults;

namespace TestVectorTests {

    public abstract class TestVectorData : IEnumerable<object[]> {
        protected readonly Dictionary<string, TestVector> VectorMap;
        protected readonly Dictionary<string, Key> KeyMap;
        protected readonly string VectorRoot;

        protected TestVectorData() {
            this.VectorRoot = GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            Manifest manifest = ParseManifest(VectorRoot);
            this.VectorMap = manifest.VectorMap;
            string keysPath = ManifestUriToPath(manifest.Keys, VectorRoot);
            this.KeyMap = ParseKeys(keysPath);
        }

        protected static string GetEnvironmentVariableOrError(string key) {
            string nullableResult = Environment.GetEnvironmentVariable(key);
            if (nullableResult == null) {
                throw new ArgumentException($"Environment Variable {key} must be set");
            }
            return nullableResult;
        }

        private static Dictionary<string, Key> ParseKeys(string path) {
            if (!File.Exists(path)) {
                throw new ArgumentException($"Could not find keys file at path: {path}");
            }
            string contents = File.ReadAllText(path);
            JObject keyManifest = JObject.Parse(contents);
            JToken keys = keyManifest["keys"];
            if (keys == null) {
                throw new ArgumentException($"Key file malformed: missing \"keys\" field");
            }
            return keys.ToObject<Dictionary<string, Key>>();
        }

        private static Manifest ParseManifest(string path) {
            if (!File.Exists(path)) {
                throw new ArgumentException($"Could not find manifest file at path: {path}");
            }
            string contents = File.ReadAllText(path);
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

        protected static string ManifestUriToPath(string uri, string manifestPath) {
            // Assumes files referenced in manifests starts with 'file://'
            if (!string.Equals(uri.Substring(0, 7), "file://")) {
                throw new ArgumentException($"Malformed filepath in manifest (needs to start with 'file://'): {uri}");
            }
            string parentDir = Directory.GetParent(manifestPath).ToString();

            return Path.Combine(parentDir, uri.Substring(7));
        }

        protected static bool VectorContainsMasterKeyOfType(TestVector vector, string typeOfKey)
        {
            return vector.MasterKeys.Any(masterKey => masterKey.Type == typeOfKey);
        }

        public abstract IEnumerator<object[]> GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
        
        // TODO remove or make more robust. Leaving it in for now because it's useful for testing
        protected static bool TargetVector(KeyValuePair<string, TestVector> entry)
        {
            if (entry.Value.MasterKeys.Any(masterKey => masterKey.Key != null && masterKey.Key.StartsWith("aes")))
            {
                return true;
            }

            return false;
        }
    }

    public class DecryptTestVectors : TestVectorData {
        public override IEnumerator<object[]> GetEnumerator() {
            foreach(var vectorEntry in VectorMap) {

                // TODO remove
                if (!TargetVector(vectorEntry))
                {
                    continue;
                }
                
                TestVector vector = vectorEntry.Value;
                byte[] plaintext = null;
                if (vector.Result.Output != null)
                {
                    string plaintextPath = ManifestUriToPath(vector.Result.Output.Plaintext, VectorRoot);
                    if (!File.Exists(plaintextPath))
                    {
                        throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                    }

                    plaintext = File.ReadAllBytes(plaintextPath);
                }

                string errorMessage = null;
                if (vector.Result.Error != null)
                {
                    errorMessage = vector.Result.Error.ErrorMessage;
                }

                string ciphertextPath = ManifestUriToPath(vector.Ciphertext, VectorRoot);
                if (!File.Exists(ciphertextPath)) {
                    throw new ArgumentException($"Could not find ciphertext file at path: {ciphertextPath}");
                }
                byte[] ciphertext = File.ReadAllBytes(ManifestUriToPath(vector.Ciphertext, VectorRoot));

                MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                yield return new object[] { vectorEntry.Key, vector, KeyMap, plaintext, errorMessage, ciphertextStream };
            }
        }
    }

    public class EncryptTestVectors : TestVectorData {
        public override IEnumerator<object[]> GetEnumerator() {
            string decryptOracle = GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_DECRYPT_ORACLE_URL");
            HttpClient client = new HttpClient();
            client.DefaultRequestHeaders.Add("Accept", "application/octet-stream");
            foreach(var vectorEntry in VectorMap) {
                TestVector vector = vectorEntry.Value;

                string plaintextPath = ManifestUriToPath(vector.Result.Output.Plaintext, VectorRoot);
                if (!File.Exists(plaintextPath)) {
                    throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                }
                byte[] plaintext = File.ReadAllBytes(plaintextPath);

                yield return new object[] { vectorEntry.Key, vector, KeyMap, plaintext, client, decryptOracle };
            }
        }
    }

    public static class CmmFactory {

        public static ICryptographicMaterialsManager DecryptCmm(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            CreateDefaultCryptographicMaterialsManagerInput input = new CreateDefaultCryptographicMaterialsManagerInput
            {
                Keyring = CreateDecryptKeyring(vector, keys)
            };
            return materialProviders.CreateDefaultCryptographicMaterialsManager(input);
        }

        public static ICryptographicMaterialsManager EncryptCmm(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            CreateDefaultCryptographicMaterialsManagerInput input = new CreateDefaultCryptographicMaterialsManagerInput
            {
                Keyring = CreateEncryptKeyring(vector, keys)
            };
            return materialProviders.CreateDefaultCryptographicMaterialsManager(input);
        }

        private static IKeyring CreateEncryptKeyring(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            IKeyring generator = CreateKeyring(vector.MasterKeys[0], keys[vector.MasterKeys[0].Key]);
            List<IKeyring> children = vector.MasterKeys.Skip(1)
                .Select(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.Key])).ToList();
            CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput 
            {
                Generator = generator,
                ChildKeyrings = children
            };

            return materialProviders.CreateMultiKeyring(createMultiKeyringInput);
        }
        private static IKeyring CreateDecryptKeyring(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            List<IKeyring> children = vector.MasterKeys
                .Select(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.Key])).ToList();
            CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput 
            {
                Generator = children[0], // TODO: back to null
                ChildKeyrings = children
            };

            return materialProviders.CreateMultiKeyring(createMultiKeyringInput);
        }
        private static IKeyring CreateKeyring(MasterKey keyInfo, Key key) {
            // TODO: maybe make this a class variable so we're not constantly re-creating it
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            if (keyInfo.Type == "aws-kms") {
                CreateStrictAwsKmsKeyringInput createKeyringInput = new CreateStrictAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateStrictAwsKmsKeyring(createKeyringInput);
            } else if (keyInfo.Type == "aws-kms-mrk-aware") {
                CreateMrkAwareStrictAwsKmsKeyringInput createKeyringInput = new CreateMrkAwareStrictAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateMrkAwareStrictAwsKmsKeyring(createKeyringInput);
            } else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "aes") {
                CreateRawAesKeyringInput createKeyringInput = new CreateRawAesKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    WrappingKey = new MemoryStream(Convert.FromBase64String(key.Material)),
                    WrappingAlg = AesAlgorithmFromBits(key.Bits),
                };

                return materialProviders.CreateRawAesKeyring(createKeyringInput);
            } else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "private") {
                Keyrings.RSAPaddingModes padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                ImportRSAKeyInput keyInput = new ImportRSAKeyInput
                {
                    Pem = key.Material,
                    Strength = key.Bits,
                    PaddingScheme = padding
                }
                Aws.Crypto.IKey rsaKey = materialProviders.ImportPrivateRSAKey(keyInput);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderIdm
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PrivateKey = rsaKey
                }
                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            }
            else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "public") {
                Keyrings.RSAPaddingModes padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                ImportRSAKeyInput keyInput = new ImportRSAKeyInput
                {
                    Pem = key.Material,
                    Strength = key.Bits,
                    PaddingScheme = padding
                }
                Aws.Crypto.IKey rsaKey = materialProviders.ImportPublicRSAKey(keyInput);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderIdm
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PublicKey = rsaKey
                }
                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            }
            else {
                throw new Exception("Unsupported keyring type!");
            }
        }
        private static AesWrappingAlg AesAlgorithmFromBits(ushort bits) {
            return bits switch {
                128 => AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16,
                192 => AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16,
                256 => AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16,
                _ => throw new Exception("Unsupported AES wrapping algorithm")
            };
        }

        private static Keyrings.RSAPaddingModes RSAPAddingFromStrings(string strAlg, string strHash) {
            return (strAlg, strHash) switch {
                ("pkcs1", _) => Keyrings.RSAPaddingModes.PKCS1,
                ("oaep-mgf1", "sha1") => Keyrings.RSAPaddingModes.OAEP_SHA1,
                ("oaep-mgf1", "sha256") => Keyrings.RSAPaddingModes.OAEP_SHA256,
                ("oaep-mgf1", "sha384") => Keyrings.RSAPaddingModes.OAEP_SHA384,
                ("oaep-mgf1", "sha512") => Keyrings.RSAPaddingModes.OAEP_SHA512,
                _ => throw new Exception("Unsupported RSA Padding " + strAlg + strHash)
            };
        }

        private static RegionEndpoint GetRegionForArn(string keyId)
        {
            string[] split = keyId.Split(":");
            string region = split[3];
            return RegionEndpoint.GetBySystemName(region);
        }
    }

    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        public bool Decrypt { get; set; }
        public bool Encrypt { get; set; }
        public string Type { get; set; }
        [JsonProperty("key-id")]
        public string Id { get; set; }
        public string Algorithm { get; set; }
        public ushort Bits { get; set; }
        public string Encoding { get; set; }
        public string Material { get; set; }
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        public string Type { get; set; }
        public string Key { get; set; }
        [JsonProperty("provider-id")]
        public string ProviderId { get; set; }
        [JsonProperty("encryption-algorithm")]
        public string EncryptionAlgorithm { get; set; }
        [JsonProperty("padding-algorithm")]
        public string PaddingAlgorithm { get; set; }
        [JsonProperty("padding-hash")]
        public string PaddingHash { get; set; }
    }

    public class TestVector {
        public string Ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }

        public TestVectorResult Result { get; set; }
    }

    public class TestVectorResult
    {
        public TestVectorOutput Output { get; set; }
        public TestVectorError Error { get; set; }
    }

    public class TestVectorOutput
    {
        public string Plaintext { get; set; }
    }
    public class TestVectorError
    {
        [JsonProperty("error-description")]
        public string ErrorMessage { get; set; }
    }

    public class Manifest {
        public Dictionary<string, TestVector> VectorMap { get; set; }
        public string Keys { get; set; }

        public Manifest(Dictionary<string, TestVector> vectorMap, string keys) {
            this.VectorMap = vectorMap;
            this.Keys = keys;
        }
    }

    public class TestVectorDecryptTests {
        #pragma warning disable xUnit1026 // Suppress Unused argument warnings for vectorID.
        [SkippableTheory]
        [ClassData (typeof(DecryptTestVectors))]
        public void CanDecryptTestVector(
            string vectorId,
            TestVector vector,
            Dictionary<string, Key> keyMap,
            byte[] expectedPlaintext,
            string expectedError,
            MemoryStream ciphertextStream
        ) {
            if (expectedPlaintext != null && expectedError != null)
            {
                throw new ArgumentException(
                    $"Test vector {vectorId} has both plaintext and error in its expected result, this is not possible"
                );
            }

            // TODO remove
            if (vector.MasterKeys.Any(masterKey => masterKey.Key != null && masterKey.Key.StartsWith("rsa")))
            {
                throw new Exception($"RSA keyrings not yet supported");
            }
            // End TODO

            try
            {
                AwsEncryptionSdkClientConfig config = new AwsEncryptionSdkClientConfig
                {
                    ConfigDefaults = ConfigurationDefaults.V1
                };
                IAwsEncryptionSdk encryptionSdkClient = new AwsEncryptionSdkClient(config);

                ICryptographicMaterialsManager cmm = CmmFactory.DecryptCmm(vector, keyMap);

                DecryptInput decryptInput = new DecryptInput
                {
                    Ciphertext = ciphertextStream,
                    MaterialsManager = cmm,
                };
                DecryptOutput decryptOutput = encryptionSdkClient.Decrypt(decryptInput);

                if (expectedError != null)
                {
                    throw new Exception(
                        $"Test vector {vectorId} succeeded when it shouldn't have"
                    );
                }


                byte[] result = decryptOutput.Plaintext.ToArray();
                Assert.Equal(expectedPlaintext, result);
            }
            catch (Exception)
            {
                if (expectedPlaintext != null)
                {
                    // Test was not expected to fail
                    // TODO: don't allow DafnyHalt and maybe some other set of exceptions that we know are not right
                    throw;
                }

                if (expectedError != null)
                {
                    // TODO: maybe do some comparison on error messages. Or if not, at least make sure the types are
                    // right? A DafnyHalt exception is definitely bad.
                    // For now, suffice to say the test correctly failed.
                }
            }
        }

        #pragma warning disable xUnit1026 // Suppress Unused argument warnings for vectorID.
        [Theory]
        [ClassData (typeof(EncryptTestVectors))]
        public void CanEncryptTestVector(
            string vectorID,
            TestVector vector,
            Dictionary<string, Key> keyMap,
            byte[] plaintext,
            HttpClient client,
            string decryptOracle
        ) {
            // TODO remove
            if (vector.MasterKeys.Any(masterKey => masterKey.Key != null && masterKey.Key.StartsWith("rsa")))
            {
                throw new Exception($"RSA keyrings not yet supported");
            }
            // End TODO

            AwsEncryptionSdkClientConfig config = new AwsEncryptionSdkClientConfig
            {
                ConfigDefaults = ConfigurationDefaults.V1
            };
            IAwsEncryptionSdk encryptionSdkClient = new AwsEncryptionSdkClient(config);

            ICryptographicMaterialsManager cmm = CmmFactory.DecryptCmm(vector, keyMap);

            EncryptInput encryptInput = new EncryptInput
            {
                Plaintext = new MemoryStream(plaintext),
                MaterialsManager = cmm
            };
            EncryptOutput encryptOutput = encryptionSdkClient.Encrypt(encryptInput);
            MemoryStream ciphertext = encryptOutput.Ciphertext;

            StreamContent content = new StreamContent(ciphertext);
            content.Headers.Add("Content-Type", "application/octet-stream");

            var response = client.PostAsync(decryptOracle, content).Result;
            Assert.Equal(HttpStatusCode.OK, response.StatusCode);
            Assert.Equal(plaintext, response.Content.ReadAsByteArrayAsync().Result);
        }
    }
}
