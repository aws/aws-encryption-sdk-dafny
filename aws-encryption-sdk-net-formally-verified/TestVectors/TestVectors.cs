// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;

using Newtonsoft.Json.Linq;
using Xunit;

using Aws.Crypto;
using Aws.Esdk;
using ConfigurationDefaults = Aws.Esdk.ConfigurationDefaults;

namespace TestVectors.Runner {
    public abstract class TestVectorData : IEnumerable<object[]> {
        protected readonly Dictionary<string, TestVector> VectorMap;
        protected readonly Dictionary<string, Key> KeyMap;
        protected readonly string VectorRoot;

        protected TestVectorData() {
            this.VectorRoot = GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            DecryptManifest manifest = ParseManifest(VectorRoot);
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

        private static DecryptManifest ParseManifest(string path) {
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

            return new DecryptManifest(tests.ToObject<Dictionary<string, TestVector>>(), keys.ToString());
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

        // Simplistic method for narrowing down which vectors to target. For now, no-op.
        // Update if you want to test certain vectors
        protected static bool TargetVector(KeyValuePair<string, TestVector> entry)
        {
            return true;
        }
    }

    public class DecryptTestVectors : TestVectorData {
        public override IEnumerator<object[]> GetEnumerator()
        {
            long count = 0;
            foreach(var vectorEntry in VectorMap) {

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
                count++;
            }

            // If nothing gets `yield return`-ed, xUnit gives an unclear error message. This error is better.
            if (count == 0)
            {
                throw new Exception("No targeted vectors found");
            }
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

            try
            {
                AwsEncryptionSdkClientConfig config = new AwsEncryptionSdkClientConfig
                {
                    ConfigDefaults = ConfigurationDefaults.V1,
                    CommitmentPolicy = CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT
                };
                IAwsEncryptionSdk encryptionSdkClient = new AwsEncryptionSdkClient(config);

                ICryptographicMaterialsManager cmm = MaterialProviderFactory.DecryptCmm(vector, keyMap);

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
    }
}
