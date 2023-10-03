// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;

using Xunit;

using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;

namespace TestVectors.Runner {
    public abstract class TestVectorData : IEnumerable<object[]> {
        protected readonly Dictionary<string, DecryptVector> VectorMap;
        protected readonly Dictionary<string, Key> KeyMap;
        protected readonly string VectorRoot;

        protected TestVectorData() {
            this.VectorRoot = Utils.GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            DecryptManifest manifest = Utils.LoadObjectFromPath<DecryptManifest>(VectorRoot);
            this.VectorMap = manifest.VectorMap;
            string keysPath = Utils.ManifestUriToPath(manifest.KeysUri, VectorRoot);
            this.KeyMap = Utils.LoadObjectFromPath<KeyManifest>(keysPath).Keys;
        }

        protected static bool VectorContainsMasterKeyOfType(DecryptVector vector, string typeOfKey)
        {
            return vector.MasterKeys.Any(masterKey => masterKey.Type == typeOfKey);
        }

        public abstract IEnumerator<object[]> GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

        // Simplistic method for narrowing down which vectors to target. Add any permanent skips
        // here (e.g. for unsupported features) or temporarily update if you want to
        // test certain vectors
        protected static bool TargetVector(KeyValuePair<string, DecryptVector> entry)
        {
            if (entry.Value.DecryptionMethod != null && entry.Value.DecryptionMethod.Equals("streaming-unsigned-only")) {
                // These vectors specifically target streaming APIs. Since we do not
                // yet support streaming, we cannot test against these.
                return false;
            }
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

                DecryptVector vector = vectorEntry.Value;
                byte[] plaintext = null;
                if (vector.Result.Output != null)
                {
                    string plaintextPath = Utils.ManifestUriToPath(vector.Result.Output.Plaintext, VectorRoot);
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

                string ciphertextPath = Utils.ManifestUriToPath(vector.Ciphertext, VectorRoot);
                if (!File.Exists(ciphertextPath)) {
                    throw new ArgumentException($"Could not find ciphertext file at path: {ciphertextPath}");
                }
                byte[] ciphertext = File.ReadAllBytes(Utils.ManifestUriToPath(vector.Ciphertext, VectorRoot));

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
        [SkippableTheory]
        [ClassData (typeof(DecryptTestVectors))]
        public void CanDecryptTestVector(
            string vectorId,
            DecryptVector vector,
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
                AwsEncryptionSdkConfig config = new AwsEncryptionSdkConfig
                {
                    CommitmentPolicy = CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT
                };
                IAwsEncryptionSdk encryptionSdk = AwsEncryptionSdkFactory.CreateAwsEncryptionSdk(config);

                ICryptographicMaterialsManager cmm = MaterialProviderFactory.CreateDecryptCmm(vector, keyMap);

                DecryptInput decryptInput = new DecryptInput
                {
                    Ciphertext = ciphertextStream,
                    MaterialsManager = cmm,
                };
                AWS.EncryptionSDK.DecryptOutput decryptOutput = encryptionSdk.Decrypt(decryptInput);
                if (expectedError != null)
                {
                    throw new Exception(
                        $"Test vector {vectorId} succeeded when it shouldn't have"
                    );
                }

                byte[] result = decryptOutput.Plaintext.ToArray();
                Assert.Equal(expectedPlaintext, result);
            }
            catch (Exception e) when (
                e is AwsEncryptionSdkException ||
                e is AwsCryptographicMaterialProvidersException
            )
            {
                if (expectedPlaintext != null)
                {
                    // Test was not expected to fail
                    throw;
                }
            }
        }
    }
}
