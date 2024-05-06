// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Xunit;
using Xunit.Abstractions;

using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Exception = System.Exception;
// ReSharper disable SuggestVarOrType_SimpleTypes
// ReSharper disable SuggestVarOrType_Elsewhere
// ReSharper disable SuggestVarOrType_BuiltInTypes

namespace TestVectors.Runner {
    
    static class RunnerUtils
    {
        internal static NetV4_0_0_RetryPolicy fromString(string input)
        {
            return input.ToLower() switch
            {
                "forbid" => NetV4_0_0_RetryPolicy.FORBID_RETRY,
                "allow" => NetV4_0_0_RetryPolicy.ALLOW_RETRY,
                _ => throw new ArgumentException(
                    $"Net v4.0.0 retry policy MUST be forbid or allow, got: {input}")
            };
        }
    }
    public abstract class TestVectorData : IEnumerable<object[]> {
        protected readonly Dictionary<string, DecryptVector> VectorMap;
        protected readonly Dictionary<string, Key> KeyMap;
        protected readonly string VectorRoot;
        protected readonly NetV4_0_0_RetryPolicy _netV400RetryPolicy;

        protected TestVectorData() {
            this.VectorRoot = Utils.GetEnvironmentVariableOrError("DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH");
            this._netV400RetryPolicy = Utils.GetEnvironmentVariableOrDefault("ESDK_NET_V400_POLICY",
                NetV4_0_0_RetryPolicy.ALLOW_RETRY, RunnerUtils.fromString);
            DecryptManifest manifest = Utils.LoadObjectFromPath<DecryptManifest>(VectorRoot);
            this.VectorMap = manifest.VectorMap;
            string keysPath = Utils.ManifestUriToPath(manifest.KeysUri, VectorRoot);
            this.KeyMap = Utils.LoadObjectFromPath<KeyManifest>(keysPath).Keys;
        }

        protected static bool VectorContainsMasterKeyOfType(DecryptVector vector, string typeOfKey)
        {
            return vector.MasterKeys != null && vector.MasterKeys.Any(masterKey => masterKey.Type == typeOfKey);
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
                if (vector.Result is {Output: not null})
                {
                    if (vector.Result.Output.Plaintext != null)
                    {
                        string plaintextPath = Utils.ManifestUriToPath(vector.Result.Output.Plaintext, VectorRoot);
                        if (!File.Exists(plaintextPath))
                        {
                            throw new ArgumentException($"Could not find plaintext file at path: {plaintextPath}");
                        }

                        plaintext = File.ReadAllBytes(plaintextPath);
                    }
                }

                string errorMessage = null;
                if (vector.Result != null && vector.Result.Error != null)
                {
                    errorMessage = vector.Result.Error.ErrorMessage;
                }

                string ciphertextPath = Utils.ManifestUriToPath(vector.Ciphertext, VectorRoot);
                if (!File.Exists(ciphertextPath)) {
                    throw new ArgumentException($"Could not find ciphertext file at path: {ciphertextPath}");
                }
                byte[] ciphertext = File.ReadAllBytes(Utils.ManifestUriToPath(vector.Ciphertext, VectorRoot));

                MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                yield return new object[] { vectorEntry.Key, vector, KeyMap, plaintext, errorMessage, ciphertextStream, _netV400RetryPolicy };
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
        private readonly ITestOutputHelper testLogging;
        private static string OPAQUE_ERROR_NULL_OBJ_MSG = "Unknown Unexpected Error";
        public TestVectorDecryptTests(ITestOutputHelper testLogging)
        {
            this.testLogging = testLogging;
        }

        [SkippableTheory]
        [ClassData (typeof(DecryptTestVectors))]
        public void CanDecryptTestVector(
            string vectorId,
            DecryptVector vector,
            Dictionary<string, Key> keyMap,
            byte[] expectedPlaintext,
            string expectedError,
            MemoryStream ciphertextStream,
            NetV4_0_0_RetryPolicy _netV400RetryPolicy
        ) {
            if (expectedPlaintext != null && expectedError != null)
            {
                throw new ArgumentException(
                    $"Test vector {vectorId} has both plaintext and error in its expected result, this is not possible"
                );
            }
            Exception exceptionHolder = null;
            bool exceptionHasBeenCaught = false;
            try
            {
                AwsEncryptionSdkConfig config = new AwsEncryptionSdkConfig
                {
                    CommitmentPolicy = ESDKCommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT,
                    NetV4_0_0_RetryPolicy = _netV400RetryPolicy
                };
                ESDK encryptionSdk = new ESDK(config);

                ICryptographicMaterialsManager cmm = MaterialProviderFactory.CreateDecryptCmm(vector, keyMap, vectorId);

                DecryptInput decryptInput = new DecryptInput
                {
                    Ciphertext = ciphertextStream,
                    MaterialsManager = cmm,
                };
                if (vector.CMM is "RequiredEncryptionContext")
                {
                    decryptInput = new DecryptInput
                    {
                        Ciphertext = ciphertextStream,
                        MaterialsManager = cmm,
                        EncryptionContext = vector.EncryptionContext
                    };
                }
                AWS.Cryptography.EncryptionSDK.DecryptOutput decryptOutput = encryptionSdk.Decrypt(decryptInput);
                if (expectedError != null)
                {
                    throw new TestVectorShouldHaveFailedException(
                        $"Test vector {vectorId} succeeded when it shouldn't have"
                    );
                }

                byte[] result = decryptOutput.Plaintext.ToArray();

                Assert.Equal(expectedPlaintext, result);
            }
            // Ensure Test Failure is not caught
            catch (TestVectorShouldHaveFailedException)
            {
                throw;
            }
            catch (Exception e) when (
                e is AWS.Cryptography.Primitives.CollectionOfErrors
                    or AWS.Cryptography.KeyStore.CollectionOfErrors
                    or AWS.Cryptography.MaterialProviders.CollectionOfErrors
                    or AWS.Cryptography.EncryptionSDK.CollectionOfErrors
            )
            {
                exceptionHasBeenCaught = true;
                exceptionHolder = e;
                // Use Reflection to get the common list field
                Type collectionType = e.GetType();
                FieldInfo listFieldInfo = collectionType.GetField("list");
                List<Exception> list = (List<Exception>)listFieldInfo?.GetValue(e);
                List<string> debugList = new List<string>();
                if (vector.MasterKeys != null) debugList.AddRange(vector.MasterKeys.Select(keyInfo => $"Key: {keyInfo.Key}, Type: {keyInfo.Type}"));

                testLogging.WriteLine($"CollectionOfErrors Logging. List:\n{string.Join("\n\t", list!)}");
                testLogging.WriteLine($"CollectionOfErrors Logging. master-keys:\n{string.Join("\n\t", debugList)}");
            }
            catch (Exception e) when (
                e is AWS.Cryptography.Primitives.OpaqueError
                    or AWS.Cryptography.KeyStore.OpaqueError
                    or AWS.Cryptography.MaterialProviders.OpaqueError
                    or AWS.Cryptography.EncryptionSDK.OpaqueError
            )
            {
                exceptionHasBeenCaught = true;
                // Use Reflection to get the common Obj field
                Type opaqueType = e.GetType();
                FieldInfo objFieldInfo = opaqueType.GetField("obj");
                object obj = objFieldInfo?.GetValue(e);
                switch (obj)
                {
                    case null when e.Message.Equals(OPAQUE_ERROR_NULL_OBJ_MSG):
                        testLogging.WriteLine($"OpaqueError Logging: Obj was null. Error Type is {opaqueType}");
                        exceptionHolder = e;
                        break;
                    case Exception nestedException:
                        testLogging.WriteLine($"OpaqueError Logging: Obj is an Exception. " +
                                              $"Error Type is {opaqueType}.\n" +
                                              $"Nested Exception is {nestedException.GetType()}.\n" +
                                              $"Nested Exceptions message is: \n\t{nestedException.Message}\n"
                                              // + $"Nested Exceptions StackTrace is: \n\t{nestedException.StackTrace}"
                                              );
                        exceptionHolder = nestedException;
                        break;
                    default:
                        testLogging.WriteLine($"OpaqueError Logging: Obj is an arbitrary object. " +
                                              $"Error Type is {opaqueType}. " +
                                              $"Type of Obj is {obj!.GetType()}.");
                        exceptionHolder = e;
                        break;
                }
            }
            catch (Exception e)
            {
                exceptionHasBeenCaught = true;
                exceptionHolder = e;
                testLogging.WriteLine($"Unexpected Exception: {e}");
                testLogging.WriteLine($"Unexpected Exception: Error Type is {e.GetType()}. " +
                                      $"Exception's message is: {e.Message}");
            }
            finally
            {
                if (expectedPlaintext == null && exceptionHasBeenCaught)
                {
                    testLogging.WriteLine("Decrypt Failed, possibly correctly?");
                }
                if (expectedPlaintext != null && exceptionHasBeenCaught)
                {
                    testLogging.WriteLine("Decrypt Failed, and should not have!");
                }
            }
            if (exceptionHolder != null && expectedPlaintext != null)
            {
                // Should succeed but did not, throw exception
                throw exceptionHolder;
            }
        }

        private class TestVectorShouldHaveFailedException : Exception
        {
            public TestVectorShouldHaveFailedException(string message) : base(message) { }
        }
    }
}
