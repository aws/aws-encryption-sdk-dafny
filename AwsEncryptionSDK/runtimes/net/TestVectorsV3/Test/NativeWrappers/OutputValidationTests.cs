// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;
// ReSharper disable once RedundantUsingDirective
using Wrappers_Compile;
using Xunit;
using Xunit.Sdk;
using static AWSEncryptionSDKTests.NativeWrappers.Utils;

namespace AWSEncryptionSDKTests.NativeWrappers
{
    public class OutputValidationTests
    {
        private const string EXPECTED_FAILURE =
            "Wrappers_Compile.Result.Failure(Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException)";

        [Fact]
        public void TestInvalidRejected()
        {
            var underTest = new NativeWrapper_Keyring(new BadKeyring());
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
                // ReSharper disable once RedundantAssignment
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> output = null;
            try
            {
                output = underTest.OnEncrypt(GetDafnyOnEncryptInput());
            }
            catch (Exception e)
            {
                throw new XunitException(
                    $"{underTest}.OnEncrypt threw an exception: {e.GetType()} with message: \"{e.Message}\"." +
                    $"Should have returned: \"{EXPECTED_FAILURE}\""
                );
            }

            if (output != null)
            {
                // Weird way of checking that the class is right, I know, but this is what I can figure out
                Assert.Equal(EXPECTED_FAILURE, $"{output}");
                var e = output.dtor_error;
                const string expectedMessage =
                    "Output of AWSEncryptionSDKTests.NativeWrappers.BadKeyring._OnEncrypt is invalid." +
                    " Missing value for required property 'Materials'";
                var actualMessage = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(e.GetMessage());
                Assert.Equal(expectedMessage, actualMessage);
            }
            else
            {
                throw new XunitException($"{underTest}.OnEncrypt returned null." +
                                         $"Should have returned: \"{EXPECTED_FAILURE}\"");
            }
        }

        [Fact]
        public void TestNullRejected()
        {
            var underTest = new NativeWrapper_Keyring(new BadKeyring());
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
                // ReSharper disable once RedundantAssignment
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> output = null;
            try
            {
                output = underTest.OnDecrypt(GetDafnyOnDecryptInput());
            }
            catch (Exception e)
            {
                throw new XunitException(
                    $"{underTest}.OnDecrypt threw an exception: {e.GetType()} with message: \"{e.Message}\"." +
                    $"Should have returned: \"{EXPECTED_FAILURE}\""
                );
            }
            if (output != null)
            {
                Assert.Equal(EXPECTED_FAILURE, $"{output}");
                var e = output.dtor_error;
                const string expectedMessage = "AWSEncryptionSDKTests.NativeWrappers.BadKeyring._OnDecrypt returned null, should be AWS.EncryptionSDK.Core.OnDecryptOutput";
                var actualMessage = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(e.GetMessage());
                /*Console.Out.WriteLine($"actual is: \"{actualMessage}\"");*/
                Assert.Equal(expectedMessage, actualMessage);
            }
            else
            {
                throw new XunitException($"{underTest}.OnDecrypt returned null." +
                                         $"Should have returned: \"{EXPECTED_FAILURE}\"");
            }
        }
    }

    class BadKeyring : KeyringBase
    {
        protected override OnEncryptOutput _OnEncrypt(OnEncryptInput input)
        {
            return new OnEncryptOutput();
        }

        protected override OnDecryptOutput _OnDecrypt(OnDecryptInput input)
        {
            return null;
        }
    }

    internal static class Utils
    {
        internal static Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput GetDafnyOnEncryptInput()
        {
            return TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(GetOnEncryptInput());
        }

        internal static Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput GetDafnyOnDecryptInput()
        {
            return TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(GetOnDecryptInput());
        }

        static OnEncryptInput GetOnEncryptInput()
        {
            var materials = new EncryptionMaterials()
            {
                AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
                EncryptionContext = new Dictionary<string, string>() {{"test", "test"}},
                EncryptedDataKeys = new List<EncryptedDataKey>()
            };
            return new OnEncryptInput {Materials = materials};
        }

        static OnDecryptInput GetOnDecryptInput()
        {
            var materials = new DecryptionMaterials()
            {
                AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
                EncryptionContext = new Dictionary<string, string>() {{"test", "test"}}
            };
            return new OnDecryptInput()
            {
                EncryptedDataKeys = new List<EncryptedDataKey>(),
                Materials = materials
            };
        }
    }
}
