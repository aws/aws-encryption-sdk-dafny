// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;
using Xunit;

namespace AWSEncryptionSDKTests.NativeWrappers
{
    public class OutputValidationTests
    {
        [Fact]
        public void TestInvalidRejected()
        {
            var wrappedBadKeyring = new NativeWrapper_Keyring(new BadKeyring());
            var e = Assert.ThrowsAny<Exception>(() => wrappedBadKeyring.OnEncrypt(Utils.GetDafnyOnEncryptInput()));
            Console.Out.WriteLine($"BadKeyring throw {e.GetType()} On Encrypt with message: \"{e.Message}\"");
            // Currently getting
            // `BadKeyring throw System.ArgumentException On Encrypt with message: "Unknown exception type"`
            // But should be
            // `BadKeyring throw AwsCryptographicMaterialProviders on Encrypt with message: "Missing value for required property 'Materials'"`
        }

        [Fact]
        public void TestNullRejected()
        {
            var wrappedBadKeyring = new NativeWrapper_Keyring(new BadKeyring());
            var e = Assert.ThrowsAny<Exception>(() => wrappedBadKeyring.OnDecrypt(Utils.GetDafnyOnDecryptInput()));
            Console.Out.WriteLine($"BadKeyring throw {e.GetType()} On Decrypt with message: \"{e.Message}\"");
            // Currently getting
            // `BadKeyring throw System.ArgumentException On Decrypt with message: "Unknown exception type"`
            // But should be
            // `BadKeyring throw AwsCryptographicMaterialProviders on Decrypt with message:
            // "Output of AWSEncryptionSDKTests.NativeWrappers.BadKeyring._OnDecrypt is invalid. Should be AWS.EncryptionSDK.Core.OnDecryptOutput but is ."
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
