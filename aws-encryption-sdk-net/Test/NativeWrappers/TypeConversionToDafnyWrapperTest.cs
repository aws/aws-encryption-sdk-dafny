// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using AWS.EncryptionSDK.Core;
using Xunit;
using Xunit.Sdk;

namespace AWSEncryptionSDKTests.NativeWrappers
{
    public class TypeConversionToDafnyWrapperTest
    {
        [Fact]
        public void TestInterfaceThrowsException()
        {
            const string expectedMessage =
                "Custom implementations of Keyring must extend KeyringBase.";
            var expected = new ArgumentException(expectedMessage);
            Dafny.Aws.EncryptionSdk.Core.IKeyring output = null;
            try
            {
                output = TypeConversion
                    .ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                        new KeyringInterface());
            }
            catch (ArgumentException e)
            {
                Assert.Equal(expectedMessage, e.Message);
                return;
            }
            catch (Exception e)
            {
                throw new XunitException(
                    nameof(TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference) +
                    $" threw an exception: {e.GetType()} with message: \"{e.Message}\"." +
                    $"Should have thrown: \"{expected}\""
                );
            }
            throw new XunitException(
                nameof(TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference) +
                $" returned {output}. Should have thrown: \"{expected}\"");
        }
    }

    class KeyringInterface : IKeyring
    {
        public OnEncryptOutput OnEncrypt(OnEncryptInput input)
        { throw new System.NotImplementedException(); }
        public OnDecryptOutput OnDecrypt(OnDecryptInput input)
        { throw new System.NotImplementedException(); }
    }
}
