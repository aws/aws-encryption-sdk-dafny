// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System.Linq;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    internal static class TypeConversion
    {
        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(value);
        }

        public static AWS.EncryptionSDK.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                AWS.EncryptionSDK.Core.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                        (AWS.EncryptionSDK.Core.AlgorithmSuiteId)value));
        }

        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return new System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring> value)
        {
            return Dafny.Sequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member).ToArray());
        }

        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(
                AWS.EncryptionSDK.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static AWS.EncryptionSDK.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                AWS.EncryptionSDK.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (AWS.EncryptionSDK.Core.IClientSupplier)value));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M5_value(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M5_value(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            if (value is Com.Amazonaws.Kms.KeyManagementServiceShim shim)
            {
                return shim._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            if (value is Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl)
            {
                return new Com.Amazonaws.Kms.KeyManagementServiceShim(impl);
            }

            throw new System.ArgumentException(
                "Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.DecryptMaterialsOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput(
                Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput)value;
            AWS.EncryptionSDK.Core.DecryptMaterialsOutput converted =
                new AWS.EncryptionSDK.Core.DecryptMaterialsOutput();
            converted.DecryptionMaterials =
                (AWS.EncryptionSDK.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    concrete.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput(
                AWS.EncryptionSDK.Core.DecryptMaterialsOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    value.DecryptionMaterials));
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (AWS.EncryptionSDK.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (AWS.EncryptionSDK.Core.IClientSupplier)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            AWS.EncryptionSDK.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (AWS.EncryptionSDK.Core.DiscoveryFilter)null;
            AWS.EncryptionSDK.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (AWS.EncryptionSDK.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    value.Regions),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static AWS.EncryptionSDK.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                AWS.EncryptionSDK.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return new System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>(
                value.Elements.Select(
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey> value)
        {
            return Dafny.Sequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member).ToArray());
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M10_ciphertext(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M10_ciphertext(
                System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static AWS.EncryptionSDK.Core.PaddingScheme
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Dafny.Aws.EncryptionSdk.Core._IPaddingScheme value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IPaddingScheme
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                AWS.EncryptionSDK.Core.PaddingScheme value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(value);
        }

        public static AWS.EncryptionSDK.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptionMaterials concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptionMaterials)value;
            AWS.EncryptionSDK.Core.DecryptionMaterials converted = new AWS.EncryptionSDK.Core.DecryptionMaterials();
            converted.AlgorithmSuiteId =
                (AWS.EncryptionSDK.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                    concrete.encryptionContext);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.verificationKey.is_Some)
                converted.VerificationKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                        concrete.verificationKey);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(
                AWS.EncryptionSDK.Core.DecryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_verificationKey =
                value.IsSetVerificationKey() ? value.VerificationKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.EncryptionSdk.Core.DecryptionMaterials(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                    var_plaintextDataKey),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                    var_verificationKey));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(Dafny.ISequence<byte> value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return utf8.GetString(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(string value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (AWS.EncryptionSDK.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (AWS.EncryptionSDK.Core.IClientSupplier)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            AWS.EncryptionSDK.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (AWS.EncryptionSDK.Core.DiscoveryFilter)null;
            AWS.EncryptionSDK.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (AWS.EncryptionSDK.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                    value.Regions),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M10_signingKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M10_signingKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(value);
        }

        public static AWS.EncryptionSDK.Core.OnEncryptInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(
                Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnEncryptInput concrete = (Dafny.Aws.EncryptionSdk.Core.OnEncryptInput)value;
            AWS.EncryptionSDK.Core.OnEncryptInput converted = new AWS.EncryptionSDK.Core.OnEncryptInput();
            converted.Materials =
                (AWS.EncryptionSDK.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(AWS.EncryptionSDK.Core.OnEncryptInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnEncryptInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(value.Materials));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static AWS.EncryptionSDK.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                Dafny.Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            if (value is NativeWrapper_ClientSupplier nativeWrapper) return nativeWrapper._impl;
            return new ClientSupplier(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IClientSupplier
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                AWS.EncryptionSDK.Core.IClientSupplier value)
        {
            switch (value)
            {
                case ClientSupplier valueWithImpl:
                    return valueWithImpl._impl;
                case ClientSupplierBase nativeImpl:
                    return new NativeWrapper_ClientSupplier(nativeImpl);
                default:
                    throw new System.ArgumentException(
                        "Custom implementations of ClientSupplier must extend ClientSupplierBase.");
            }
        }

        public static AWS.EncryptionSDK.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            Dafny.Aws.EncryptionSdk.Core.EncryptionMaterials concrete =
                (Dafny.Aws.EncryptionSdk.Core.EncryptionMaterials)value;
            AWS.EncryptionSDK.Core.EncryptionMaterials converted = new AWS.EncryptionSDK.Core.EncryptionMaterials();
            converted.AlgorithmSuiteId =
                (AWS.EncryptionSDK.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.signingKey.is_Some)
                converted.SigningKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M10_signingKey(
                        concrete.signingKey);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(
                AWS.EncryptionSDK.Core.EncryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_signingKey =
                value.IsSetSigningKey() ? value.SigningKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.EncryptionSdk.Core.EncryptionMaterials(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                    value.EncryptedDataKeys),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                    var_plaintextDataKey),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M10_signingKey(var_signingKey));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M10_accountIds(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M10_accountIds(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList(value);
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
                    concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(value.KmsKeyId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput(
                Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput)value;
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput converted =
                new AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput();
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.CommitmentPolicy =
                (AWS.EncryptionSDK.Core.CommitmentPolicy)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (AWS.EncryptionSDK.Core.AlgorithmSuiteId)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                        concrete.algorithmSuiteId);
            if (concrete.maxPlaintextLength.is_Some)
                converted.MaxPlaintextLength =
                    (long)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                        concrete.maxPlaintextLength);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput(
                AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput value)
        {
            AWS.EncryptionSDK.Core.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (AWS.EncryptionSDK.Core.AlgorithmSuiteId)null;
            long? var_maxPlaintextLength = value.IsSetMaxPlaintextLength() ? value.MaxPlaintextLength : (long?)null;
            return new Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    value.CommitmentPolicy),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                    var_algorithmSuiteId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                    var_maxPlaintextLength));
        }

        public static AWS.EncryptionSDK.Core.IAwsCryptographicMaterialProviders
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders value)
        {
            return new AwsCryptographicMaterialProviders(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                AWS.EncryptionSDK.Core.IAwsCryptographicMaterialProviders value)
        {
            if (value is AwsCryptographicMaterialProviders valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of AWS.EncryptionSDK.Core.IAwsCryptographicMaterialProviders are not supported");
        }

        public static AWS.EncryptionSDK.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                AWS.EncryptionSDK.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (AWS.EncryptionSDK.Core.DiscoveryFilter)value));
        }

        public static AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersException
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException value)
        {
            return new AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersException(
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                    value.message));
        }

        public static Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersException value)
        {
            Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException converted =
                new Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException();
            converted.message =
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                    value.Message);
            return converted;
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M9_partition(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M9_partition(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static AWS.EncryptionSDK.Core.EncryptedDataKey
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member(
                Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member(
                AWS.EncryptionSDK.Core.EncryptedDataKey value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(value);
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList__M6_member).ToArray());
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static AWS.EncryptionSDK.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                AWS.EncryptionSDK.Core.ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static AWS.EncryptionSDK.Core.AesWrappingAlg
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                AWS.EncryptionSDK.Core.AesWrappingAlg value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(value);
        }

        public static AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput(
                Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput concrete =
                (Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput)value;
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput converted =
                new AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput();
            converted.EncryptionMaterials =
                (AWS.EncryptionSDK.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    concrete.encryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput(
                AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    value.EncryptionMaterials));
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                AWS.EncryptionSDK.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (AWS.EncryptionSDK.Core.IClientSupplier)value));
        }

        public static AWS.EncryptionSDK.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                AWS.EncryptionSDK.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static AWS.EncryptionSDK.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                AWS.EncryptionSDK.Core.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static AWS.EncryptionSDK.Core.CreateRawAesKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateRawAesKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateRawAesKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateRawAesKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateRawAesKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateRawAesKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(
                    concrete.keyName);
            converted.WrappingKey =
                (System.IO.MemoryStream)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    concrete.wrappingKey);
            converted.WrappingAlg =
                (AWS.EncryptionSDK.Core.AesWrappingAlg)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    concrete.wrappingAlg);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateRawAesKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput(
                AWS.EncryptionSDK.Core.CreateRawAesKeyringInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.CreateRawAesKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    value.KeyNamespace),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    value.WrappingKey),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    value.WrappingAlg));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static AWS.EncryptionSDK.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                AWS.EncryptionSDK.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static AWS.EncryptionSDK.Core.AesWrappingAlg
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(
                Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg value)
        {
            if (value.is_ALG__AES128__GCM__IV12__TAG16)
                return AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
            if (value.is_ALG__AES192__GCM__IV12__TAG16)
                return AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
            if (value.is_ALG__AES256__GCM__IV12__TAG16)
                return AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.AesWrappingAlg value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(AWS.EncryptionSDK.Core.AesWrappingAlg value)
        {
            if (AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
            if (AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
            if (AWS.EncryptionSDK.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.AesWrappingAlg value");
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static AWS.EncryptionSDK.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                AWS.EncryptionSDK.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M3_key(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M3_key(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList(System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList__M6_member).ToArray());
        }

        public static AWS.EncryptionSDK.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                    value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                AWS.EncryptionSDK.Core.ICryptographicMaterialsManager value)
        {
            return
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                    value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (AWS.EncryptionSDK.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            converted.Region =
                (string)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                    concrete.region);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            AWS.EncryptionSDK.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (AWS.EncryptionSDK.Core.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                    value.KmsClient),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                    var_grantTokens),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                    value.Region));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(value);
        }

        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static AWS.EncryptionSDK.Core.OnEncryptOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(
                Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput concrete = (Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput)value;
            AWS.EncryptionSDK.Core.OnEncryptOutput converted = new AWS.EncryptionSDK.Core.OnEncryptOutput();
            converted.Materials =
                (AWS.EncryptionSDK.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(
                AWS.EncryptionSDK.Core.OnEncryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(value.Materials));
        }

        public static AWS.EncryptionSDK.Core.DecryptMaterialsInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput(
                Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsInput)value;
            AWS.EncryptionSDK.Core.DecryptMaterialsInput converted = new AWS.EncryptionSDK.Core.DecryptMaterialsInput();
            converted.AlgorithmSuiteId =
                (AWS.EncryptionSDK.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.CommitmentPolicy =
                (AWS.EncryptionSDK.Core.CommitmentPolicy)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput(
                AWS.EncryptionSDK.Core.DecryptMaterialsInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                    value.CommitmentPolicy),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                    value.EncryptedDataKeys),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                        concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (AWS.EncryptionSDK.Core.IClientSupplier)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsMrkMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            AWS.EncryptionSDK.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (AWS.EncryptionSDK.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                    var_generator),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                    var_kmsKeyIds),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static AWS.EncryptionSDK.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                AWS.EncryptionSDK.Core.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList__M6_member(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static AWS.EncryptionSDK.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                AWS.EncryptionSDK.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (AWS.EncryptionSDK.Core.DiscoveryFilter)value));
        }

        public static AWS.EncryptionSDK.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                AWS.EncryptionSDK.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M13_keyProviderId(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M13_keyProviderId(string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_Utf8Bytes(value);
        }

        public static AWS.EncryptionSDK.Core.PaddingScheme
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(
                Dafny.Aws.EncryptionSdk.Core._IPaddingScheme value)
        {
            if (value.is_PKCS1) return AWS.EncryptionSDK.Core.PaddingScheme.PKCS1;
            if (value.is_OAEP__SHA1__MGF1) return AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA1_MGF1;
            if (value.is_OAEP__SHA256__MGF1) return AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA256_MGF1;
            if (value.is_OAEP__SHA384__MGF1) return AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA384_MGF1;
            if (value.is_OAEP__SHA512__MGF1) return AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA512_MGF1;
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.PaddingScheme value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IPaddingScheme
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(AWS.EncryptionSDK.Core.PaddingScheme value)
        {
            if (AWS.EncryptionSDK.Core.PaddingScheme.PKCS1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_PKCS1();
            if (AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA1_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA1__MGF1();
            if (AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA256_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA256__MGF1();
            if (AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA384_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA384__MGF1();
            if (AWS.EncryptionSDK.Core.PaddingScheme.OAEP_SHA512_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA512__MGF1();
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.PaddingScheme value");
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(AWS.EncryptionSDK.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateDefaultClientSupplierInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateDefaultClientSupplierInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput)value;
            AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput converted =
                new AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput();
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateDefaultClientSupplierInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateDefaultClientSupplierInput(
                AWS.EncryptionSDK.Core.CreateDefaultClientSupplierInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput();
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList__M6_member).ToArray());
        }

        public static AWS.EncryptionSDK.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(
                AWS.EncryptionSDK.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId((string)value));
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                AWS.EncryptionSDK.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static AWS.EncryptionSDK.Core.OnDecryptOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(
                Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput concrete = (Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput)value;
            AWS.EncryptionSDK.Core.OnDecryptOutput converted = new AWS.EncryptionSDK.Core.OnDecryptOutput();
            converted.Materials =
                (AWS.EncryptionSDK.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(
                AWS.EncryptionSDK.Core.OnDecryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(value.Materials));
        }

        public static AWS.EncryptionSDK.Core.CreateMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateMultiKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateMultiKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (AWS.EncryptionSDK.Core.IKeyring)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                        concrete.generator);
            converted.ChildKeyrings =
                (System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                    concrete.childKeyrings);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput(
                AWS.EncryptionSDK.Core.CreateMultiKeyringInput value)
        {
            AWS.EncryptionSDK.Core.IKeyring var_generator =
                value.IsSetGenerator() ? value.Generator : (AWS.EncryptionSDK.Core.IKeyring)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateMultiKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                    value.ChildKeyrings));
        }

        public static long?
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateRawRsaKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(
                    concrete.keyName);
            converted.PaddingScheme =
                (AWS.EncryptionSDK.Core.PaddingScheme)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                    concrete.paddingScheme);
            if (concrete.publicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                        concrete.publicKey);
            if (concrete.privateKey.is_Some)
                converted.PrivateKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                        concrete.privateKey);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateRawRsaKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput(
                AWS.EncryptionSDK.Core.CreateRawRsaKeyringInput value)
        {
            System.IO.MemoryStream var_publicKey =
                value.IsSetPublicKey() ? value.PublicKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_privateKey =
                value.IsSetPrivateKey() ? value.PrivateKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    value.KeyNamespace),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                    value.PaddingScheme),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(var_publicKey),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                    var_privateKey));
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                        concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (AWS.EncryptionSDK.Core.IClientSupplier)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            AWS.EncryptionSDK.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (AWS.EncryptionSDK.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
                    var_generator),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                    var_kmsKeyIds),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static AWS.EncryptionSDK.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                AWS.EncryptionSDK.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (AWS.EncryptionSDK.Core.DiscoveryFilter)value));
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.IKeyring)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                AWS.EncryptionSDK.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                        (AWS.EncryptionSDK.Core.IKeyring)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(
                AWS.EncryptionSDK.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static AWS.EncryptionSDK.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                AWS.EncryptionSDK.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (AWS.EncryptionSDK.Core.IClientSupplier)value));
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S6_Region(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_AccountId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_AccountId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static AWS.EncryptionSDK.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384)
                return AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.AlgorithmSuiteId value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                AWS.EncryptionSDK.Core.AlgorithmSuiteId value)
        {
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY();
            if (AWS.EncryptionSDK.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384();
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.AlgorithmSuiteId value");
        }

        public static AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateDefaultCryptographicMaterialsManagerInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput)value;
            AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput converted =
                new AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput();
            converted.Keyring =
                (AWS.EncryptionSDK.Core.IKeyring)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateDefaultCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                AWS.EncryptionSDK.Core.CreateDefaultCryptographicMaterialsManagerInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    value.Keyring));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return value.ItemEnumerable.ToDictionary(
                pair => FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M3_key(pair.Car),
                pair => FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M5_value(pair.Cdr));
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromCollection(value.Select(pair =>
                new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M3_key(pair.Key),
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext__M5_value(pair.Value))
            ));
        }

        public static AWS.EncryptionSDK.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                AWS.EncryptionSDK.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (AWS.EncryptionSDK.Core.IClientSupplier)value));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S9_AccountId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_AccountIdList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S9_AccountId(value);
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(string value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value);
        }

        public static AWS.EncryptionSDK.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(
                AWS.EncryptionSDK.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static AWS.EncryptionSDK.Core.GetClientInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(
                Dafny.Aws.EncryptionSdk.Core._IGetClientInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetClientInput concrete = (Dafny.Aws.EncryptionSdk.Core.GetClientInput)value;
            AWS.EncryptionSDK.Core.GetClientInput converted = new AWS.EncryptionSDK.Core.GetClientInput();
            converted.Region =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(concrete.region);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IGetClientInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(AWS.EncryptionSDK.Core.GetClientInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.GetClientInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(value.Region));
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            if (value is NativeWrapper_Keyring nativeWrapper) return nativeWrapper._impl;
            return new Keyring(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(AWS.EncryptionSDK.Core.IKeyring value)
        {
            switch (value)
            {
                case Keyring valueWithImpl:
                    return valueWithImpl._impl;
                case KeyringBase nativeImpl:
                    return new NativeWrapper_Keyring(nativeImpl);
                default:
                    throw new System.ArgumentException(
                        "Custom implementations of Keyring must extend KeyringBase.");
            }
        }

        public static AWS.EncryptionSDK.Core.OnDecryptInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(
                Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnDecryptInput concrete = (Dafny.Aws.EncryptionSdk.Core.OnDecryptInput)value;
            AWS.EncryptionSDK.Core.OnDecryptInput converted = new AWS.EncryptionSDK.Core.OnDecryptInput();
            converted.Materials =
                (AWS.EncryptionSDK.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(concrete.materials);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(AWS.EncryptionSDK.Core.OnDecryptInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnDecryptInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(value.Materials),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                    value.EncryptedDataKeys));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.EncryptedDataKey
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(
                Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey value)
        {
            Dafny.Aws.EncryptionSdk.Core.EncryptedDataKey concrete =
                (Dafny.Aws.EncryptionSdk.Core.EncryptedDataKey)value;
            AWS.EncryptionSDK.Core.EncryptedDataKey converted = new AWS.EncryptionSDK.Core.EncryptedDataKey();
            converted.KeyProviderId =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M13_keyProviderId(
                    concrete.keyProviderId);
            converted.KeyProviderInfo =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
                    concrete.keyProviderInfo);
            converted.Ciphertext =
                (System.IO.MemoryStream)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M10_ciphertext(concrete.ciphertext);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(
                AWS.EncryptionSDK.Core.EncryptedDataKey value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.EncryptedDataKey(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M13_keyProviderId(
                    value.KeyProviderId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
                    value.KeyProviderInfo),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey__M10_ciphertext(value.Ciphertext));
        }

        public static string
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S8_KmsKeyId((string)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static AWS.EncryptionSDK.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            if (value is NativeWrapper_CryptographicMaterialsManager nativeWrapper) return nativeWrapper._impl;
            return new CryptographicMaterialsManager(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                AWS.EncryptionSDK.Core.ICryptographicMaterialsManager value)
        {
            switch (value)
            {
                case CryptographicMaterialsManager valueWithImpl:
                    return valueWithImpl._impl;
                case CryptographicMaterialsManagerBase nativeImpl:
                    return new NativeWrapper_CryptographicMaterialsManager(nativeImpl);
                default:
                    throw new System.ArgumentException(
                        "Custom implementations of CryptographicMaterialsManager must extend CryptographicMaterialsManagerBase.");
            }
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
                    concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsMrkKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
                    value.KmsKeyId),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                    value.KmsClient),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static AWS.EncryptionSDK.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            if (value.is_FORBID__ENCRYPT__ALLOW__DECRYPT)
                return AWS.EncryptionSDK.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT)
                return AWS.EncryptionSDK.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT)
                return AWS.EncryptionSDK.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.CommitmentPolicy value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(
                AWS.EncryptionSDK.Core.CommitmentPolicy value)
        {
            if (AWS.EncryptionSDK.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT();
            if (AWS.EncryptionSDK.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
            if (AWS.EncryptionSDK.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
            throw new System.ArgumentException("Invalid AWS.EncryptionSDK.Core.CommitmentPolicy value");
        }

        public static System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                System.Collections.Generic.List<AWS.EncryptionSDK.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput)value;
            AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput converted =
                new AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (AWS.EncryptionSDK.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(
                AWS.EncryptionSDK.Core.CreateAwsKmsDiscoveryKeyringInput value)
        {
            AWS.EncryptionSDK.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (AWS.EncryptionSDK.Core.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                    value.KmsClient),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList(System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S12_KmsKeyIdList__M6_member).ToArray());
        }

        public static AWS.EncryptionSDK.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter value)
        {
            Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter concrete = (Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter)value;
            AWS.EncryptionSDK.Core.DiscoveryFilter converted = new AWS.EncryptionSDK.Core.DiscoveryFilter();
            converted.AccountIds =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M10_accountIds(concrete.accountIds);
            converted.Partition =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M9_partition(
                    concrete.partition);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                AWS.EncryptionSDK.Core.DiscoveryFilter value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M10_accountIds(value.AccountIds),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M9_partition(value.Partition));
        }

        public static AWS.EncryptionSDK.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(
                AWS.EncryptionSDK.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static AWS.EncryptionSDK.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member(
                AWS.EncryptionSDK.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S10_RegionList(value);
        }

        public static AWS.EncryptionSDK.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (AWS.EncryptionSDK.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                AWS.EncryptionSDK.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (AWS.EncryptionSDK.Core.DiscoveryFilter)value));
        }

        public static AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersBaseException
            FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException value)
        {
            switch (value)
            {
                case Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException dafnyVal:
                    return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                        dafnyVal);
                default:
                    return new AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersBaseException(
                        FromDafny_N6_smithy__N3_api__S6_String(value.GetMessage()));
            }
        }

        public static Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException ToDafny_CommonError(
            System.Exception value)
        {
            Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersBaseException rtn;
            switch (value)
            {
                case AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersException exception:
                    return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                        exception);
                case AWS.EncryptionSDK.Core.AwsCryptographicMaterialProvidersBaseException exception:
                    rtn = new Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersBaseException();
                    rtn.message = ToDafny_N6_smithy__N3_api__S6_String(exception.Message);
                    return rtn;
                default:
                    var message =
                        $"AwsCryptographicMaterialProviders encountered unexpected: {value.GetType()}: \"{value.Message}\"";
                    rtn = new Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersBaseException();
                    rtn.message = ToDafny_N6_smithy__N3_api__S6_String(message);
                    return rtn;
            }
        }
    }
}
