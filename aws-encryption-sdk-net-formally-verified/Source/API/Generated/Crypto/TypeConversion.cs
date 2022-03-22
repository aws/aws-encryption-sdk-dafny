// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.EncryptionSdk.Core;

namespace Aws.EncryptionSdk.Core
{
    internal static class TypeConversion
    {
        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(value);
        }

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                        (Aws.EncryptionSdk.Core.AlgorithmSuiteId)value));
        }

        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return new System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring>(
                value.Elements.Select(FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return Dafny.Sequence<Dafny.Aws.EncryptionSdk.Core.IKeyring>.FromArray(value
                .Select(ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member).ToArray());
        }

        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(
                Aws.EncryptionSdk.Core.IKeyring value)
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

        public static Aws.EncryptionSdk.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (Aws.EncryptionSdk.Core.IClientSupplier)value));
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

        public static Aws.EncryptionSdk.Core.DecryptMaterialsOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput(
                Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput)value;
            Aws.EncryptionSdk.Core.DecryptMaterialsOutput converted =
                new Aws.EncryptionSdk.Core.DecryptMaterialsOutput();
            converted.DecryptionMaterials =
                (Aws.EncryptionSdk.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    concrete.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput(
                Aws.EncryptionSdk.Core.DecryptMaterialsOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    value.DecryptionMaterials));
        }

        public static Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.EncryptionSdk.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.EncryptionSdk.Core.IClientSupplier)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Aws.EncryptionSdk.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.EncryptionSdk.Core.DiscoveryFilter)null;
            Aws.EncryptionSdk.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.EncryptionSdk.Core.IClientSupplier)null;
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

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
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

        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return new System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>(
                value.Elements.Select(
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> value)
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

        public static Aws.EncryptionSdk.Core.PaddingScheme
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Dafny.Aws.EncryptionSdk.Core._IPaddingScheme value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IPaddingScheme
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Aws.EncryptionSdk.Core.PaddingScheme value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(value);
        }

        public static Aws.EncryptionSdk.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptionMaterials concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptionMaterials)value;
            Aws.EncryptionSdk.Core.DecryptionMaterials converted = new Aws.EncryptionSdk.Core.DecryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
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
                Aws.EncryptionSdk.Core.DecryptionMaterials value)
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

        public static Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.EncryptionSdk.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.EncryptionSdk.Core.IClientSupplier)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Aws.EncryptionSdk.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.EncryptionSdk.Core.DiscoveryFilter)null;
            Aws.EncryptionSdk.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.EncryptionSdk.Core.IClientSupplier)null;
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

        public static Aws.EncryptionSdk.Core.OnEncryptInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(
                Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnEncryptInput concrete = (Dafny.Aws.EncryptionSdk.Core.OnEncryptInput)value;
            Aws.EncryptionSdk.Core.OnEncryptInput converted = new Aws.EncryptionSdk.Core.OnEncryptInput();
            converted.Materials =
                (Aws.EncryptionSdk.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(Aws.EncryptionSdk.Core.OnEncryptInput value)
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

        public static Aws.EncryptionSdk.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                Dafny.Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            return new ClientSupplier(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IClientSupplier
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            if (value is ClientSupplier valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.EncryptionSdk.Core.IClientSupplier are not supported yet");
        }

        public static Aws.EncryptionSdk.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            Dafny.Aws.EncryptionSdk.Core.EncryptionMaterials concrete =
                (Dafny.Aws.EncryptionSdk.Core.EncryptionMaterials)value;
            Aws.EncryptionSdk.Core.EncryptionMaterials converted = new Aws.EncryptionSdk.Core.EncryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>)
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
                Aws.EncryptionSdk.Core.EncryptionMaterials value)
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

        public static Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput(
                Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput)value;
            Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput converted =
                new Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput();
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.CommitmentPolicy =
                (Aws.EncryptionSdk.Core.CommitmentPolicy)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
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
                Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput value)
        {
            Aws.EncryptionSdk.Core.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (Aws.EncryptionSdk.Core.AlgorithmSuiteId)null;
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

        public static Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput();
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
                Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput value)
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

        public static Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders value)
        {
            return new AwsCryptographicMaterialProviders(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders value)
        {
            if (value is AwsCryptographicMaterialProviders valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders are not supported yet");
        }

        public static Aws.EncryptionSdk.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.EncryptionSdk.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (Aws.EncryptionSdk.Core.DiscoveryFilter)value));
        }

        public static Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException value)
        {
            return new Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException(
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                    value.message));
        }

        public static Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException value)
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

        public static Aws.EncryptionSdk.Core.EncryptedDataKey
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member(
                Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList__M6_member(
                Aws.EncryptionSdk.Core.EncryptedDataKey value)
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

        public static Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
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

        public static Aws.EncryptionSdk.Core.AesWrappingAlg
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Aws.EncryptionSdk.Core.AesWrappingAlg value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(value);
        }

        public static Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput(
                Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput concrete =
                (Dafny.Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput)value;
            Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput converted =
                new Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput();
            converted.EncryptionMaterials =
                (Aws.EncryptionSdk.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    concrete.encryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput(
                Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput value)
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

        public static Aws.EncryptionSdk.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (Aws.EncryptionSdk.Core.IClientSupplier)value));
        }

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Aws.EncryptionSdk.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Aws.EncryptionSdk.Core.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static Aws.EncryptionSdk.Core.CreateRawAesKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateRawAesKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateRawAesKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateRawAesKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateRawAesKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateRawAesKeyringInput();
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
                (Aws.EncryptionSdk.Core.AesWrappingAlg)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    concrete.wrappingAlg);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateRawAesKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput(
                Aws.EncryptionSdk.Core.CreateRawAesKeyringInput value)
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

        public static Aws.EncryptionSdk.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Aws.EncryptionSdk.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Aws.EncryptionSdk.Core.AesWrappingAlg
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(
                Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg value)
        {
            if (value.is_ALG__AES128__GCM__IV12__TAG16)
                return Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
            if (value.is_ALG__AES192__GCM__IV12__TAG16)
                return Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
            if (value.is_ALG__AES256__GCM__IV12__TAG16)
                return Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.AesWrappingAlg value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAesWrappingAlg
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_AesWrappingAlg(Aws.EncryptionSdk.Core.AesWrappingAlg value)
        {
            if (Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
            if (Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
            if (Aws.EncryptionSdk.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.AesWrappingAlg value");
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

        public static Aws.EncryptionSdk.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Aws.EncryptionSdk.Core.DecryptionMaterials value)
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

        public static Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                    value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
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

        public static Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.EncryptionSdk.Core.DiscoveryFilter)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Aws.EncryptionSdk.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.EncryptionSdk.Core.DiscoveryFilter)null;
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

        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Aws.EncryptionSdk.Core.DecryptMaterialsInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput(
                Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.DecryptMaterialsInput)value;
            Aws.EncryptionSdk.Core.DecryptMaterialsInput converted = new Aws.EncryptionSdk.Core.DecryptMaterialsInput();
            converted.AlgorithmSuiteId =
                (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.CommitmentPolicy =
                (Aws.EncryptionSdk.Core.CommitmentPolicy)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>)
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
                Aws.EncryptionSdk.Core.DecryptMaterialsInput value)
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

        public static Aws.EncryptionSdk.Core.OnEncryptOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(
                Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput concrete = (Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput)value;
            Aws.EncryptionSdk.Core.OnEncryptOutput converted = new Aws.EncryptionSdk.Core.OnEncryptOutput();
            converted.Materials =
                (Aws.EncryptionSdk.Core.EncryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(
                Aws.EncryptionSdk.Core.OnEncryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnEncryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(value.Materials));
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

        public static Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput();
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
                    (Aws.EncryptionSdk.Core.IClientSupplier)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.EncryptionSdk.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.EncryptionSdk.Core.IClientSupplier)null;
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

        public static Aws.EncryptionSdk.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Aws.EncryptionSdk.Core.CommitmentPolicy value)
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

        public static Aws.EncryptionSdk.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.EncryptionSdk.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (Aws.EncryptionSdk.Core.DiscoveryFilter)value));
        }

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
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

        public static Aws.EncryptionSdk.Core.PaddingScheme
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(
                Dafny.Aws.EncryptionSdk.Core._IPaddingScheme value)
        {
            if (value.is_PKCS1) return Aws.EncryptionSdk.Core.PaddingScheme.PKCS1;
            if (value.is_OAEP__SHA1__MGF1) return Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA1_MGF1;
            if (value.is_OAEP__SHA256__MGF1) return Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA256_MGF1;
            if (value.is_OAEP__SHA384__MGF1) return Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA384_MGF1;
            if (value.is_OAEP__SHA512__MGF1) return Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA512_MGF1;
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.PaddingScheme value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IPaddingScheme
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S13_PaddingScheme(Aws.EncryptionSdk.Core.PaddingScheme value)
        {
            if (Aws.EncryptionSdk.Core.PaddingScheme.PKCS1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_PKCS1();
            if (Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA1_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA1__MGF1();
            if (Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA256_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA256__MGF1();
            if (Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA384_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA384__MGF1();
            if (Aws.EncryptionSdk.Core.PaddingScheme.OAEP_SHA512_MGF1.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.PaddingScheme.create_OAEP__SHA512__MGF1();
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.PaddingScheme value");
        }

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(Aws.EncryptionSdk.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateDefaultClientSupplierInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateDefaultClientSupplierInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput)value;
            Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput converted =
                new Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput();
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateDefaultClientSupplierInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateDefaultClientSupplierInput(
                Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput value)
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

        public static Aws.EncryptionSdk.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(
                Aws.EncryptionSdk.Core.DecryptionMaterials value)
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

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Aws.EncryptionSdk.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Aws.EncryptionSdk.Core.OnDecryptOutput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(
                Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput concrete = (Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput)value;
            Aws.EncryptionSdk.Core.OnDecryptOutput converted = new Aws.EncryptionSdk.Core.OnDecryptOutput();
            converted.Materials =
                (Aws.EncryptionSdk.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(
                Aws.EncryptionSdk.Core.OnDecryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.OnDecryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(value.Materials));
        }

        public static Aws.EncryptionSdk.Core.CreateMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateMultiKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateMultiKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (Aws.EncryptionSdk.Core.IKeyring)
                    FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                        concrete.generator);
            converted.ChildKeyrings =
                (System.Collections.Generic.List<Aws.EncryptionSdk.Core.IKeyring>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                    concrete.childKeyrings);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateMultiKeyringInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput(
                Aws.EncryptionSdk.Core.CreateMultiKeyringInput value)
        {
            Aws.EncryptionSdk.Core.IKeyring var_generator =
                value.IsSetGenerator() ? value.Generator : (Aws.EncryptionSdk.Core.IKeyring)null;
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

        public static Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateRawRsaKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(
                    concrete.keyName);
            converted.PaddingScheme =
                (Aws.EncryptionSdk.Core.PaddingScheme)
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
                Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput value)
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

        public static Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMultiKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput();
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
                    (Aws.EncryptionSdk.Core.IClientSupplier)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.EncryptionSdk.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.EncryptionSdk.Core.IClientSupplier)null;
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

        public static Aws.EncryptionSdk.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.EncryptionSdk.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (Aws.EncryptionSdk.Core.DiscoveryFilter)value));
        }

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IKeyring)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                Aws.EncryptionSdk.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                        (Aws.EncryptionSdk.Core.IKeyring)value));
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

        public static Aws.EncryptionSdk.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput__M9_materials(
                Aws.EncryptionSdk.Core.EncryptionMaterials value)
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

        public static Aws.EncryptionSdk.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (Aws.EncryptionSdk.Core.IClientSupplier)value));
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

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384)
                return Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.AlgorithmSuiteId value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY();
            if (Aws.EncryptionSdk.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384();
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.AlgorithmSuiteId value");
        }

        public static Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateDefaultCryptographicMaterialsManagerInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput)value;
            Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput converted =
                new Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput();
            converted.Keyring =
                (Aws.EncryptionSdk.Core.IKeyring)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICreateDefaultCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput value)
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

        public static Aws.EncryptionSdk.Core.IClientSupplier
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IClientSupplier)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Aws.EncryptionSdk.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                        (Aws.EncryptionSdk.Core.IClientSupplier)value));
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

        public static Aws.EncryptionSdk.Core.DecryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IDecryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput__M9_materials(
                Aws.EncryptionSdk.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_DecryptionMaterials(value);
        }

        public static Aws.EncryptionSdk.Core.GetClientInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(
                Dafny.Aws.EncryptionSdk.Core._IGetClientInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.GetClientInput concrete = (Dafny.Aws.EncryptionSdk.Core.GetClientInput)value;
            Aws.EncryptionSdk.Core.GetClientInput converted = new Aws.EncryptionSdk.Core.GetClientInput();
            converted.Region =
                (string)FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(concrete.region);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IGetClientInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(Aws.EncryptionSdk.Core.GetClientInput value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.GetClientInput(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput__M6_region(value.Region));
        }

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return new Keyring(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(Aws.EncryptionSdk.Core.IKeyring value)
        {
            if (value is Keyring valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.EncryptionSdk.Core.IKeyring are not supported yet");
        }

        public static Aws.EncryptionSdk.Core.OnDecryptInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(
                Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.OnDecryptInput concrete = (Dafny.Aws.EncryptionSdk.Core.OnDecryptInput)value;
            Aws.EncryptionSdk.Core.OnDecryptInput converted = new Aws.EncryptionSdk.Core.OnDecryptInput();
            converted.Materials =
                (Aws.EncryptionSdk.Core.DecryptionMaterials)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M9_materials(concrete.materials);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(Aws.EncryptionSdk.Core.OnDecryptInput value)
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

        public static Aws.EncryptionSdk.Core.EncryptedDataKey
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_EncryptedDataKey(
                Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey value)
        {
            Dafny.Aws.EncryptionSdk.Core.EncryptedDataKey concrete =
                (Dafny.Aws.EncryptionSdk.Core.EncryptedDataKey)value;
            Aws.EncryptionSdk.Core.EncryptedDataKey converted = new Aws.EncryptionSdk.Core.EncryptedDataKey();
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
                Aws.EncryptionSdk.Core.EncryptedDataKey value)
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

        public static Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return new CryptographicMaterialsManager(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            if (value is CryptographicMaterialsManager valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.EncryptionSdk.Core.ICryptographicMaterialsManager are not supported yet");
        }

        public static Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput();
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
                Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput value)
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

        public static Aws.EncryptionSdk.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(
                Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy value)
        {
            if (value.is_FORBID__ENCRYPT__ALLOW__DECRYPT)
                return Aws.EncryptionSdk.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT)
                return Aws.EncryptionSdk.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT)
                return Aws.EncryptionSdk.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.CommitmentPolicy value");
        }

        public static Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(
                Aws.EncryptionSdk.Core.CommitmentPolicy value)
        {
            if (Aws.EncryptionSdk.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.EncryptionSdk.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.EncryptionSdk.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT.Equals(value))
                return Dafny.Aws.EncryptionSdk.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
            throw new System.ArgumentException("Invalid Aws.EncryptionSdk.Core.CommitmentPolicy value");
        }

        public static System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey>
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.EncryptionSdk.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(
                Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryKeyringInput value)
        {
            Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput concrete =
                (Dafny.Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput)value;
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput converted =
                new Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.EncryptionSdk.Core.DiscoveryFilter)
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
                Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput value)
        {
            Aws.EncryptionSdk.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.EncryptionSdk.Core.DiscoveryFilter)null;
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

        public static Aws.EncryptionSdk.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter value)
        {
            Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter concrete = (Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter)value;
            Aws.EncryptionSdk.Core.DiscoveryFilter converted = new Aws.EncryptionSdk.Core.DiscoveryFilter();
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
                Aws.EncryptionSdk.Core.DiscoveryFilter value)
        {
            return new Dafny.Aws.EncryptionSdk.Core.DiscoveryFilter(
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M10_accountIds(value.AccountIds),
                ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter__M9_partition(value.Partition));
        }

        public static Aws.EncryptionSdk.Core.EncryptionMaterials
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(
                Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IEncryptionMaterials
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput__M9_materials(
                Aws.EncryptionSdk.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S19_EncryptionMaterials(value);
        }

        public static Aws.EncryptionSdk.Core.IKeyring
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member(
                Dafny.Aws.EncryptionSdk.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core.IKeyring
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S11_KeyringList__M6_member(
                Aws.EncryptionSdk.Core.IKeyring value)
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

        public static Aws.EncryptionSdk.Core.DiscoveryFilter
            FromDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.EncryptionSdk.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_DiscoveryFilter(
                        (Aws.EncryptionSdk.Core.DiscoveryFilter)value));
        }

        public static Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersBaseException
            FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException value)
        {
            if (value is Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException)
                return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                    (Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException
            ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersBaseException value)
        {
            if (value is Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException)
                return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersException(
                    (Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
