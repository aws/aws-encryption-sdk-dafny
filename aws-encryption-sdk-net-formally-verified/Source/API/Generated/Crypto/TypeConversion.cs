// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Encryption.Core;

namespace Aws.Encryption.Core
{
    internal static class TypeConversion
    {
        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput__M6_client(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput__M6_client(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Aws.Encryption.Core.DecryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(
                Dafny.Aws.Encryption.Core._IDecryptionMaterials value)
        {
            Dafny.Aws.Encryption.Core.DecryptionMaterials concrete =
                (Dafny.Aws.Encryption.Core.DecryptionMaterials)value;
            Aws.Encryption.Core.DecryptionMaterials converted = new Aws.Encryption.Core.DecryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Encryption.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                    concrete.encryptionContext);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.verificationKey.is_Some)
                converted.VerificationKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                        concrete.verificationKey);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IDecryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(
                Aws.Encryption.Core.DecryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_verificationKey =
                value.IsSetVerificationKey() ? value.VerificationKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Encryption.Core.DecryptionMaterials(
                ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                    var_plaintextDataKey),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                    var_verificationKey));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(Dafny.ISequence<byte> value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return utf8.GetString(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(string value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
        }

        public static Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
                    concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(value.KmsKeyId),
                ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>
            FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(
                Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey> value)
        {
            return new System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(
                System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey> value)
        {
            return Dafny.Sequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList__M6_member).ToArray());
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>
            ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(
                        (Aws.Encryption.Core.AlgorithmSuiteId)value));
        }

        public static Aws.Encryption.Core.IKeyring
            FromDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList__M6_member(
                Dafny.Aws.Encryption.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Encryption.Core.IKeyring
            ToDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList__M6_member(Aws.Encryption.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Aws.Encryption.Core.EncryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Dafny.Aws.Encryption.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IEncryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Aws.Encryption.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput__M6_region(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput__M6_region(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Encryption.Core.DecryptMaterialsOutput
            FromDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput(
                Dafny.Aws.Encryption.Core._IDecryptMaterialsOutput value)
        {
            Dafny.Aws.Encryption.Core.DecryptMaterialsOutput concrete =
                (Dafny.Aws.Encryption.Core.DecryptMaterialsOutput)value;
            Aws.Encryption.Core.DecryptMaterialsOutput converted = new Aws.Encryption.Core.DecryptMaterialsOutput();
            converted.DecryptionMaterials =
                (Aws.Encryption.Core.DecryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    concrete.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IDecryptMaterialsOutput
            ToDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput(
                Aws.Encryption.Core.DecryptMaterialsOutput value)
        {
            return new Dafny.Aws.Encryption.Core.DecryptMaterialsOutput(
                ToDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    value.DecryptionMaterials));
        }

        public static Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Dafny.Aws.Encryption.Core._ICreateDefaultCryptographicMaterialsManagerInput value)
        {
            Dafny.Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput concrete =
                (Dafny.Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput)value;
            Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput converted =
                new Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput();
            converted.Keyring =
                (Aws.Encryption.Core.IKeyring)
                FromDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateDefaultCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput value)
        {
            return new Dafny.Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    value.Keyring));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.IKeyring>
            FromDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                Dafny.ISequence<Dafny.Aws.Encryption.Core.IKeyring> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core.IKeyring>
            ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                System.Collections.Generic.List<Aws.Encryption.Core.IKeyring> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList(value);
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>
            FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Aws.Encryption.Core.IClientSupplier
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IClientSupplier)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier>
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.Encryption.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                        (Aws.Encryption.Core.IClientSupplier)value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Aws.Encryption.Core.IClientSupplier
            FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IClientSupplier)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier>
            ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Aws.Encryption.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                        (Aws.Encryption.Core.IClientSupplier)value));
        }

        public static Aws.Encryption.Core.DiscoveryFilter
            FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(
                Dafny.Aws.Encryption.Core._IDiscoveryFilter value)
        {
            Dafny.Aws.Encryption.Core.DiscoveryFilter concrete = (Dafny.Aws.Encryption.Core.DiscoveryFilter)value;
            Aws.Encryption.Core.DiscoveryFilter converted = new Aws.Encryption.Core.DiscoveryFilter();
            converted.AccountIds =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M10_accountIds(concrete.accountIds);
            converted.Partition =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M9_partition(
                    concrete.partition);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IDiscoveryFilter
            ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(Aws.Encryption.Core.DiscoveryFilter value)
        {
            return new Dafny.Aws.Encryption.Core.DiscoveryFilter(
                ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M10_accountIds(value.AccountIds),
                ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M9_partition(value.Partition));
        }

        public static Aws.Encryption.Core.IAwsCryptographicMaterialProviders
            FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProviders value)
        {
            return new AwsCryptographicMaterialProviders(value);
        }

        public static Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProviders
            ToDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                Aws.Encryption.Core.IAwsCryptographicMaterialProviders value)
        {
            if (value is AwsCryptographicMaterialProviders valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Encryption.Core.IAwsCryptographicMaterialProviders are not supported yet");
        }

        public static Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Encryption.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput value)
        {
            Aws.Encryption.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.Encryption.Core.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                    value.KmsClient),
                ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static Aws.Encryption.Core.EncryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput__M9_materials(
                Dafny.Aws.Encryption.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IEncryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput__M9_materials(
                Aws.Encryption.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M10_ciphertext(Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M10_ciphertext(System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Encryption.Core.CommitmentPolicy
            FromDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(
                Dafny.Aws.Encryption.Core._ICommitmentPolicy value)
        {
            if (value.is_FORBID__ENCRYPT__ALLOW__DECRYPT)
                return Aws.Encryption.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT)
                return Aws.Encryption.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT)
                return Aws.Encryption.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.CommitmentPolicy value");
        }

        public static Dafny.Aws.Encryption.Core._ICommitmentPolicy
            ToDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(Aws.Encryption.Core.CommitmentPolicy value)
        {
            if (Aws.Encryption.Core.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.Encryption.Core.CommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.Encryption.Core.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.Encryption.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.Encryption.Core.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT.Equals(value))
                return Dafny.Aws.Encryption.Core.CommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.CommitmentPolicy value");
        }

        public static Aws.Encryption.Core.GetEncryptionMaterialsOutput
            FromDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput(
                Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsOutput value)
        {
            Dafny.Aws.Encryption.Core.GetEncryptionMaterialsOutput concrete =
                (Dafny.Aws.Encryption.Core.GetEncryptionMaterialsOutput)value;
            Aws.Encryption.Core.GetEncryptionMaterialsOutput converted =
                new Aws.Encryption.Core.GetEncryptionMaterialsOutput();
            converted.EncryptionMaterials =
                (Aws.Encryption.Core.EncryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    concrete.encryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsOutput
            ToDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput(
                Aws.Encryption.Core.GetEncryptionMaterialsOutput value)
        {
            return new Dafny.Aws.Encryption.Core.GetEncryptionMaterialsOutput(
                ToDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    value.EncryptionMaterials));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Aws.Encryption.Core.IClientSupplier
            FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                Dafny.Aws.Encryption.Core.IClientSupplier value)
        {
            return new ClientSupplier(value);
        }

        public static Dafny.Aws.Encryption.Core.IClientSupplier
            ToDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                Aws.Encryption.Core.IClientSupplier value)
        {
            if (value is ClientSupplier valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Encryption.Core.IClientSupplier are not supported yet");
        }

        public static Aws.Encryption.Core.CreateMultiKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateMultiKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateMultiKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateMultiKeyringInput)value;
            Aws.Encryption.Core.CreateMultiKeyringInput converted = new Aws.Encryption.Core.CreateMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (Aws.Encryption.Core.IKeyring)
                    FromDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                        concrete.generator);
            converted.ChildKeyrings =
                (System.Collections.Generic.List<Aws.Encryption.Core.IKeyring>)
                FromDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                    concrete.childKeyrings);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateMultiKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput(
                Aws.Encryption.Core.CreateMultiKeyringInput value)
        {
            Aws.Encryption.Core.IKeyring var_generator =
                value.IsSetGenerator() ? value.Generator : (Aws.Encryption.Core.IKeyring)null;
            return new Dafny.Aws.Encryption.Core.CreateMultiKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M13_childKeyrings(
                    value.ChildKeyrings));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M10_accountIds(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M10_accountIds(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList(value);
        }

        public static Aws.Encryption.Core.DecryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput__M9_materials(
                Dafny.Aws.Encryption.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IDecryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput__M9_materials(
                Aws.Encryption.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static Aws.Encryption.Core.OnDecryptOutput
            FromDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput(
                Dafny.Aws.Encryption.Core._IOnDecryptOutput value)
        {
            Dafny.Aws.Encryption.Core.OnDecryptOutput concrete = (Dafny.Aws.Encryption.Core.OnDecryptOutput)value;
            Aws.Encryption.Core.OnDecryptOutput converted = new Aws.Encryption.Core.OnDecryptOutput();
            converted.Materials =
                (Aws.Encryption.Core.DecryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IOnDecryptOutput
            ToDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput(Aws.Encryption.Core.OnDecryptOutput value)
        {
            return new Dafny.Aws.Encryption.Core.OnDecryptOutput(
                ToDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput__M9_materials(value.Materials));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return value.ItemEnumerable.ToDictionary(
                pair => FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M3_key(pair.Car),
                pair => FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M5_value(pair.Cdr));
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromCollection(value.Select(pair =>
                new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(
                    ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M3_key(pair.Key),
                    ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M5_value(pair.Value))
            ));
        }

        public static Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsMultiKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                        concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Encryption.Core.IClientSupplier)
                    FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsMultiKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.Encryption.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.Encryption.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(var_kmsKeyIds),
                ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static Aws.Encryption.Core.IClientSupplier
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IClientSupplier)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier>
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Aws.Encryption.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                        (Aws.Encryption.Core.IClientSupplier)value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.OnDecryptInput FromDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput(
            Dafny.Aws.Encryption.Core._IOnDecryptInput value)
        {
            Dafny.Aws.Encryption.Core.OnDecryptInput concrete = (Dafny.Aws.Encryption.Core.OnDecryptInput)value;
            Aws.Encryption.Core.OnDecryptInput converted = new Aws.Encryption.Core.OnDecryptInput();
            converted.Materials =
                (Aws.Encryption.Core.DecryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M9_materials(concrete.materials);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IOnDecryptInput
            ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput(Aws.Encryption.Core.OnDecryptInput value)
        {
            return new Dafny.Aws.Encryption.Core.OnDecryptInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M9_materials(value.Materials),
                ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                    value.EncryptedDataKeys));
        }

        public static Aws.Encryption.Core.EncryptedDataKey
            FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey(
                Dafny.Aws.Encryption.Core._IEncryptedDataKey value)
        {
            Dafny.Aws.Encryption.Core.EncryptedDataKey concrete = (Dafny.Aws.Encryption.Core.EncryptedDataKey)value;
            Aws.Encryption.Core.EncryptedDataKey converted = new Aws.Encryption.Core.EncryptedDataKey();
            converted.KeyProviderId =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M13_keyProviderId(
                    concrete.keyProviderId);
            converted.KeyProviderInfo =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
                    concrete.keyProviderInfo);
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M10_ciphertext(
                    concrete.ciphertext);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IEncryptedDataKey
            ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey(Aws.Encryption.Core.EncryptedDataKey value)
        {
            return new Dafny.Aws.Encryption.Core.EncryptedDataKey(
                ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M13_keyProviderId(value.KeyProviderId),
                ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M15_keyProviderInfo(
                    value.KeyProviderInfo),
                ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M10_ciphertext(value.Ciphertext));
        }

        public static Aws.Encryption.Core.IKeyring
            FromDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IKeyring)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring>
            ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput__M9_generator(
                Aws.Encryption.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference((Aws.Encryption.Core.IKeyring)value));
        }

        public static Aws.Encryption.Core.PaddingScheme
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Dafny.Aws.Encryption.Core._IPaddingScheme value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S13_PaddingScheme(value);
        }

        public static Dafny.Aws.Encryption.Core._IPaddingScheme
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Aws.Encryption.Core.PaddingScheme value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S13_PaddingScheme(value);
        }

        public static Aws.Encryption.Core.IKeyring FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(
            Dafny.Aws.Encryption.Core.IKeyring value)
        {
            return new Keyring(value);
        }

        public static Dafny.Aws.Encryption.Core.IKeyring ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(
            Aws.Encryption.Core.IKeyring value)
        {
            if (value is Keyring valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Encryption.Core.IKeyring are not supported yet");
        }

        public static Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Encryption.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Encryption.Core.IClientSupplier)
                    FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Aws.Encryption.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.Encryption.Core.DiscoveryFilter)null;
            Aws.Encryption.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.Encryption.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    value.Regions),
                ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(
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
            ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            if (value is Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl)
            {
                return new Com.Amazonaws.Kms.KeyManagementServiceShim(impl);
            }

            throw new System.ArgumentException(
                "Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Encryption.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Encryption.Core.IClientSupplier)
                    FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Aws.Encryption.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.Encryption.Core.DiscoveryFilter)null;
            Aws.Encryption.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.Encryption.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                    value.Regions),
                ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static Aws.Encryption.Core.IClientSupplier
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IClientSupplier)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IClientSupplier>
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.Encryption.Core.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                        (Aws.Encryption.Core.IClientSupplier)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S6_Region(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S6_Region(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S9_AccountId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S9_AccountId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Aws.Encryption.Core.OnEncryptInput FromDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput(
            Dafny.Aws.Encryption.Core._IOnEncryptInput value)
        {
            Dafny.Aws.Encryption.Core.OnEncryptInput concrete = (Dafny.Aws.Encryption.Core.OnEncryptInput)value;
            Aws.Encryption.Core.OnEncryptInput converted = new Aws.Encryption.Core.OnEncryptInput();
            converted.Materials =
                (Aws.Encryption.Core.EncryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IOnEncryptInput
            ToDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput(Aws.Encryption.Core.OnEncryptInput value)
        {
            return new Dafny.Aws.Encryption.Core.OnEncryptInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput__M9_materials(value.Materials));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384)
                return Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.AlgorithmSuiteId value");
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY();
            if (Aws.Encryption.Core.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384.Equals(value))
                return Dafny.Aws.Encryption.Core.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384();
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.AlgorithmSuiteId value");
        }

        public static Aws.Encryption.Core.DiscoveryFilter
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.Encryption.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(
                        (Aws.Encryption.Core.DiscoveryFilter)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M5_value(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M5_value(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Aws.Encryption.Core.IKeyring FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(
            Dafny.Aws.Encryption.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static Dafny.Aws.Encryption.Core.IKeyring
            ToDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(Aws.Encryption.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList__M6_member).ToArray());
        }

        public static Aws.Encryption.Core.AesWrappingAlg FromDafny_N3_aws__N10_encryption__N4_core__S14_AesWrappingAlg(
            Dafny.Aws.Encryption.Core._IAesWrappingAlg value)
        {
            if (value.is_ALG__AES128__GCM__IV12__TAG16)
                return Aws.Encryption.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
            if (value.is_ALG__AES192__GCM__IV12__TAG16)
                return Aws.Encryption.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
            if (value.is_ALG__AES256__GCM__IV12__TAG16)
                return Aws.Encryption.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.AesWrappingAlg value");
        }

        public static Dafny.Aws.Encryption.Core._IAesWrappingAlg
            ToDafny_N3_aws__N10_encryption__N4_core__S14_AesWrappingAlg(Aws.Encryption.Core.AesWrappingAlg value)
        {
            if (Aws.Encryption.Core.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Encryption.Core.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
            if (Aws.Encryption.Core.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Encryption.Core.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
            if (Aws.Encryption.Core.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Encryption.Core.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.AesWrappingAlg value");
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList__M6_member).ToArray());
        }

        public static Aws.Encryption.Core.CreateDefaultClientSupplierInput
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateDefaultClientSupplierInput(
                Dafny.Aws.Encryption.Core._ICreateDefaultClientSupplierInput value)
        {
            Dafny.Aws.Encryption.Core.CreateDefaultClientSupplierInput concrete =
                (Dafny.Aws.Encryption.Core.CreateDefaultClientSupplierInput)value;
            Aws.Encryption.Core.CreateDefaultClientSupplierInput converted =
                new Aws.Encryption.Core.CreateDefaultClientSupplierInput();
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateDefaultClientSupplierInput
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateDefaultClientSupplierInput(
                Aws.Encryption.Core.CreateDefaultClientSupplierInput value)
        {
            return new Dafny.Aws.Encryption.Core.CreateDefaultClientSupplierInput();
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S10_RegionList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S10_RegionList__M6_member).ToArray());
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId((string)value));
        }

        public static Aws.Encryption.Core.DecryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M9_materials(
                Dafny.Aws.Encryption.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IDecryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M9_materials(
                Aws.Encryption.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static string
            FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static Aws.Encryption.Core.IKeyring
            FromDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Dafny.Aws.Encryption.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Encryption.Core.IKeyring
            ToDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Aws.Encryption.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S18_KmsClientReference(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.CommitmentPolicy
            FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.Encryption.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.Encryption.Core._ICommitmentPolicy
            ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Aws.Encryption.Core.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.DiscoveryFilter
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.Encryption.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(
                        (Aws.Encryption.Core.DiscoveryFilter)value));
        }

        public static Aws.Encryption.Core.CommitmentPolicy
            FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.Encryption.Core._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.Encryption.Core._ICommitmentPolicy
            ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Aws.Encryption.Core.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(value);
        }

        public static Aws.Encryption.Core.CreateRawRsaKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateRawRsaKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateRawRsaKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateRawRsaKeyringInput)value;
            Aws.Encryption.Core.CreateRawRsaKeyringInput converted = new Aws.Encryption.Core.CreateRawRsaKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(
                    concrete.keyName);
            converted.PaddingScheme =
                (Aws.Encryption.Core.PaddingScheme)
                FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                    concrete.paddingScheme);
            if (concrete.publicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(
                        concrete.publicKey);
            if (concrete.privateKey.is_Some)
                converted.PrivateKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(
                        concrete.privateKey);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateRawRsaKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput(
                Aws.Encryption.Core.CreateRawRsaKeyringInput value)
        {
            System.IO.MemoryStream var_publicKey =
                value.IsSetPublicKey() ? value.PublicKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_privateKey =
                value.IsSetPrivateKey() ? value.PrivateKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Encryption.Core.CreateRawRsaKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    value.KeyNamespace),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                    value.PaddingScheme),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M9_publicKey(var_publicKey),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M10_privateKey(var_privateKey));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M13_keyProviderId(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey__M13_keyProviderId(string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
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
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.GetClientInput FromDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput(
            Dafny.Aws.Encryption.Core._IGetClientInput value)
        {
            Dafny.Aws.Encryption.Core.GetClientInput concrete = (Dafny.Aws.Encryption.Core.GetClientInput)value;
            Aws.Encryption.Core.GetClientInput converted = new Aws.Encryption.Core.GetClientInput();
            converted.Region =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput__M6_region(concrete.region);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IGetClientInput
            ToDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput(Aws.Encryption.Core.GetClientInput value)
        {
            return new Dafny.Aws.Encryption.Core.GetClientInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S14_GetClientInput__M6_region(value.Region));
        }

        public static Aws.Encryption.Core.EncryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput__M9_materials(
                Dafny.Aws.Encryption.Core._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IEncryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput__M9_materials(
                Aws.Encryption.Core.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(value);
        }

        public static Aws.Encryption.Core.AesWrappingAlg
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Dafny.Aws.Encryption.Core._IAesWrappingAlg value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S14_AesWrappingAlg(value);
        }

        public static Dafny.Aws.Encryption.Core._IAesWrappingAlg
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Aws.Encryption.Core.AesWrappingAlg value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S14_AesWrappingAlg(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S12_KmsKeyIdList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S10_RegionList(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Aws.Encryption.Core.DiscoveryFilter
            FromDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.Encryption.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(
                        (Aws.Encryption.Core.DiscoveryFilter)value));
        }

        public static string
            FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S10_RegionList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S10_RegionList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S6_Region(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList__M6_member(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Encryption.Core.DecryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Dafny.Aws.Encryption.Core._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Encryption.Core._IDecryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Aws.Encryption.Core.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M3_key(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext__M3_key(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S9_Utf8Bytes(value);
        }

        public static Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkMultiKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)
                    FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                        concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Encryption.Core.IClientSupplier)
                    FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkMultiKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.Encryption.Core.IClientSupplier var_clientSupplier = value.IsSetClientSupplier()
                ? value.ClientSupplier
                : (Aws.Encryption.Core.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                    var_generator),
                ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                    var_kmsKeyIds),
                ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static Aws.Encryption.Core.PaddingScheme FromDafny_N3_aws__N10_encryption__N4_core__S13_PaddingScheme(
            Dafny.Aws.Encryption.Core._IPaddingScheme value)
        {
            if (value.is_PKCS1) return Aws.Encryption.Core.PaddingScheme.PKCS1;
            if (value.is_OAEP__SHA1__MGF1) return Aws.Encryption.Core.PaddingScheme.OAEP_SHA1_MGF1;
            if (value.is_OAEP__SHA256__MGF1) return Aws.Encryption.Core.PaddingScheme.OAEP_SHA256_MGF1;
            if (value.is_OAEP__SHA384__MGF1) return Aws.Encryption.Core.PaddingScheme.OAEP_SHA384_MGF1;
            if (value.is_OAEP__SHA512__MGF1) return Aws.Encryption.Core.PaddingScheme.OAEP_SHA512_MGF1;
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.PaddingScheme value");
        }

        public static Dafny.Aws.Encryption.Core._IPaddingScheme
            ToDafny_N3_aws__N10_encryption__N4_core__S13_PaddingScheme(Aws.Encryption.Core.PaddingScheme value)
        {
            if (Aws.Encryption.Core.PaddingScheme.PKCS1.Equals(value))
                return Dafny.Aws.Encryption.Core.PaddingScheme.create_PKCS1();
            if (Aws.Encryption.Core.PaddingScheme.OAEP_SHA1_MGF1.Equals(value))
                return Dafny.Aws.Encryption.Core.PaddingScheme.create_OAEP__SHA1__MGF1();
            if (Aws.Encryption.Core.PaddingScheme.OAEP_SHA256_MGF1.Equals(value))
                return Dafny.Aws.Encryption.Core.PaddingScheme.create_OAEP__SHA256__MGF1();
            if (Aws.Encryption.Core.PaddingScheme.OAEP_SHA384_MGF1.Equals(value))
                return Dafny.Aws.Encryption.Core.PaddingScheme.create_OAEP__SHA384__MGF1();
            if (Aws.Encryption.Core.PaddingScheme.OAEP_SHA512_MGF1.Equals(value))
                return Dafny.Aws.Encryption.Core.PaddingScheme.create_OAEP__SHA512__MGF1();
            throw new System.ArgumentException("Invalid Aws.Encryption.Core.PaddingScheme value");
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Aws.Encryption.Core.AwsCryptographicMaterialProvidersException
            FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException(
                Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException value)
        {
            return new Aws.Encryption.Core.AwsCryptographicMaterialProvidersException(
                FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                    value.message));
        }

        public static Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException
            ToDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException(
                Aws.Encryption.Core.AwsCryptographicMaterialProvidersException value)
        {
            Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException converted =
                new Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException();
            converted.message =
                ToDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException__M7_message(
                    value.Message);
            return converted;
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S9_AccountId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S13_AccountIdList__M6_member(
            string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S9_AccountId(value);
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>
            FromDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core._IEncryptedDataKey>
            ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList__M6_member).ToArray());
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Encryption.Core.DecryptMaterialsInput
            FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput(
                Dafny.Aws.Encryption.Core._IDecryptMaterialsInput value)
        {
            Dafny.Aws.Encryption.Core.DecryptMaterialsInput concrete =
                (Dafny.Aws.Encryption.Core.DecryptMaterialsInput)value;
            Aws.Encryption.Core.DecryptMaterialsInput converted = new Aws.Encryption.Core.DecryptMaterialsInput();
            converted.AlgorithmSuiteId =
                (Aws.Encryption.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.CommitmentPolicy =
                (Aws.Encryption.Core.CommitmentPolicy)
                FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IDecryptMaterialsInput
            ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput(
                Aws.Encryption.Core.DecryptMaterialsInput value)
        {
            return new Dafny.Aws.Encryption.Core.DecryptMaterialsInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                    value.CommitmentPolicy),
                ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                    value.EncryptedDataKeys),
                ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext));
        }

        public static Aws.Encryption.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return new CryptographicMaterialsManager(value);
        }

        public static Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            if (value is CryptographicMaterialsManager valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Encryption.Core.ICryptographicMaterialsManager are not supported yet");
        }

        public static Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput converted =
                new Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Encryption.Core.DiscoveryFilter)
                    FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            converted.Region =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                    concrete.region);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Aws.Encryption.Core.DiscoveryFilter var_discoveryFilter = value.IsSetDiscoveryFilter()
                ? value.DiscoveryFilter
                : (Aws.Encryption.Core.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                    value.KmsClient),
                ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                    var_grantTokens),
                ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                    value.Region));
        }

        public static string
            FromDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId((string)value));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput__M6_client(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S15_GetClientOutput__M6_client(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.OnEncryptOutput
            FromDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput(
                Dafny.Aws.Encryption.Core._IOnEncryptOutput value)
        {
            Dafny.Aws.Encryption.Core.OnEncryptOutput concrete = (Dafny.Aws.Encryption.Core.OnEncryptOutput)value;
            Aws.Encryption.Core.OnEncryptOutput converted = new Aws.Encryption.Core.OnEncryptOutput();
            converted.Materials =
                (Aws.Encryption.Core.EncryptionMaterials)
                FromDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput__M9_materials(concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IOnEncryptOutput
            ToDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput(Aws.Encryption.Core.OnEncryptOutput value)
        {
            return new Dafny.Aws.Encryption.Core.OnEncryptOutput(
                ToDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput__M9_materials(value.Materials));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>)value));
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M9_partition(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter__M9_partition(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Encryption.Core.CreateRawAesKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateRawAesKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateRawAesKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateRawAesKeyringInput)value;
            Aws.Encryption.Core.CreateRawAesKeyringInput converted = new Aws.Encryption.Core.CreateRawAesKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(
                    concrete.keyName);
            converted.WrappingKey =
                (System.IO.MemoryStream)
                FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    concrete.wrappingKey);
            converted.WrappingAlg =
                (Aws.Encryption.Core.AesWrappingAlg)
                FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    concrete.wrappingAlg);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateRawAesKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput(
                Aws.Encryption.Core.CreateRawAesKeyringInput value)
        {
            return new Dafny.Aws.Encryption.Core.CreateRawAesKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    value.KeyNamespace),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    value.WrappingKey),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    value.WrappingAlg));
        }

        public static Aws.Encryption.Core.DiscoveryFilter
            FromDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.DiscoveryFilter)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IDiscoveryFilter>
            ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.Encryption.Core.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S15_DiscoveryFilter(
                        (Aws.Encryption.Core.DiscoveryFilter)value));
        }

        public static Aws.Encryption.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return
                FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                    value);
        }

        public static Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return
                ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                    value);
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(string value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S8_KmsKeyId(value);
        }

        public static long?
            FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static Aws.Encryption.Core.GetEncryptionMaterialsInput
            FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput(
                Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsInput value)
        {
            Dafny.Aws.Encryption.Core.GetEncryptionMaterialsInput concrete =
                (Dafny.Aws.Encryption.Core.GetEncryptionMaterialsInput)value;
            Aws.Encryption.Core.GetEncryptionMaterialsInput converted =
                new Aws.Encryption.Core.GetEncryptionMaterialsInput();
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.CommitmentPolicy =
                (Aws.Encryption.Core.CommitmentPolicy)
                FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.Encryption.Core.AlgorithmSuiteId)
                    FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                        concrete.algorithmSuiteId);
            if (concrete.maxPlaintextLength.is_Some)
                converted.MaxPlaintextLength =
                    (long)
                    FromDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                        concrete.maxPlaintextLength);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsInput
            ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput(
                Aws.Encryption.Core.GetEncryptionMaterialsInput value)
        {
            Aws.Encryption.Core.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (Aws.Encryption.Core.AlgorithmSuiteId)null;
            long? var_maxPlaintextLength = value.IsSetMaxPlaintextLength() ? value.MaxPlaintextLength : (long?)null;
            return new Dafny.Aws.Encryption.Core.GetEncryptionMaterialsInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    value.CommitmentPolicy),
                ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                    var_algorithmSuiteId),
                ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                    var_maxPlaintextLength));
        }

        public static Aws.Encryption.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager
            ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M16_plaintextDataKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static string FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput__M7_keyName(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Encryption.Core.EncryptionMaterials
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(
                Dafny.Aws.Encryption.Core._IEncryptionMaterials value)
        {
            Dafny.Aws.Encryption.Core.EncryptionMaterials concrete =
                (Dafny.Aws.Encryption.Core.EncryptionMaterials)value;
            Aws.Encryption.Core.EncryptionMaterials converted = new Aws.Encryption.Core.EncryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Encryption.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Encryption.Core.EncryptedDataKey>)
                FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.signingKey.is_Some)
                converted.SigningKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M10_signingKey(
                        concrete.signingKey);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._IEncryptionMaterials
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials(
                Aws.Encryption.Core.EncryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_signingKey =
                value.IsSetSigningKey() ? value.SigningKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Encryption.Core.EncryptionMaterials(
                ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M17_encryptedDataKeys(
                    value.EncryptedDataKeys),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M16_plaintextDataKey(
                    var_plaintextDataKey),
                ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M10_signingKey(var_signingKey));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M10_signingKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_EncryptionMaterials__M10_signingKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Encryption.Core.CreateAwsKmsKeyringInput
            FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput(
                Dafny.Aws.Encryption.Core._ICreateAwsKmsKeyringInput value)
        {
            Dafny.Aws.Encryption.Core.CreateAwsKmsKeyringInput concrete =
                (Dafny.Aws.Encryption.Core.CreateAwsKmsKeyringInput)value;
            Aws.Encryption.Core.CreateAwsKmsKeyringInput converted = new Aws.Encryption.Core.CreateAwsKmsKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
                    concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                    concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Encryption.Core._ICreateAwsKmsKeyringInput
            ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput(
                Aws.Encryption.Core.CreateAwsKmsKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Encryption.Core.CreateAwsKmsKeyringInput(
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(value.KmsKeyId),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static System.Collections.Generic.List<Aws.Encryption.Core.IKeyring>
            FromDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList(
                Dafny.ISequence<Dafny.Aws.Encryption.Core.IKeyring> value)
        {
            return new System.Collections.Generic.List<Aws.Encryption.Core.IKeyring>(
                value.Elements.Select(FromDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.Encryption.Core.IKeyring>
            ToDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList(
                System.Collections.Generic.List<Aws.Encryption.Core.IKeyring> value)
        {
            return Dafny.Sequence<Dafny.Aws.Encryption.Core.IKeyring>.FromArray(value
                .Select(ToDafny_N3_aws__N10_encryption__N4_core__S11_KeyringList__M6_member).ToArray());
        }

        public static System.IO.MemoryStream
            FromDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__N4_core__S19_DecryptionMaterials__M15_verificationKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Encryption.Core.IKeyring
            FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput__M7_keyring(
                Dafny.Aws.Encryption.Core.IKeyring value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Encryption.Core.IKeyring
            ToDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput__M7_keyring(
                Aws.Encryption.Core.IKeyring value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value);
        }

        public static Aws.Encryption.Core.EncryptedDataKey
            FromDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList__M6_member(
                Dafny.Aws.Encryption.Core._IEncryptedDataKey value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey(value);
        }

        public static Dafny.Aws.Encryption.Core._IEncryptedDataKey
            ToDafny_N3_aws__N10_encryption__N4_core__S20_EncryptedDataKeyList__M6_member(
                Aws.Encryption.Core.EncryptedDataKey value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_EncryptedDataKey(value);
        }

        public static Aws.Encryption.Core.AwsCryptographicMaterialProvidersBaseException
            FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException value)
        {
            if (value is Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException)
                return FromDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException(
                    (Dafny.Aws.Encryption.Core.AwsCryptographicMaterialProvidersException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException
            ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                Aws.Encryption.Core.AwsCryptographicMaterialProvidersBaseException value)
        {
            if (value is Aws.Encryption.Core.AwsCryptographicMaterialProvidersException)
                return ToDafny_N3_aws__N10_encryption__N4_core__S42_AwsCryptographicMaterialProvidersException(
                    (Aws.Encryption.Core.AwsCryptographicMaterialProvidersException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
