// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Crypto;

namespace Aws.Crypto
{
    internal static class TypeConversion
    {
        public static Aws.Crypto.CreateAwsKmsKeyringInput FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput(
            Dafny.Aws.Crypto._ICreateAwsKmsKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsKeyringInput concrete = (Dafny.Aws.Crypto.CreateAwsKmsKeyringInput)value;
            Aws.Crypto.CreateAwsKmsKeyringInput converted = new Aws.Crypto.CreateAwsKmsKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M9_kmsClient(concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M11_grantTokens(concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsKeyringInput
            ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput(Aws.Crypto.CreateAwsKmsKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsKeyringInput(
                ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(value.KmsKeyId),
                ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M11_grantTokens(var_grantTokens));
        }

        public static Aws.Crypto.IClientSupplier FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(
            Dafny.Aws.Crypto.IClientSupplier value)
        {
            return new ClientSupplier(value);
        }

        public static Dafny.Aws.Crypto.IClientSupplier ToDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(
            Aws.Crypto.IClientSupplier value)
        {
            if (value is ClientSupplier valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Crypto.IClientSupplier are not supported yet");
        }

        public static Aws.Crypto.DiscoveryFilter
            FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Crypto.DiscoveryFilter)null
                : FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter>
            ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.Crypto.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter((Aws.Crypto.DiscoveryFilter)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S12_KmsKeyIdList__M6_member(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S12_KmsKeyIdList__M6_member(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M10_accountIds(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S13_AccountIdList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M10_accountIds(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S13_AccountIdList(value);
        }

        public static Aws.Crypto.GetEncryptionMaterialsInput
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(
                Dafny.Aws.Crypto._IGetEncryptionMaterialsInput value)
        {
            Dafny.Aws.Crypto.GetEncryptionMaterialsInput concrete = (Dafny.Aws.Crypto.GetEncryptionMaterialsInput)value;
            Aws.Crypto.GetEncryptionMaterialsInput converted = new Aws.Crypto.GetEncryptionMaterialsInput();
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.CommitmentPolicy =
                (Aws.Crypto.CommitmentPolicy)
                FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    concrete.commitmentPolicy);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.Crypto.AlgorithmSuiteId)
                    FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                        concrete.algorithmSuiteId);
            if (concrete.maxPlaintextLength.is_Some)
                converted.MaxPlaintextLength =
                    (long)FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                        concrete.maxPlaintextLength);
            return converted;
        }

        public static Dafny.Aws.Crypto._IGetEncryptionMaterialsInput
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(Aws.Crypto.GetEncryptionMaterialsInput value)
        {
            Aws.Crypto.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (Aws.Crypto.AlgorithmSuiteId)null;
            long? var_maxPlaintextLength = value.IsSetMaxPlaintextLength() ? value.MaxPlaintextLength : (long?)null;
            return new Dafny.Aws.Crypto.GetEncryptionMaterialsInput(
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                    value.CommitmentPolicy),
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(var_algorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                    var_maxPlaintextLength));
        }

        public static Aws.Crypto.GetEncryptionMaterialsOutput
            FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(
                Dafny.Aws.Crypto._IGetEncryptionMaterialsOutput value)
        {
            Dafny.Aws.Crypto.GetEncryptionMaterialsOutput concrete =
                (Dafny.Aws.Crypto.GetEncryptionMaterialsOutput)value;
            Aws.Crypto.GetEncryptionMaterialsOutput converted = new Aws.Crypto.GetEncryptionMaterialsOutput();
            converted.EncryptionMaterials =
                (Aws.Crypto.EncryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    concrete.encryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Crypto._IGetEncryptionMaterialsOutput
            ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(Aws.Crypto.GetEncryptionMaterialsOutput value)
        {
            return new Dafny.Aws.Crypto.GetEncryptionMaterialsOutput(
                ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    value.EncryptionMaterials));
        }

        public static string FromDafny_N3_aws__N6_crypto__S10_RegionList__M6_member(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S10_RegionList__M6_member(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S15_GetClientOutput(Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S15_GetClientOutput__M6_client(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S15_GetClientOutput(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S15_GetClientOutput__M6_client(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string)null : FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S8_KmsKeyId((string)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S10_RegionList(value);
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N6_crypto__S16_KeyringReference(
            Dafny.Aws.Crypto.IKeyring value)
        {
            return new Keyring(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N6_crypto__S16_KeyringReference(
            Aws.Crypto.IKeyring value)
        {
            if (value is Keyring valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException("Custom implementations of Aws.Crypto.IKeyring are not supported yet");
        }

        public static Aws.Crypto.IClientSupplier
            FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Crypto.IClientSupplier)null
                : FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier>
            ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.Crypto.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S23_ClientSupplierReference((Aws.Crypto.IClientSupplier)value));
        }

        public static Aws.Crypto.GetClientInput FromDafny_N3_aws__N6_crypto__S14_GetClientInput(
            Dafny.Aws.Crypto._IGetClientInput value)
        {
            Dafny.Aws.Crypto.GetClientInput concrete = (Dafny.Aws.Crypto.GetClientInput)value;
            Aws.Crypto.GetClientInput converted = new Aws.Crypto.GetClientInput();
            converted.Region = (string)FromDafny_N3_aws__N6_crypto__S14_GetClientInput__M6_region(concrete.region);
            return converted;
        }

        public static Dafny.Aws.Crypto._IGetClientInput ToDafny_N3_aws__N6_crypto__S14_GetClientInput(
            Aws.Crypto.GetClientInput value)
        {
            return new Dafny.Aws.Crypto.GetClientInput(
                ToDafny_N3_aws__N6_crypto__S14_GetClientInput__M6_region(value.Region));
        }

        public static Aws.Crypto.DecryptionMaterials FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(
            Dafny.Aws.Crypto._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IDecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(
            string value)
        {
            return ToDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return value.ItemEnumerable.ToDictionary(
                pair => FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(pair.Car),
                pair => FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(pair.Cdr));
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromCollection(value.Select(pair =>
                new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(
                    ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(pair.Key),
                    ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(pair.Value))
            ));
        }

        public static Aws.Crypto.DiscoveryFilter
            FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Crypto.DiscoveryFilter)null
                : FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter>
            ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.Crypto.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter((Aws.Crypto.DiscoveryFilter)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M9_partition(Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M9_partition(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Crypto.CreateRawRsaKeyringInput FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput(
            Dafny.Aws.Crypto._ICreateRawRsaKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateRawRsaKeyringInput concrete = (Dafny.Aws.Crypto.CreateRawRsaKeyringInput)value;
            Aws.Crypto.CreateRawRsaKeyringInput converted = new Aws.Crypto.CreateRawRsaKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M7_keyName(concrete.keyName);
            converted.PaddingScheme =
                (Aws.Crypto.PaddingScheme)FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                    concrete.paddingScheme);
            if (concrete.publicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M9_publicKey(
                        concrete.publicKey);
            if (concrete.privateKey.is_Some)
                converted.PrivateKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M10_privateKey(
                        concrete.privateKey);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateRawRsaKeyringInput
            ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput(Aws.Crypto.CreateRawRsaKeyringInput value)
        {
            System.IO.MemoryStream var_publicKey =
                value.IsSetPublicKey() ? value.PublicKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_privateKey =
                value.IsSetPrivateKey() ? value.PrivateKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Crypto.CreateRawRsaKeyringInput(
                ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M12_keyNamespace(value.KeyNamespace),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M13_paddingScheme(value.PaddingScheme),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M9_publicKey(var_publicKey),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M10_privateKey(var_privateKey));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M15_keyProviderInfo(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M15_keyProviderInfo(
            string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.DecryptionMaterials FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(
            Dafny.Aws.Crypto._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IDecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Aws.Crypto.IClientSupplier
            FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Crypto.IClientSupplier)null
                : FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier>
            ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                Aws.Crypto.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S23_ClientSupplierReference((Aws.Crypto.IClientSupplier)value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Aws.Crypto.OnEncryptOutput FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput(
            Dafny.Aws.Crypto._IOnEncryptOutput value)
        {
            Dafny.Aws.Crypto.OnEncryptOutput concrete = (Dafny.Aws.Crypto.OnEncryptOutput)value;
            Aws.Crypto.OnEncryptOutput converted = new Aws.Crypto.OnEncryptOutput();
            converted.Materials =
                (Aws.Crypto.EncryptionMaterials)FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(
                    concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto._IOnEncryptOutput ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput(
            Aws.Crypto.OnEncryptOutput value)
        {
            return new Dafny.Aws.Crypto.OnEncryptOutput(
                ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(value.Materials));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Aws.Crypto.DecryptMaterialsInput FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(
            Dafny.Aws.Crypto._IDecryptMaterialsInput value)
        {
            Dafny.Aws.Crypto.DecryptMaterialsInput concrete = (Dafny.Aws.Crypto.DecryptMaterialsInput)value;
            Aws.Crypto.DecryptMaterialsInput converted = new Aws.Crypto.DecryptMaterialsInput();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            converted.CommitmentPolicy =
                (Aws.Crypto.CommitmentPolicy)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_commitmentPolicy(concrete.commitmentPolicy);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                    concrete.encryptedDataKeys);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(
                    concrete.encryptionContext);
            return converted;
        }

        public static Dafny.Aws.Crypto._IDecryptMaterialsInput ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(
            Aws.Crypto.DecryptMaterialsInput value)
        {
            return new Dafny.Aws.Crypto.DecryptMaterialsInput(
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_commitmentPolicy(value.CommitmentPolicy),
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(value.EncryptedDataKeys),
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(value.EncryptionContext));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S10_RegionList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S10_RegionList(value);
        }

        public static Aws.Crypto.DiscoveryFilter
            FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Crypto.DiscoveryFilter)null
                : FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter>
            ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                Aws.Crypto.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter((Aws.Crypto.DiscoveryFilter)value));
        }

        public static Aws.Crypto.DecryptMaterialsOutput FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(
            Dafny.Aws.Crypto._IDecryptMaterialsOutput value)
        {
            Dafny.Aws.Crypto.DecryptMaterialsOutput concrete = (Dafny.Aws.Crypto.DecryptMaterialsOutput)value;
            Aws.Crypto.DecryptMaterialsOutput converted = new Aws.Crypto.DecryptMaterialsOutput();
            converted.DecryptionMaterials =
                (Aws.Crypto.DecryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    concrete.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Crypto._IDecryptMaterialsOutput ToDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(
            Aws.Crypto.DecryptMaterialsOutput value)
        {
            return new Dafny.Aws.Crypto.DecryptMaterialsOutput(
                ToDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    value.DecryptionMaterials));
        }

        public static Aws.Crypto.IKeyring
            FromDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring
            ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                Aws.Crypto.IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Aws.Crypto.CommitmentPolicy FromDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(
            Dafny.Aws.Crypto._ICommitmentPolicy value)
        {
            if (value.is_FORBID__ENCRYPT__ALLOW__DECRYPT)
                return Aws.Crypto.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__ALLOW__DECRYPT)
                return Aws.Crypto.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
            if (value.is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT)
                return Aws.Crypto.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
            throw new System.ArgumentException("Invalid Aws.Crypto.CommitmentPolicy value");
        }

        public static Dafny.Aws.Crypto._ICommitmentPolicy ToDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(
            Aws.Crypto.CommitmentPolicy value)
        {
            if (Aws.Crypto.CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.Crypto.CommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.Crypto.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT.Equals(value))
                return Dafny.Aws.Crypto.CommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
            if (Aws.Crypto.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT.Equals(value))
                return Dafny.Aws.Crypto.CommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
            throw new System.ArgumentException("Invalid Aws.Crypto.CommitmentPolicy value");
        }

        public static Aws.Crypto.PaddingScheme FromDafny_N3_aws__N6_crypto__S13_PaddingScheme(
            Dafny.Aws.Crypto._IPaddingScheme value)
        {
            if (value.is_PKCS1) return Aws.Crypto.PaddingScheme.PKCS1;
            if (value.is_OAEP__SHA1__MGF1) return Aws.Crypto.PaddingScheme.OAEP_SHA1_MGF1;
            if (value.is_OAEP__SHA256__MGF1) return Aws.Crypto.PaddingScheme.OAEP_SHA256_MGF1;
            if (value.is_OAEP__SHA384__MGF1) return Aws.Crypto.PaddingScheme.OAEP_SHA384_MGF1;
            if (value.is_OAEP__SHA512__MGF1) return Aws.Crypto.PaddingScheme.OAEP_SHA512_MGF1;
            throw new System.ArgumentException("Invalid Aws.Crypto.PaddingScheme value");
        }

        public static Dafny.Aws.Crypto._IPaddingScheme ToDafny_N3_aws__N6_crypto__S13_PaddingScheme(
            Aws.Crypto.PaddingScheme value)
        {
            if (Aws.Crypto.PaddingScheme.PKCS1.Equals(value)) return Dafny.Aws.Crypto.PaddingScheme.create_PKCS1();
            if (Aws.Crypto.PaddingScheme.OAEP_SHA1_MGF1.Equals(value))
                return Dafny.Aws.Crypto.PaddingScheme.create_OAEP__SHA1__MGF1();
            if (Aws.Crypto.PaddingScheme.OAEP_SHA256_MGF1.Equals(value))
                return Dafny.Aws.Crypto.PaddingScheme.create_OAEP__SHA256__MGF1();
            if (Aws.Crypto.PaddingScheme.OAEP_SHA384_MGF1.Equals(value))
                return Dafny.Aws.Crypto.PaddingScheme.create_OAEP__SHA384__MGF1();
            if (Aws.Crypto.PaddingScheme.OAEP_SHA512_MGF1.Equals(value))
                return Dafny.Aws.Crypto.PaddingScheme.create_OAEP__SHA512__MGF1();
            throw new System.ArgumentException("Invalid Aws.Crypto.PaddingScheme value");
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static Aws.Crypto.AesWrappingAlg
            FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Dafny.Aws.Crypto._IAesWrappingAlg value)
        {
            return FromDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(value);
        }

        public static Dafny.Aws.Crypto._IAesWrappingAlg
            ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(Aws.Crypto.AesWrappingAlg value)
        {
            return ToDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(value);
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_aws__N6_crypto__S12_KmsKeyIdList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S12_KmsKeyIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N6_crypto__S12_KmsKeyIdList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S12_KmsKeyIdList__M6_member).ToArray());
        }

        public static string FromDafny_N3_aws__N6_crypto__S13_AccountIdList__M6_member(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_AccountId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S13_AccountIdList__M6_member(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_AccountId(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Aws.Crypto.DiscoveryFilter FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(
            Dafny.Aws.Crypto._IDiscoveryFilter value)
        {
            Dafny.Aws.Crypto.DiscoveryFilter concrete = (Dafny.Aws.Crypto.DiscoveryFilter)value;
            Aws.Crypto.DiscoveryFilter converted = new Aws.Crypto.DiscoveryFilter();
            converted.AccountIds =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M10_accountIds(concrete.accountIds);
            converted.Partition =
                (string)FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M9_partition(concrete.partition);
            return converted;
        }

        public static Dafny.Aws.Crypto._IDiscoveryFilter ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(
            Aws.Crypto.DiscoveryFilter value)
        {
            return new Dafny.Aws.Crypto.DiscoveryFilter(
                ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M10_accountIds(value.AccountIds),
                ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter__M9_partition(value.Partition));
        }

        public static Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput
            FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsMrkMultiKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput)value;
            Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput converted = new Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Crypto.IClientSupplier)
                    FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsMrkMultiKeyringInput
            ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput(
                Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.Crypto.IClientSupplier var_clientSupplier =
                value.IsSetClientSupplier() ? value.ClientSupplier : (Aws.Crypto.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput(
                ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(var_kmsKeyIds),
                ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(var_clientSupplier),
                ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(var_grantTokens));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S14_GetClientInput__M6_region(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S14_GetClientInput__M6_region(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput)value;
            Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput converted =
                new Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(
                    concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Crypto.DiscoveryFilter)
                    FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Crypto.IClientSupplier)
                    FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput value)
        {
            Aws.Crypto.DiscoveryFilter var_discoveryFilter =
                value.IsSetDiscoveryFilter() ? value.DiscoveryFilter : (Aws.Crypto.DiscoveryFilter)null;
            Aws.Crypto.IClientSupplier var_clientSupplier =
                value.IsSetClientSupplier() ? value.ClientSupplier : (Aws.Crypto.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M7_regions(value.Regions),
                ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static string FromDafny_N3_aws__N6_crypto__S14_GrantTokenList__M6_member(Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S14_GrantTokenList__M6_member(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S9_AccountId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S9_AccountId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Aws.Crypto.CreateDefaultClientSupplierInput
            FromDafny_N3_aws__N6_crypto__S32_CreateDefaultClientSupplierInput(
                Dafny.Aws.Crypto._ICreateDefaultClientSupplierInput value)
        {
            Dafny.Aws.Crypto.CreateDefaultClientSupplierInput concrete =
                (Dafny.Aws.Crypto.CreateDefaultClientSupplierInput)value;
            Aws.Crypto.CreateDefaultClientSupplierInput converted = new Aws.Crypto.CreateDefaultClientSupplierInput();
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateDefaultClientSupplierInput
            ToDafny_N3_aws__N6_crypto__S32_CreateDefaultClientSupplierInput(
                Aws.Crypto.CreateDefaultClientSupplierInput value)
        {
            return new Dafny.Aws.Crypto.CreateDefaultClientSupplierInput();
        }

        public static Aws.Crypto.OnEncryptInput FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput(
            Dafny.Aws.Crypto._IOnEncryptInput value)
        {
            Dafny.Aws.Crypto.OnEncryptInput concrete = (Dafny.Aws.Crypto.OnEncryptInput)value;
            Aws.Crypto.OnEncryptInput converted = new Aws.Crypto.OnEncryptInput();
            converted.Materials =
                (Aws.Crypto.EncryptionMaterials)FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(
                    concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto._IOnEncryptInput ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput(
            Aws.Crypto.OnEncryptInput value)
        {
            return new Dafny.Aws.Crypto.OnEncryptInput(
                ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(value.Materials));
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(
            Dafny.Aws.Crypto._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IEncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Aws.Crypto.CreateMultiKeyringInput FromDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(
            Dafny.Aws.Crypto._ICreateMultiKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateMultiKeyringInput concrete = (Dafny.Aws.Crypto.CreateMultiKeyringInput)value;
            Aws.Crypto.CreateMultiKeyringInput converted = new Aws.Crypto.CreateMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (Aws.Crypto.IKeyring)FromDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M9_generator(
                        concrete.generator);
            converted.ChildKeyrings =
                (System.Collections.Generic.List<Aws.Crypto.IKeyring>)
                FromDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M13_childKeyrings(concrete.childKeyrings);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateMultiKeyringInput ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(
            Aws.Crypto.CreateMultiKeyringInput value)
        {
            Aws.Crypto.IKeyring var_generator = value.IsSetGenerator() ? value.Generator : (Aws.Crypto.IKeyring)null;
            return new Dafny.Aws.Crypto.CreateMultiKeyringInput(
                ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M13_childKeyrings(value.ChildKeyrings));
        }

        public static Aws.Crypto.PaddingScheme
            FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M13_paddingScheme(
                Dafny.Aws.Crypto._IPaddingScheme value)
        {
            return FromDafny_N3_aws__N6_crypto__S13_PaddingScheme(value);
        }

        public static Dafny.Aws.Crypto._IPaddingScheme
            ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M13_paddingScheme(Aws.Crypto.PaddingScheme value)
        {
            return ToDafny_N3_aws__N6_crypto__S13_PaddingScheme(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S12_KmsKeyIdList((System.Collections.Generic.List<string>)value));
        }

        public static Aws.Crypto.CreateAwsKmsMrkKeyringInput
            FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsMrkKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsMrkKeyringInput concrete = (Dafny.Aws.Crypto.CreateAwsKmsMrkKeyringInput)value;
            Aws.Crypto.CreateAwsKmsMrkKeyringInput converted = new Aws.Crypto.CreateAwsKmsMrkKeyringInput();
            converted.KmsKeyId =
                (string)FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(concrete.kmsKeyId);
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(concrete.kmsClient);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsMrkKeyringInput
            ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput(Aws.Crypto.CreateAwsKmsMrkKeyringInput value)
        {
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsMrkKeyringInput(
                ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M8_kmsKeyId(value.KmsKeyId),
                ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput__M11_grantTokens(var_grantTokens));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M9_publicKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M9_publicKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput
            FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput)value;
            Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput converted =
                new Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput();
            converted.Regions =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(concrete.regions);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Crypto.DiscoveryFilter)
                    FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Crypto.IClientSupplier)
                    FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryMultiKeyringInput
            ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput(
                Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput value)
        {
            Aws.Crypto.DiscoveryFilter var_discoveryFilter =
                value.IsSetDiscoveryFilter() ? value.DiscoveryFilter : (Aws.Crypto.DiscoveryFilter)null;
            Aws.Crypto.IClientSupplier var_clientSupplier =
                value.IsSetClientSupplier() ? value.ClientSupplier : (Aws.Crypto.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput(
                ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M7_regions(value.Regions),
                ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M14_clientSupplier(
                    var_clientSupplier),
                ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput__M11_grantTokens(
                    var_grantTokens));
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(
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
            ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            if (value is Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl)
            {
                return new Com.Amazonaws.Kms.KeyManagementServiceShim(impl);
            }

            throw new System.ArgumentException(
                "Custom implementations of Amazon.KeyManagementService.IAmazonKeyManagementService are not supported yet");
        }

        public static string FromDafny_N3_aws__N6_crypto__S6_Region(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S6_Region(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string
            FromDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException__M7_message(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException__M7_message(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string)null : FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_generator(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S8_KmsKeyId((string)value));
        }

        public static Aws.Crypto.AwsCryptographicMaterialProvidersClientException
            FromDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException(
                Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException value)
        {
            return new Aws.Crypto.AwsCryptographicMaterialProvidersClientException(
                FromDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException__M7_message(
                    value.message));
        }

        public static Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException
            ToDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException(
                Aws.Crypto.AwsCryptographicMaterialProvidersClientException value)
        {
            Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException converted =
                new Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException();
            converted.message =
                ToDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException__M7_message(
                    value.Message);
            return converted;
        }

        public static Aws.Crypto.EncryptedDataKey FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(
            Dafny.Aws.Crypto._IEncryptedDataKey value)
        {
            Dafny.Aws.Crypto.EncryptedDataKey concrete = (Dafny.Aws.Crypto.EncryptedDataKey)value;
            Aws.Crypto.EncryptedDataKey converted = new Aws.Crypto.EncryptedDataKey();
            converted.KeyProviderId =
                (string)FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M13_keyProviderId(concrete.keyProviderId);
            converted.KeyProviderInfo =
                (string)FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M15_keyProviderInfo(concrete
                    .keyProviderInfo);
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M10_ciphertext(
                    concrete.ciphertext);
            return converted;
        }

        public static Dafny.Aws.Crypto._IEncryptedDataKey ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(
            Aws.Crypto.EncryptedDataKey value)
        {
            return new Dafny.Aws.Crypto.EncryptedDataKey(
                ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M13_keyProviderId(value.KeyProviderId),
                ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M15_keyProviderInfo(value.KeyProviderInfo),
                ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M10_ciphertext(value.Ciphertext));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M9_generator(
            Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Crypto.IKeyring)null
                : FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring>
            ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M9_generator(Aws.Crypto.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_KeyringReference((Aws.Crypto.IKeyring)value));
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_aws__N6_crypto__S10_RegionList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S10_RegionList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N6_crypto__S10_RegionList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S10_RegionList__M6_member).ToArray());
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static Aws.Crypto.DiscoveryFilter
            FromDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter> value)
        {
            return value.is_None
                ? (Aws.Crypto.DiscoveryFilter)null
                : FromDafny_N3_aws__N6_crypto__S15_DiscoveryFilter(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IDiscoveryFilter>
            ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput__M15_discoveryFilter(
                Aws.Crypto.DiscoveryFilter value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IDiscoveryFilter>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S15_DiscoveryFilter((Aws.Crypto.DiscoveryFilter)value));
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(
            Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(
            Aws.Crypto.IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput__M7_keyring(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Aws.Crypto.AlgorithmSuiteId FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(
            Dafny.Aws.Crypto._IAlgorithmSuiteId value)
        {
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY;
            if (value.is_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384)
                return Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
            throw new System.ArgumentException("Invalid Aws.Crypto.AlgorithmSuiteId value");
        }

        public static Dafny.Aws.Crypto._IAlgorithmSuiteId ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(
            Aws.Crypto.AlgorithmSuiteId value)
        {
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY();
            if (Aws.Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384();
            throw new System.ArgumentException("Invalid Aws.Crypto.AlgorithmSuiteId value");
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(
            Dafny.Aws.Crypto._IEncryptionMaterials value)
        {
            Dafny.Aws.Crypto.EncryptionMaterials concrete = (Dafny.Aws.Crypto.EncryptionMaterials)value;
            Aws.Crypto.EncryptionMaterials converted = new Aws.Crypto.EncryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(concrete.encryptionContext);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(concrete.encryptedDataKeys);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.signingKey.is_Some)
                converted.SigningKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(
                        concrete.signingKey);
            return converted;
        }

        public static Dafny.Aws.Crypto._IEncryptionMaterials ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(
            Aws.Crypto.EncryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_signingKey =
                value.IsSetSigningKey() ? value.SigningKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Crypto.EncryptionMaterials(
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(value.EncryptedDataKeys),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(var_plaintextDataKey),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(var_signingKey));
        }

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(
                Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return new CryptographicMaterialsManager(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            if (value is CryptographicMaterialsManager valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Crypto.ICryptographicMaterialsManager are not supported yet");
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Dafny.Aws.Crypto._ICreateDefaultCryptographicMaterialsManagerInput value)
        {
            Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput concrete =
                (Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput)value;
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput converted =
                new Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput();
            converted.Keyring =
                (Aws.Crypto.IKeyring)
                FromDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateDefaultCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput value)
        {
            return new Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput(
                ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    value.Keyring));
        }

        public static Aws.Crypto.OnDecryptInput FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput(
            Dafny.Aws.Crypto._IOnDecryptInput value)
        {
            Dafny.Aws.Crypto.OnDecryptInput concrete = (Dafny.Aws.Crypto.OnDecryptInput)value;
            Aws.Crypto.OnDecryptInput converted = new Aws.Crypto.OnDecryptInput();
            converted.Materials =
                (Aws.Crypto.DecryptionMaterials)FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(
                    concrete.materials);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(concrete.encryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.Crypto._IOnDecryptInput ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput(
            Aws.Crypto.OnDecryptInput value)
        {
            return new Dafny.Aws.Crypto.OnDecryptInput(
                ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(value.Materials),
                ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(value.EncryptedDataKeys));
        }

        public static Aws.Crypto.IClientSupplier
            FromDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Crypto.IClientSupplier)null
                : FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier>
            ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput__M14_clientSupplier(
                Aws.Crypto.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S23_ClientSupplierReference((Aws.Crypto.IClientSupplier)value));
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(
            Dafny.Aws.Crypto._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IEncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M12_keyNamespace(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput
            FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput)value;
            Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput converted =
                new Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Crypto.DiscoveryFilter)
                    FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            converted.Region =
                (string)FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
                    concrete.region);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryKeyringInput
            ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput(
                Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput value)
        {
            Aws.Crypto.DiscoveryFilter var_discoveryFilter =
                value.IsSetDiscoveryFilter() ? value.DiscoveryFilter : (Aws.Crypto.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput(
                ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(var_grantTokens),
                ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(value.Region));
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N6_crypto__S11_KeyringList__M6_member(
            Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N6_crypto__S11_KeyringList__M6_member(
            Aws.Crypto.IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Aws.Crypto.CreateRawAesKeyringInput FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(
            Dafny.Aws.Crypto._ICreateRawAesKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateRawAesKeyringInput concrete = (Dafny.Aws.Crypto.CreateRawAesKeyringInput)value;
            Aws.Crypto.CreateRawAesKeyringInput converted = new Aws.Crypto.CreateRawAesKeyringInput();
            converted.KeyNamespace =
                (string)FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    concrete.keyNamespace);
            converted.KeyName =
                (string)FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(concrete.keyName);
            converted.WrappingKey =
                (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    concrete.wrappingKey);
            converted.WrappingAlg =
                (Aws.Crypto.AesWrappingAlg)FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    concrete.wrappingAlg);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateRawAesKeyringInput
            ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(Aws.Crypto.CreateRawAesKeyringInput value)
        {
            return new Dafny.Aws.Crypto.CreateRawAesKeyringInput(
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(value.KeyNamespace),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(value.WrappingKey),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(value.WrappingAlg));
        }

        public static Aws.Crypto.CreateAwsKmsMultiKeyringInput
            FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsMultiKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsMultiKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsMultiKeyringInput)value;
            Aws.Crypto.CreateAwsKmsMultiKeyringInput converted = new Aws.Crypto.CreateAwsKmsMultiKeyringInput();
            if (concrete.generator.is_Some)
                converted.Generator =
                    (string)FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_generator(
                        concrete.generator);
            if (concrete.kmsKeyIds.is_Some)
                converted.KmsKeyIds =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(concrete.kmsKeyIds);
            if (concrete.clientSupplier.is_Some)
                converted.ClientSupplier =
                    (Aws.Crypto.IClientSupplier)
                    FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                        concrete.clientSupplier);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsMultiKeyringInput
            ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput(Aws.Crypto.CreateAwsKmsMultiKeyringInput value)
        {
            string var_generator = value.IsSetGenerator() ? value.Generator : (string)null;
            System.Collections.Generic.List<string> var_kmsKeyIds =
                value.IsSetKmsKeyIds() ? value.KmsKeyIds : (System.Collections.Generic.List<string>)null;
            Aws.Crypto.IClientSupplier var_clientSupplier =
                value.IsSetClientSupplier() ? value.ClientSupplier : (Aws.Crypto.IClientSupplier)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsMultiKeyringInput(
                ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_generator(var_generator),
                ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(var_kmsKeyIds),
                ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(var_clientSupplier),
                ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M11_grantTokens(var_grantTokens));
        }

        public static long? FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static Aws.Crypto.OnDecryptOutput FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(
            Dafny.Aws.Crypto._IOnDecryptOutput value)
        {
            Dafny.Aws.Crypto.OnDecryptOutput concrete = (Dafny.Aws.Crypto.OnDecryptOutput)value;
            Aws.Crypto.OnDecryptOutput converted = new Aws.Crypto.OnDecryptOutput();
            converted.Materials =
                (Aws.Crypto.DecryptionMaterials)FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(
                    concrete.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto._IOnDecryptOutput ToDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(
            Aws.Crypto.OnDecryptOutput value)
        {
            return new Dafny.Aws.Crypto.OnDecryptOutput(
                ToDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(value.Materials));
        }

        public static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Dafny.Aws.Crypto._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto._IAlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(
                Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey> value)
        {
            return new System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto._IEncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return Dafny.Sequence<Dafny.Aws.Crypto._IEncryptedDataKey>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput__M8_kmsKeyId(
            string value)
        {
            return ToDafny_N3_aws__N6_crypto__S8_KmsKeyId(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.IClientSupplier
            FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier> value)
        {
            return value.is_None
                ? (Aws.Crypto.IClientSupplier)null
                : FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IClientSupplier>
            ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M14_clientSupplier(
                Aws.Crypto.IClientSupplier value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IClientSupplier>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S23_ClientSupplierReference((Aws.Crypto.IClientSupplier)value));
        }

        public static Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput
            FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput(
                Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryKeyringInput value)
        {
            Dafny.Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput concrete =
                (Dafny.Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput)value;
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput converted = new Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput();
            converted.KmsClient =
                (Amazon.KeyManagementService.IAmazonKeyManagementService)
                FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(concrete.kmsClient);
            if (concrete.discoveryFilter.is_Some)
                converted.DiscoveryFilter =
                    (Aws.Crypto.DiscoveryFilter)
                    FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                        concrete.discoveryFilter);
            if (concrete.grantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(
                        concrete.grantTokens);
            return converted;
        }

        public static Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryKeyringInput
            ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput(
                Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput value)
        {
            Aws.Crypto.DiscoveryFilter var_discoveryFilter =
                value.IsSetDiscoveryFilter() ? value.DiscoveryFilter : (Aws.Crypto.DiscoveryFilter)null;
            System.Collections.Generic.List<string> var_grantTokens = value.IsSetGrantTokens()
                ? value.GrantTokens
                : (System.Collections.Generic.List<string>)null;
            return new Dafny.Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput(
                ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(value.KmsClient),
                ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M15_discoveryFilter(
                    var_discoveryFilter),
                ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M11_grantTokens(var_grantTokens));
        }

        public static Aws.Crypto.DecryptionMaterials
            FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Dafny.Aws.Crypto._IDecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IDecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.IKeyring>
            FromDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M13_childKeyrings(
                Dafny.ISequence<Dafny.Aws.Crypto.IKeyring> value)
        {
            return FromDafny_N3_aws__N6_crypto__S11_KeyringList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>
            ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput__M13_childKeyrings(
                System.Collections.Generic.List<Aws.Crypto.IKeyring> value)
        {
            return ToDafny_N3_aws__N6_crypto__S11_KeyringList(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.IKeyring> FromDafny_N3_aws__N6_crypto__S11_KeyringList(
            Dafny.ISequence<Dafny.Aws.Crypto.IKeyring> value)
        {
            return new System.Collections.Generic.List<Aws.Crypto.IKeyring>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S11_KeyringList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.IKeyring> ToDafny_N3_aws__N6_crypto__S11_KeyringList(
            System.Collections.Generic.List<Aws.Crypto.IKeyring> value)
        {
            return Dafny.Sequence<Dafny.Aws.Crypto.IKeyring>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S11_KeyringList__M6_member).ToArray());
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Crypto._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto._IAlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.Crypto.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IAlgorithmSuiteId>
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Aws.Crypto.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId((Aws.Crypto.AlgorithmSuiteId)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M7_keyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M7_keyName(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S15_GetClientOutput__M6_client(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S15_GetClientOutput__M6_client(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M10_privateKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput__M10_privateKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_aws__N6_crypto__S13_AccountIdList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S13_AccountIdList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N6_crypto__S13_AccountIdList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S13_AccountIdList__M6_member).ToArray());
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S12_KmsKeyIdList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput__M9_kmsKeyIds(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S12_KmsKeyIdList((System.Collections.Generic.List<string>)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S8_KmsKeyId(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N6_crypto__S8_KmsKeyId(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Aws.Crypto.DecryptionMaterials FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(
            Dafny.Aws.Crypto._IDecryptionMaterials value)
        {
            Dafny.Aws.Crypto.DecryptionMaterials concrete = (Dafny.Aws.Crypto.DecryptionMaterials)value;
            Aws.Crypto.DecryptionMaterials converted = new Aws.Crypto.DecryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(
                    concrete.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(concrete.encryptionContext);
            if (concrete.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(
                        concrete.plaintextDataKey);
            if (concrete.verificationKey.is_Some)
                converted.VerificationKey =
                    (System.IO.MemoryStream)FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(
                        concrete.verificationKey);
            return converted;
        }

        public static Dafny.Aws.Crypto._IDecryptionMaterials ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(
            Aws.Crypto.DecryptionMaterials value)
        {
            System.IO.MemoryStream var_plaintextDataKey =
                value.IsSetPlaintextDataKey() ? value.PlaintextDataKey : (System.IO.MemoryStream)null;
            System.IO.MemoryStream var_verificationKey =
                value.IsSetVerificationKey() ? value.VerificationKey : (System.IO.MemoryStream)null;
            return new Dafny.Aws.Crypto.DecryptionMaterials(
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(var_plaintextDataKey),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(var_verificationKey));
        }

        public static Aws.Crypto.AesWrappingAlg FromDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(
            Dafny.Aws.Crypto._IAesWrappingAlg value)
        {
            if (value.is_ALG__AES128__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
            if (value.is_ALG__AES192__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
            if (value.is_ALG__AES256__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
            throw new System.ArgumentException("Invalid Aws.Crypto.AesWrappingAlg value");
        }

        public static Dafny.Aws.Crypto._IAesWrappingAlg ToDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(
            Aws.Crypto.AesWrappingAlg value)
        {
            if (Aws.Crypto.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Crypto.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
            if (Aws.Crypto.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Crypto.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
            if (Aws.Crypto.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16.Equals(value))
                return Dafny.Aws.Crypto.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
            throw new System.ArgumentException("Invalid Aws.Crypto.AesWrappingAlg value");
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M13_keyProviderId(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M13_keyProviderId(
            string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.CommitmentPolicy
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.Crypto._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.Crypto._ICommitmentPolicy
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_commitmentPolicy(
                Aws.Crypto.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(value);
        }

        public static Amazon.KeyManagementService.IAmazonKeyManagementService
            FromDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient
            ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput__M9_kmsClient(
                Amazon.KeyManagementService.IAmazonKeyManagementService value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(value);
        }

        public static Aws.Crypto.CommitmentPolicy
            FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Dafny.Aws.Crypto._ICommitmentPolicy value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(value);
        }

        public static Dafny.Aws.Crypto._ICommitmentPolicy
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_commitmentPolicy(
                Aws.Crypto.CommitmentPolicy value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(value);
        }

        public static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M6_region(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S6_Region(value);
        }

        public static Aws.Crypto.EncryptionMaterials
            FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Dafny.Aws.Crypto._IEncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto._IEncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(Dafny.ISequence<byte> value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return utf8.GetString(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(string value)
        {
            System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
            return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Crypto._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto._IAlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>)null
                : FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput__M11_grantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S14_GrantTokenList((System.Collections.Generic.List<string>)value));
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_aws__N6_crypto__S14_GrantTokenList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S14_GrantTokenList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_aws__N6_crypto__S14_GrantTokenList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S14_GrantTokenList__M6_member).ToArray());
        }

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput__M16_materialsManager(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Aws.Crypto.EncryptedDataKey FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member(
            Dafny.Aws.Crypto._IEncryptedDataKey value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(value);
        }

        public static Dafny.Aws.Crypto._IEncryptedDataKey
            ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member(Aws.Crypto.EncryptedDataKey value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(value);
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput__M7_keyring(
            Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput__M7_keyring(
            Aws.Crypto.IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Aws.Crypto.AwsCryptographicMaterialProvidersException
            FromDafny_CommonError_AwsCryptographicMaterialProvidersException(
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException value)
        {
            if (value is Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException)
                return FromDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException(
                    (Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException
            ToDafny_CommonError_AwsCryptographicMaterialProvidersException(
                Aws.Crypto.AwsCryptographicMaterialProvidersException value)
        {
            if (value is Aws.Crypto.AwsCryptographicMaterialProvidersClientException)
                return ToDafny_N3_aws__N6_crypto__S48_AwsCryptographicMaterialProvidersClientException(
                    (Aws.Crypto.AwsCryptographicMaterialProvidersClientException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
