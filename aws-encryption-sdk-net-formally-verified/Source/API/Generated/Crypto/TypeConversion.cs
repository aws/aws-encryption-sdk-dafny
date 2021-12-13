// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Crypto;

namespace Aws.Crypto
{
    internal static class TypeConversion
    {
        public static Aws.Crypto.PutEntryForEncryptInput FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput(
            Dafny.Aws.Crypto.PutEntryForEncryptInput value)
        {
            Aws.Crypto.PutEntryForEncryptInput converted = new Aws.Crypto.PutEntryForEncryptInput();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M10_identifier(
                    value.identifier);
            converted.EncryptionMaterials =
                (Aws.Crypto.EncryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M19_encryptionMaterials(
                    value.encryptionMaterials);
            converted.UsageMetadata =
                (Aws.Crypto.CacheUsageMetadata)
                FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M13_usageMetadata(value.usageMetadata);
            return converted;
        }

        public static Dafny.Aws.Crypto.PutEntryForEncryptInput ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput(
            Aws.Crypto.PutEntryForEncryptInput value)
        {
            return new Dafny.Aws.Crypto.PutEntryForEncryptInput(
                ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M10_identifier(value.Identifier),
                ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M19_encryptionMaterials(
                    value.EncryptionMaterials),
                ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M13_usageMetadata(value.UsageMetadata));
        }

        public static Aws.Crypto.PutEntryForEncryptOutput FromDafny_N3_aws__N6_crypto__S24_PutEntryForEncryptOutput(
            Dafny.Aws.Crypto.PutEntryForEncryptOutput value)
        {
            Aws.Crypto.PutEntryForEncryptOutput converted = new Aws.Crypto.PutEntryForEncryptOutput();
            return converted;
        }

        public static Dafny.Aws.Crypto.PutEntryForEncryptOutput ToDafny_N3_aws__N6_crypto__S24_PutEntryForEncryptOutput(
            Aws.Crypto.PutEntryForEncryptOutput value)
        {
            return new Dafny.Aws.Crypto.PutEntryForEncryptOutput();
        }

        public static Aws.Crypto.CacheUsageMetadata
            FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M13_usageMetadata(
                Dafny.Aws.Crypto.CacheUsageMetadata value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Dafny.Aws.Crypto.CacheUsageMetadata
            ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M13_usageMetadata(
                Aws.Crypto.CacheUsageMetadata value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Aws.Crypto.CreateLocalCryptoMaterialsCacheInput
            FromDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput(
                Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput value)
        {
            Aws.Crypto.CreateLocalCryptoMaterialsCacheInput converted =
                new Aws.Crypto.CreateLocalCryptoMaterialsCacheInput();
            converted.EntryCapacity =
                (int) FromDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M13_entryCapacity(
                    value.entryCapacity);
            if (value.entryPruningTailSize.is_Some)
                converted.EntryPruningTailSize =
                    (int)
                    FromDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M20_entryPruningTailSize(
                        value.entryPruningTailSize);
            return converted;
        }

        public static Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput
            ToDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput(
                Aws.Crypto.CreateLocalCryptoMaterialsCacheInput value)
        {
            return new Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput(
                ToDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M13_entryCapacity(
                    value.EntryCapacity),
                ToDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M20_entryPruningTailSize(
                    value.EntryPruningTailSize));
        }

        public static int?
            FromDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M20_entryPruningTailSize(
                Wrappers_Compile.Option<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N6_smithy__N3_api__S7_Integer(value.Extract());
        }

        public static Wrappers_Compile.Option<int>
            ToDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M20_entryPruningTailSize(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(ToDafny_N6_smithy__N3_api__S7_Integer((int) value));
        }

        public static Aws.Crypto.GetEncryptionMaterialsInput
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(
                Dafny.Aws.Crypto.GetEncryptionMaterialsInput value)
        {
            Aws.Crypto.GetEncryptionMaterialsInput converted = new Aws.Crypto.GetEncryptionMaterialsInput();
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    value.encryptionContext);
            if (value.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.Crypto.AlgorithmSuiteId)
                    FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                        value.algorithmSuiteId);
            if (value.maxPlaintextLength.is_Some)
                converted.MaxPlaintextLength =
                    (long) FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                        value.maxPlaintextLength);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEncryptionMaterialsInput
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(Aws.Crypto.GetEncryptionMaterialsInput value)
        {
            return new Dafny.Aws.Crypto.GetEncryptionMaterialsInput(
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M17_encryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                    value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
                    value.MaxPlaintextLength));
        }

        public static Aws.Crypto.GetEncryptionMaterialsOutput
            FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(
                Dafny.Aws.Crypto.GetEncryptionMaterialsOutput value)
        {
            Aws.Crypto.GetEncryptionMaterialsOutput converted = new Aws.Crypto.GetEncryptionMaterialsOutput();
            converted.EncryptionMaterials =
                (Aws.Crypto.EncryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    value.encryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEncryptionMaterialsOutput
            ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(Aws.Crypto.GetEncryptionMaterialsOutput value)
        {
            return new Dafny.Aws.Crypto.GetEncryptionMaterialsOutput(
                ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                    value.EncryptionMaterials));
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

        public static Aws.Crypto.EncryptEntry FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput__M10_cacheEntry(
            Dafny.Aws.Crypto.EncryptEntry value)
        {
            return FromDafny_N3_aws__N6_crypto__S12_EncryptEntry(value);
        }

        public static Dafny.Aws.Crypto.EncryptEntry
            ToDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput__M10_cacheEntry(Aws.Crypto.EncryptEntry value)
        {
            return ToDafny_N3_aws__N6_crypto__S12_EncryptEntry(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Crypto.DecryptionMaterials FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(
            Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials ToDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(
            Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
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

        public static Aws.Crypto.ICryptoMaterialsCache
            FromDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput(
                Dafny.Aws.Crypto.ICryptoMaterialsCache value)
        {
            return FromDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput__M5_cache(value);
        }

        public static Dafny.Aws.Crypto.ICryptoMaterialsCache
            ToDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput(Aws.Crypto.ICryptoMaterialsCache value)
        {
            return ToDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput__M5_cache(value);
        }

        public static Aws.Crypto.DeleteEntryInput FromDafny_N3_aws__N6_crypto__S16_DeleteEntryInput(
            Dafny.Aws.Crypto.DeleteEntryInput value)
        {
            Aws.Crypto.DeleteEntryInput converted = new Aws.Crypto.DeleteEntryInput();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S16_DeleteEntryInput__M10_identifier(
                    value.identifier);
            return converted;
        }

        public static Dafny.Aws.Crypto.DeleteEntryInput ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput(
            Aws.Crypto.DeleteEntryInput value)
        {
            return new Dafny.Aws.Crypto.DeleteEntryInput(
                ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput__M10_identifier(value.Identifier));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
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
            Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(
            Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Aws.Crypto.ICryptoMaterialsCache
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M5_cache(
                Dafny.Aws.Crypto.ICryptoMaterialsCache value)
        {
            return FromDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptoMaterialsCache
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M5_cache(
                Aws.Crypto.ICryptoMaterialsCache value)
        {
            return ToDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(value);
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
            Dafny.Aws.Crypto.OnEncryptOutput value)
        {
            Aws.Crypto.OnEncryptOutput converted = new Aws.Crypto.OnEncryptOutput();
            converted.Materials =
                (Aws.Crypto.EncryptionMaterials) FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(
                    value.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto.OnEncryptOutput ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput(
            Aws.Crypto.OnEncryptOutput value)
        {
            return new Dafny.Aws.Crypto.OnEncryptOutput(
                ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(value.Materials));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Crypto.DecryptMaterialsInput FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(
            Dafny.Aws.Crypto.DecryptMaterialsInput value)
        {
            Aws.Crypto.DecryptMaterialsInput converted = new Aws.Crypto.DecryptMaterialsInput();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(value.algorithmSuiteId);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(value.encryptedDataKeys);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(value.encryptionContext);
            return converted;
        }

        public static Dafny.Aws.Crypto.DecryptMaterialsInput ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(
            Aws.Crypto.DecryptMaterialsInput value)
        {
            return new Dafny.Aws.Crypto.DecryptMaterialsInput(
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(value.EncryptedDataKeys),
                ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptionContext(value.EncryptionContext));
        }

        public static Aws.Crypto.CacheUsageMetadata FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M13_usageMetadata(
            Dafny.Aws.Crypto.CacheUsageMetadata value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Dafny.Aws.Crypto.CacheUsageMetadata
            ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M13_usageMetadata(Aws.Crypto.CacheUsageMetadata value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M16_materialsManager(
                Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M16_materialsManager(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Aws.Crypto.DecryptMaterialsOutput FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(
            Dafny.Aws.Crypto.DecryptMaterialsOutput value)
        {
            Aws.Crypto.DecryptMaterialsOutput converted = new Aws.Crypto.DecryptMaterialsOutput();
            converted.DecryptionMaterials =
                (Aws.Crypto.DecryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                    value.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Crypto.DecryptMaterialsOutput ToDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(
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

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Crypto.AesWrappingAlg
            FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                Dafny.Aws.Crypto.AesWrappingAlg value)
        {
            return FromDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(value);
        }

        public static Dafny.Aws.Crypto.AesWrappingAlg
            ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(Aws.Crypto.AesWrappingAlg value)
        {
            return ToDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(value);
        }

        public static long FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_expiryTime(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_expiryTime(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static Aws.Crypto.IKeyring
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M7_keyring(
                Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M7_keyring(
                Aws.Crypto.IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Aws.Crypto.GetEntryForEncryptInput FromDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput(
            Dafny.Aws.Crypto.GetEntryForEncryptInput value)
        {
            Aws.Crypto.GetEntryForEncryptInput converted = new Aws.Crypto.GetEntryForEncryptInput();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput__M10_identifier(
                    value.identifier);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEntryForEncryptInput ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput(
            Aws.Crypto.GetEntryForEncryptInput value)
        {
            return new Dafny.Aws.Crypto.GetEntryForEncryptInput(
                ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput__M10_identifier(value.Identifier));
        }

        public static Aws.Crypto.ICryptoMaterialsCache
            FromDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput__M5_cache(
                Dafny.Aws.Crypto.ICryptoMaterialsCache value)
        {
            return FromDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptoMaterialsCache
            ToDafny_N3_aws__N6_crypto__S37_CreateLocalCryptoMaterialsCacheOutput__M5_cache(
                Aws.Crypto.ICryptoMaterialsCache value)
        {
            return ToDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static int FromDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M13_entryCapacity(
            int value)
        {
            return FromDafny_N6_smithy__N3_api__S7_Integer(value);
        }

        public static int ToDafny_N3_aws__N6_crypto__S36_CreateLocalCryptoMaterialsCacheInput__M13_entryCapacity(
            int value)
        {
            return ToDafny_N6_smithy__N3_api__S7_Integer(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.GetEntryForDecryptInput FromDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput(
            Dafny.Aws.Crypto.GetEntryForDecryptInput value)
        {
            Aws.Crypto.GetEntryForDecryptInput converted = new Aws.Crypto.GetEntryForDecryptInput();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput__M10_identifier(
                    value.identifier);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEntryForDecryptInput ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput(
            Aws.Crypto.GetEntryForDecryptInput value)
        {
            return new Dafny.Aws.Crypto.GetEntryForDecryptInput(
                ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput__M10_identifier(value.Identifier));
        }

        public static Aws.Crypto.GetEntryForEncryptOutput FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput(
            Dafny.Aws.Crypto.GetEntryForEncryptOutput value)
        {
            Aws.Crypto.GetEntryForEncryptOutput converted = new Aws.Crypto.GetEntryForEncryptOutput();
            converted.CacheEntry =
                (Aws.Crypto.EncryptEntry) FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput__M10_cacheEntry(
                    value.cacheEntry);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEntryForEncryptOutput ToDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput(
            Aws.Crypto.GetEntryForEncryptOutput value)
        {
            return new Dafny.Aws.Crypto.GetEntryForEncryptOutput(
                ToDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput__M10_cacheEntry(value.CacheEntry));
        }

        public static Aws.Crypto.OnEncryptInput FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput(
            Dafny.Aws.Crypto.OnEncryptInput value)
        {
            Aws.Crypto.OnEncryptInput converted = new Aws.Crypto.OnEncryptInput();
            converted.Materials =
                (Aws.Crypto.EncryptionMaterials) FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(
                    value.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto.OnEncryptInput ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput(
            Aws.Crypto.OnEncryptInput value)
        {
            return new Dafny.Aws.Crypto.OnEncryptInput(
                ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(value.Materials));
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(
            Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput__M9_materials(
            Aws.Crypto.EncryptionMaterials value)
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

        public static Aws.Crypto.GetEntryForDecryptOutput FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput(
            Dafny.Aws.Crypto.GetEntryForDecryptOutput value)
        {
            Aws.Crypto.GetEntryForDecryptOutput converted = new Aws.Crypto.GetEntryForDecryptOutput();
            converted.CacheEntry =
                (Aws.Crypto.DecryptEntry) FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput__M10_cacheEntry(
                    value.cacheEntry);
            return converted;
        }

        public static Dafny.Aws.Crypto.GetEntryForDecryptOutput ToDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput(
            Aws.Crypto.GetEntryForDecryptOutput value)
        {
            return new Dafny.Aws.Crypto.GetEntryForDecryptOutput(
                ToDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput__M10_cacheEntry(value.CacheEntry));
        }

        public static Aws.Crypto.CacheUsageMetadata FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(
            Dafny.Aws.Crypto.CacheUsageMetadata value)
        {
            Aws.Crypto.CacheUsageMetadata converted = new Aws.Crypto.CacheUsageMetadata();
            converted.MessageUsage =
                (long) FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M12_messageUsage(value.messageUsage);
            converted.ByteUsage =
                (long) FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M9_byteUsage(value.byteUsage);
            return converted;
        }

        public static Dafny.Aws.Crypto.CacheUsageMetadata ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(
            Aws.Crypto.CacheUsageMetadata value)
        {
            return new Dafny.Aws.Crypto.CacheUsageMetadata(
                ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M12_messageUsage(value.MessageUsage),
                ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M9_byteUsage(value.ByteUsage));
        }

        public static Aws.Crypto.CacheUsageMetadata FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M13_usageMetadata(
            Dafny.Aws.Crypto.CacheUsageMetadata value)
        {
            return FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Dafny.Aws.Crypto.CacheUsageMetadata
            ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M13_usageMetadata(Aws.Crypto.CacheUsageMetadata value)
        {
            return ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata(value);
        }

        public static Aws.Crypto.DecryptionMaterials
            FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M19_decryptionMaterials(
                Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M19_decryptionMaterials(Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Aws.Crypto.EncryptionMaterials
            FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M19_encryptionMaterials(
                Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M19_encryptionMaterials(
                Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static string
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M11_partitionId(
                Wrappers_Compile.Option<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.ISequence<char>>
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M11_partitionId(
                string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S6_String((string) value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S16_DeleteEntryInput__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Crypto.EncryptedDataKey FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(
            Dafny.Aws.Crypto.EncryptedDataKey value)
        {
            Aws.Crypto.EncryptedDataKey converted = new Aws.Crypto.EncryptedDataKey();
            converted.KeyProviderId =
                (string) FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M13_keyProviderId(value.keyProviderId);
            converted.KeyProviderInfo =
                (string) FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M15_keyProviderInfo(value.keyProviderInfo);
            converted.Ciphertext =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey__M10_ciphertext(
                    value.ciphertext);
            return converted;
        }

        public static Dafny.Aws.Crypto.EncryptedDataKey ToDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(
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
            Dafny.Aws.Crypto.AlgorithmSuiteId value)
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
            throw new System.ArgumentException("Invalid Aws.Crypto.AlgorithmSuiteId value");
        }

        public static Dafny.Aws.Crypto.AlgorithmSuiteId ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(
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
            throw new System.ArgumentException("Invalid Aws.Crypto.AlgorithmSuiteId value");
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(
            Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            Aws.Crypto.EncryptionMaterials converted = new Aws.Crypto.EncryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)
                FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(value.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(value.encryptionContext);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(value.encryptedDataKeys);
            if (value.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(
                        value.plaintextDataKey);
            if (value.signingKey.is_Some)
                converted.SigningKey =
                    (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(
                        value.signingKey);
            return converted;
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(
            Aws.Crypto.EncryptionMaterials value)
        {
            return new Dafny.Aws.Crypto.EncryptionMaterials(
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M17_encryptedDataKeys(value.EncryptedDataKeys),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(value.PlaintextDataKey),
                ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(value.SigningKey));
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

        public static Aws.Crypto.PutEntryForDecryptOutput FromDafny_N3_aws__N6_crypto__S24_PutEntryForDecryptOutput(
            Dafny.Aws.Crypto.PutEntryForDecryptOutput value)
        {
            Aws.Crypto.PutEntryForDecryptOutput converted = new Aws.Crypto.PutEntryForDecryptOutput();
            return converted;
        }

        public static Dafny.Aws.Crypto.PutEntryForDecryptOutput ToDafny_N3_aws__N6_crypto__S24_PutEntryForDecryptOutput(
            Aws.Crypto.PutEntryForDecryptOutput value)
        {
            return new Dafny.Aws.Crypto.PutEntryForDecryptOutput();
        }

        public static Aws.Crypto.DeleteEntryOutput FromDafny_N3_aws__N6_crypto__S17_DeleteEntryOutput(
            Dafny.Aws.Crypto.DeleteEntryOutput value)
        {
            Aws.Crypto.DeleteEntryOutput converted = new Aws.Crypto.DeleteEntryOutput();
            return converted;
        }

        public static Dafny.Aws.Crypto.DeleteEntryOutput ToDafny_N3_aws__N6_crypto__S17_DeleteEntryOutput(
            Aws.Crypto.DeleteEntryOutput value)
        {
            return new Dafny.Aws.Crypto.DeleteEntryOutput();
        }

        public static int
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_cacheLimitTtl(
                int value)
        {
            return FromDafny_N6_smithy__N3_api__S7_Integer(value);
        }

        public static int
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_cacheLimitTtl(int value)
        {
            return ToDafny_N6_smithy__N3_api__S7_Integer(value);
        }

        public static Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput value)
        {
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput converted =
                new Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput();
            converted.Keyring =
                (Aws.Crypto.IKeyring)
                FromDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    value.keyring);
            return converted;
        }

        public static Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(
                Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput value)
        {
            return new Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput(
                ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput__M7_keyring(
                    value.Keyring));
        }

        public static long?
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M10_limitBytes(
                Wrappers_Compile.Option<long> value)
        {
            return value.is_None ? (long?) null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile.Option<long>
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M10_limitBytes(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long) value));
        }

        public static Aws.Crypto.OnDecryptInput FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput(
            Dafny.Aws.Crypto.OnDecryptInput value)
        {
            Aws.Crypto.OnDecryptInput converted = new Aws.Crypto.OnDecryptInput();
            converted.Materials =
                (Aws.Crypto.DecryptionMaterials) FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(
                    value.materials);
            converted.EncryptedDataKeys =
                (System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>)
                FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(value.encryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.Crypto.OnDecryptInput ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput(
            Aws.Crypto.OnDecryptInput value)
        {
            return new Dafny.Aws.Crypto.OnDecryptInput(
                ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M9_materials(value.Materials),
                ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(value.EncryptedDataKeys));
        }

        public static Aws.Crypto.EncryptionMaterials
            FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M19_encryptionMaterials(
                Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M19_encryptionMaterials(Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Aws.Crypto.EncryptionMaterials FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(
            Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials ToDafny_N3_aws__N6_crypto__S15_OnEncryptOutput__M9_materials(
            Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(
                Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput__M17_encryptedDataKeys(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static long FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M12_creationTime(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M12_creationTime(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static Aws.Crypto.CreateRawAesKeyringInput FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(
            Dafny.Aws.Crypto.CreateRawAesKeyringInput value)
        {
            Aws.Crypto.CreateRawAesKeyringInput converted = new Aws.Crypto.CreateRawAesKeyringInput();
            converted.KeyNamespace =
                (string) FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(
                    value.keyNamespace);
            converted.KeyName =
                (string) FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(value.keyName);
            converted.WrappingKey =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(
                    value.wrappingKey);
            converted.WrappingAlg =
                (Aws.Crypto.AesWrappingAlg) FromDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(
                    value.wrappingAlg);
            return converted;
        }

        public static Dafny.Aws.Crypto.CreateRawAesKeyringInput ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(
            Aws.Crypto.CreateRawAesKeyringInput value)
        {
            return new Dafny.Aws.Crypto.CreateRawAesKeyringInput(
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M12_keyNamespace(value.KeyNamespace),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M7_keyName(value.KeyName),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingKey(value.WrappingKey),
                ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput__M11_wrappingAlg(value.WrappingAlg));
        }

        public static long? FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(
            Wrappers_Compile.Option<long> value)
        {
            return value.is_None ? (long?) null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile.Option<long>
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M18_maxPlaintextLength(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long) value));
        }

        public static Aws.Crypto.OnDecryptOutput FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(
            Dafny.Aws.Crypto.OnDecryptOutput value)
        {
            Aws.Crypto.OnDecryptOutput converted = new Aws.Crypto.OnDecryptOutput();
            converted.Materials =
                (Aws.Crypto.DecryptionMaterials) FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput__M9_materials(
                    value.materials);
            return converted;
        }

        public static Dafny.Aws.Crypto.OnDecryptOutput ToDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(
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
                Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> value)
        {
            return FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(value);
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey>
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
                Dafny.Aws.Crypto.AlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto.AlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput__M16_algorithmSuiteId(
                Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Aws.Crypto.DecryptionMaterials
            FromDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M19_decryptionMaterials(
                Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M19_decryptionMaterials(
                Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>
            FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(
                Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> value)
        {
            return new System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey>(
                value.Elements.Select(FromDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey>
            ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList(
                System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> value)
        {
            return Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromArray(value
                .Select(ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member).ToArray());
        }

        public static long FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M12_messageUsage(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M12_messageUsage(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static Aws.Crypto.DecryptEntry FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput__M10_cacheEntry(
            Dafny.Aws.Crypto.DecryptEntry value)
        {
            return FromDafny_N3_aws__N6_crypto__S12_DecryptEntry(value);
        }

        public static Dafny.Aws.Crypto.DecryptEntry
            ToDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput__M10_cacheEntry(Aws.Crypto.DecryptEntry value)
        {
            return ToDafny_N3_aws__N6_crypto__S12_DecryptEntry(value);
        }

        public static Aws.Crypto.DecryptEntry FromDafny_N3_aws__N6_crypto__S12_DecryptEntry(
            Dafny.Aws.Crypto.DecryptEntry value)
        {
            Aws.Crypto.DecryptEntry converted = new Aws.Crypto.DecryptEntry();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_identifier(
                    value.identifier);
            converted.DecryptionMaterials =
                (Aws.Crypto.DecryptionMaterials) FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M19_decryptionMaterials(
                    value.decryptionMaterials);
            converted.CreationTime =
                (long) FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M12_creationTime(value.creationTime);
            converted.ExpiryTime =
                (long) FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_expiryTime(value.expiryTime);
            converted.UsageMetadata =
                (Aws.Crypto.CacheUsageMetadata) FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M13_usageMetadata(
                    value.usageMetadata);
            return converted;
        }

        public static Dafny.Aws.Crypto.DecryptEntry ToDafny_N3_aws__N6_crypto__S12_DecryptEntry(
            Aws.Crypto.DecryptEntry value)
        {
            return new Dafny.Aws.Crypto.DecryptEntry(
                ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_identifier(value.Identifier),
                ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M19_decryptionMaterials(value.DecryptionMaterials),
                ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M12_creationTime(value.CreationTime),
                ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_expiryTime(value.ExpiryTime),
                ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M13_usageMetadata(value.UsageMetadata));
        }

        public static long?
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_limitMessages(
                Wrappers_Compile.Option<long> value)
        {
            return value.is_None ? (long?) null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile.Option<long>
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_limitMessages(
                long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long) value));
        }

        public static Aws.Crypto.ICryptoMaterialsCache FromDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(
            Dafny.Aws.Crypto.ICryptoMaterialsCache value)
        {
            return new CryptoMaterialsCache(value);
        }

        public static Dafny.Aws.Crypto.ICryptoMaterialsCache
            ToDafny_N3_aws__N6_crypto__S29_CryptoMaterialsCacheReference(Aws.Crypto.ICryptoMaterialsCache value)
        {
            if (value is CryptoMaterialsCache valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Crypto.ICryptoMaterialsCache are not supported yet");
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
            Wrappers_Compile.Option<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_plaintextDataKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static long FromDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M9_byteUsage(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S18_CacheUsageMetadata__M9_byteUsage(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M12_creationTime(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M12_creationTime(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static Aws.Crypto.DecryptionMaterials
            FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials
            ToDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput__M19_decryptionMaterials(
                Aws.Crypto.DecryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(
            Wrappers_Compile.Option<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Crypto.AlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto.AlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M16_algorithmSuiteId(Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.Crypto.AlgorithmSuiteId) null
                : FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>
            ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput__M16_algorithmSuiteId(
                Aws.Crypto.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId((Aws.Crypto.AlgorithmSuiteId) value));
        }

        public static Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput
            FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput(
                Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput value)
        {
            Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput converted =
                new Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput();
            converted.Cache =
                (Aws.Crypto.ICryptoMaterialsCache)
                FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M5_cache(value.cache);
            converted.CacheLimitTtl =
                (int)
                FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_cacheLimitTtl(
                    value.cacheLimitTtl);
            if (value.keyring != null)
                converted.Keyring =
                    (Aws.Crypto.IKeyring)
                    FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M7_keyring(
                        value.keyring);
            if (value.materialsManager != null)
                converted.MaterialsManager =
                    (Aws.Crypto.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M16_materialsManager(
                        value.materialsManager);
            if (value.partitionId.is_Some)
                converted.PartitionId =
                    (string)
                    FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M11_partitionId(
                        value.partitionId);
            if (value.limitBytes.is_Some)
                converted.LimitBytes =
                    (long)
                    FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M10_limitBytes(
                        value.limitBytes);
            if (value.limitMessages.is_Some)
                converted.LimitMessages =
                    (long)
                    FromDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_limitMessages(
                        value.limitMessages);
            return converted;
        }

        public static Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput
            ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput(
                Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput value)
        {
            return new Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput(
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M5_cache(value.Cache),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_cacheLimitTtl(
                    value.CacheLimitTtl),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M7_keyring(
                    value.Keyring),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M16_materialsManager(
                    value.MaterialsManager),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M11_partitionId(
                    value.PartitionId),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M10_limitBytes(
                    value.LimitBytes),
                ToDafny_N3_aws__N6_crypto__S47_CreateCachingCryptographicMaterialsManagerInput__M13_limitMessages(
                    value.LimitMessages));
        }

        public static Aws.Crypto.PutEntryForDecryptInput FromDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput(
            Dafny.Aws.Crypto.PutEntryForDecryptInput value)
        {
            Aws.Crypto.PutEntryForDecryptInput converted = new Aws.Crypto.PutEntryForDecryptInput();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M10_identifier(
                    value.identifier);
            converted.DecryptionMaterials =
                (Aws.Crypto.DecryptionMaterials)
                FromDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M19_decryptionMaterials(
                    value.decryptionMaterials);
            return converted;
        }

        public static Dafny.Aws.Crypto.PutEntryForDecryptInput ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput(
            Aws.Crypto.PutEntryForDecryptInput value)
        {
            return new Dafny.Aws.Crypto.PutEntryForDecryptInput(
                ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M10_identifier(value.Identifier),
                ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput__M19_decryptionMaterials(
                    value.DecryptionMaterials));
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

        public static Aws.Crypto.DecryptionMaterials FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(
            Dafny.Aws.Crypto.DecryptionMaterials value)
        {
            Aws.Crypto.DecryptionMaterials converted = new Aws.Crypto.DecryptionMaterials();
            converted.AlgorithmSuiteId =
                (Aws.Crypto.AlgorithmSuiteId)
                FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(value.algorithmSuiteId);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(value.encryptionContext);
            if (value.plaintextDataKey.is_Some)
                converted.PlaintextDataKey =
                    (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(
                        value.plaintextDataKey);
            if (value.verificationKey.is_Some)
                converted.VerificationKey =
                    (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(
                        value.verificationKey);
            return converted;
        }

        public static Dafny.Aws.Crypto.DecryptionMaterials ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials(
            Aws.Crypto.DecryptionMaterials value)
        {
            return new Dafny.Aws.Crypto.DecryptionMaterials(
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(value.PlaintextDataKey),
                ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M15_verificationKey(value.VerificationKey));
        }

        public static Aws.Crypto.AesWrappingAlg FromDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(
            Dafny.Aws.Crypto.AesWrappingAlg value)
        {
            if (value.is_ALG__AES128__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
            if (value.is_ALG__AES192__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
            if (value.is_ALG__AES256__GCM__IV12__TAG16) return Aws.Crypto.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
            throw new System.ArgumentException("Invalid Aws.Crypto.AesWrappingAlg value");
        }

        public static Dafny.Aws.Crypto.AesWrappingAlg ToDafny_N3_aws__N6_crypto__S14_AesWrappingAlg(
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

        public static int FromDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }

        public static int ToDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }

        public static Aws.Crypto.EncryptionMaterials
            FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Dafny.Aws.Crypto.EncryptionMaterials value)
        {
            return FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static Dafny.Aws.Crypto.EncryptionMaterials
            ToDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput__M19_encryptionMaterials(
                Aws.Crypto.EncryptionMaterials value)
        {
            return ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials(value);
        }

        public static long FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_expiryTime(long value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Long(value);
        }

        public static long ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_expiryTime(long value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Long(value);
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
            Wrappers_Compile.Option<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_plaintextDataKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
        }

        public static Aws.Crypto.AlgorithmSuiteId
            FromDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(
                Dafny.Aws.Crypto.AlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Crypto.AlgorithmSuiteId
            ToDafny_N3_aws__N6_crypto__S19_DecryptionMaterials__M16_algorithmSuiteId(Aws.Crypto.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(
            Wrappers_Compile.Option<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S19_EncryptionMaterials__M10_signingKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
        }

        public static Aws.Crypto.EncryptEntry FromDafny_N3_aws__N6_crypto__S12_EncryptEntry(
            Dafny.Aws.Crypto.EncryptEntry value)
        {
            Aws.Crypto.EncryptEntry converted = new Aws.Crypto.EncryptEntry();
            converted.Identifier =
                (System.IO.MemoryStream) FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_identifier(
                    value.identifier);
            converted.EncryptionMaterials =
                (Aws.Crypto.EncryptionMaterials) FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M19_encryptionMaterials(
                    value.encryptionMaterials);
            converted.CreationTime =
                (long) FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M12_creationTime(value.creationTime);
            converted.ExpiryTime =
                (long) FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_expiryTime(value.expiryTime);
            converted.UsageMetadata =
                (Aws.Crypto.CacheUsageMetadata) FromDafny_N3_aws__N6_crypto__S12_EncryptEntry__M13_usageMetadata(
                    value.usageMetadata);
            return converted;
        }

        public static Dafny.Aws.Crypto.EncryptEntry ToDafny_N3_aws__N6_crypto__S12_EncryptEntry(
            Aws.Crypto.EncryptEntry value)
        {
            return new Dafny.Aws.Crypto.EncryptEntry(
                ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_identifier(value.Identifier),
                ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M19_encryptionMaterials(value.EncryptionMaterials),
                ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M12_creationTime(value.CreationTime),
                ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M10_expiryTime(value.ExpiryTime),
                ToDafny_N3_aws__N6_crypto__S12_EncryptEntry__M13_usageMetadata(value.UsageMetadata));
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
            Dafny.Aws.Crypto.EncryptedDataKey value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_EncryptedDataKey(value);
        }

        public static Dafny.Aws.Crypto.EncryptedDataKey ToDafny_N3_aws__N6_crypto__S20_EncryptedDataKeyList__M6_member(
            Aws.Crypto.EncryptedDataKey value)
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

        public static System.IO.MemoryStream FromDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_identifier(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S12_DecryptEntry__M10_identifier(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }
    }
}