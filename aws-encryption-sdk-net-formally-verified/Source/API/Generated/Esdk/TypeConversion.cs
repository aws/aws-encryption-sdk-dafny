// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:32:59.34431

using System.Linq;
using Aws.Crypto;

namespace Aws.Esdk
{
    internal static class TypeConversion
    {
        public static int? FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(
            Wrappers_Compile.Option<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N6_smithy__N3_api__S7_Integer(value.Extract());
        }

        public static Wrappers_Compile.Option<int> ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(
            int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(ToDafny_N6_smithy__N3_api__S7_Integer((int) value));
        }

        public static AlgorithmSuiteId FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(
            Dafny.Aws.Crypto.AlgorithmSuiteId value)
        {
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF)
                return AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF)
                return AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF)
                return AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256)
                return AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256)
                return AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256)
                return AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256;
            if (value.is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)
                return AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256;
            if (value.is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            if (value.is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)
                return AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
            throw new System.ArgumentException("Invalid AlgorithmSuiteId value");
        }

        public static Dafny.Aws.Crypto.AlgorithmSuiteId ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(
            AlgorithmSuiteId value)
        {
            if (AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
            if (AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
            if (AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
            if (AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
            if (AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
            if (AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
            if (AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
            if (AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            if (AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384.Equals(value))
                return Dafny.Aws.Crypto.AlgorithmSuiteId
                    .create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
            throw new System.ArgumentException("Invalid AlgorithmSuiteId value");
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static int FromDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }

        public static int ToDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static EncryptOutput FromDafny_N3_aws__N4_esdk__S13_EncryptOutput(Dafny.Aws.Esdk.EncryptOutput value)
        {
            return EncryptOutput.Builder()
                .WithEncryptedMessage(
                    FromDafny_N3_aws__N4_esdk__S13_EncryptOutput__M16_encryptedMessage(value.encryptedMessage)).Build();
        }

        public static Dafny.Aws.Esdk.EncryptOutput ToDafny_N3_aws__N4_esdk__S13_EncryptOutput(EncryptOutput value)
        {
            return new Dafny.Aws.Esdk.EncryptOutput(
                ToDafny_N3_aws__N4_esdk__S13_EncryptOutput__M16_encryptedMessage(value.EncryptedMessage));
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

        public static ICryptographicMaterialsManager FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(
            Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static ICryptographicMaterialsManager
            FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(
                Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return new CryptographicMaterialsManager(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(ICryptographicMaterialsManager value)
        {
            if (value is CryptographicMaterialsManager valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of ICryptographicMaterialsManager are not supported yet");
        }

        public static ICryptographicMaterialsManager FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(
            Dafny.Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static Dafny.Aws.Crypto.ICryptographicMaterialsManager
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(ICryptographicMaterialsManager value)
        {
            return ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value);
        }

        public static AlgorithmSuiteId FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(
            Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> value)
        {
            return value.is_None
                ? (AlgorithmSuiteId) null
                : FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId((AlgorithmSuiteId) value));
        }

        public static IKeyring FromDafny_N3_aws__N6_crypto__S16_KeyringReference(Dafny.Aws.Crypto.IKeyring value)
        {
            return new Keyring(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N6_crypto__S16_KeyringReference(IKeyring value)
        {
            if (value is Keyring valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            // TODO the rest of the method has been manually updated
            // throw new System.ArgumentException("Custom implementations of IKeyring are not supported yet");
            return null;
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S13_EncryptOutput__M16_encryptedMessage(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S13_EncryptOutput__M16_encryptedMessage(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_encryptedMessage(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_encryptedMessage(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static IKeyring FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static System.Collections.Generic.IDictionary<string, string>
            FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return value.ItemEnumerable.ToDictionary(
                pair => FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(pair.Car),
                pair => FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(pair.Cdr));
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
        {
            return Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromCollection(value.Select(pair =>
                new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(
                    ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(pair.Key),
                    ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(pair.Value))
            ));
        }

        public static DecryptInput FromDafny_N3_aws__N4_esdk__S12_DecryptInput(Dafny.Aws.Esdk.DecryptInput value)
        {
            return DecryptInput.Builder()
                .WithEncryptedMessage(
                    FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_encryptedMessage(value.encryptedMessage))
                .WithMaterialsManager(
                    FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(value.materialsManager))
                .WithKeyring(FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(value.keyring)).Build();
        }

        public static Dafny.Aws.Esdk.DecryptInput ToDafny_N3_aws__N4_esdk__S12_DecryptInput(DecryptInput value)
        {
            return new Dafny.Aws.Esdk.DecryptInput(
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_encryptedMessage(value.EncryptedMessage),
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(value.MaterialsManager),
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(value.Keyring));
        }

        public static IKeyring FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(Dafny.Aws.Crypto.IKeyring value)
        {
            return FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static Dafny.Aws.Crypto.IKeyring ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(IKeyring value)
        {
            return ToDafny_N3_aws__N6_crypto__S16_KeyringReference(value);
        }

        public static DecryptOutput FromDafny_N3_aws__N4_esdk__S13_DecryptOutput(Dafny.Aws.Esdk.DecryptOutput value)
        {
            return DecryptOutput.Builder()
                .WithPlaintext(FromDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(value.plaintext)).Build();
        }

        public static Dafny.Aws.Esdk.DecryptOutput ToDafny_N3_aws__N4_esdk__S13_DecryptOutput(DecryptOutput value)
        {
            return new Dafny.Aws.Esdk.DecryptOutput(
                ToDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(value.Plaintext));
        }

        public static EncryptInput FromDafny_N3_aws__N4_esdk__S12_EncryptInput(Dafny.Aws.Esdk.EncryptInput value)
        {
            return EncryptInput.Builder()
                .WithPlaintext(FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(value.plaintext))
                .WithEncryptionContext(
                    FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(value.encryptionContext))
                .WithMaterialsManager(
                    FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(value.materialsManager))
                .WithKeyring(FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(value.keyring))
                .WithAlgorithmSuiteId(
                    FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(value.algorithmSuiteId))
                .WithFrameLength(FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(value.frameLength))
                .Build();
        }

        public static Dafny.Aws.Esdk.EncryptInput ToDafny_N3_aws__N4_esdk__S12_EncryptInput(EncryptInput value)
        {
            return new Dafny.Aws.Esdk.EncryptInput(
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(value.MaterialsManager),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(value.Keyring),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(value.FrameLength));
        }

        public static System.Collections.Generic.IDictionary<string, string>
            FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
        {
            return ToDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }
    }
}