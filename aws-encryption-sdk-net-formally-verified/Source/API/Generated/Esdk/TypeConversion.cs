// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.EncryptionSdk.Core;

namespace Aws.EncryptionSdk
{
    internal static class TypeConversion
    {
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

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Aws.EncryptionSdk.EncryptOutput FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput(
            Dafny.Aws.EncryptionSdk._IEncryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.EncryptOutput concrete = (Dafny.Aws.EncryptionSdk.EncryptOutput)value;
            Aws.EncryptionSdk.EncryptOutput converted = new Aws.EncryptionSdk.EncryptOutput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M10_ciphertext(
                    concrete.ciphertext);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.AlgorithmSuiteId =
                (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk._IEncryptOutput ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput(
            Aws.EncryptionSdk.EncryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.EncryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M10_ciphertext(value.Ciphertext),
                ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M16_algorithmSuiteId(value.AlgorithmSuiteId));
        }

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M16_algorithmSuiteId(
                Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                    value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_materialsManager(
                Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                        (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)value));
        }

        public static Aws.EncryptionSdk.IAwsEncryptionSdk
            FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkReference(
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk value)
        {
            return new AwsEncryptionSdk(value);
        }

        public static Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk
            ToDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkReference(Aws.EncryptionSdk.IAwsEncryptionSdk value)
        {
            if (value is AwsEncryptionSdk valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.EncryptionSdk.IAwsEncryptionSdk are not supported yet");
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
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

        public static Aws.EncryptionSdk.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>
            ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_algorithmSuiteId(
                Aws.EncryptionSdk.Core.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_AlgorithmSuiteId(
                        (Aws.EncryptionSdk.Core.AlgorithmSuiteId)value));
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

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Aws.EncryptionSdk.AwsEncryptionSdkException
            FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException(
                Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException value)
        {
            return new Aws.EncryptionSdk.AwsEncryptionSdkException(
                FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException__M7_message(value.message));
        }

        public static Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException
            ToDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException(
                Aws.EncryptionSdk.AwsEncryptionSdkException value)
        {
            Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException converted =
                new Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException();
            converted.message =
                ToDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException__M7_message(value.Message);
            return converted;
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.EncryptionSdk.DecryptInput FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput(
            Dafny.Aws.EncryptionSdk._IDecryptInput value)
        {
            Dafny.Aws.EncryptionSdk.DecryptInput concrete = (Dafny.Aws.EncryptionSdk.DecryptInput)value;
            Aws.EncryptionSdk.DecryptInput converted = new Aws.EncryptionSdk.DecryptInput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M10_ciphertext(
                    concrete.ciphertext);
            if (concrete.materialsManager.is_Some)
                converted.MaterialsManager =
                    (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M16_materialsManager(
                        concrete.materialsManager);
            if (concrete.keyring.is_Some)
                converted.Keyring =
                    (Aws.EncryptionSdk.Core.IKeyring)FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M7_keyring(
                        concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk._IDecryptInput ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput(
            Aws.EncryptionSdk.DecryptInput value)
        {
            Aws.EncryptionSdk.Core.ICryptographicMaterialsManager var_materialsManager = value.IsSetMaterialsManager()
                ? value.MaterialsManager
                : (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)null;
            Aws.EncryptionSdk.Core.IKeyring var_keyring =
                value.IsSetKeyring() ? value.Keyring : (Aws.EncryptionSdk.Core.IKeyring)null;
            return new Dafny.Aws.EncryptionSdk.DecryptInput(
                ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M10_ciphertext(value.Ciphertext),
                ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M16_materialsManager(var_materialsManager),
                ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M7_keyring(var_keyring));
        }

        public static string FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException__M7_message(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException__M7_message(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.EncryptionSdk.Core.CommitmentPolicy
            FromDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.CommitmentPolicy)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy>
            ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                Aws.EncryptionSdk.Core.CommitmentPolicy value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core._ICommitmentPolicy>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_CommitmentPolicy(
                        (Aws.EncryptionSdk.Core.CommitmentPolicy)value));
        }

        public static Aws.EncryptionSdk.Core.IKeyring FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IKeyring)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M7_keyring(Aws.EncryptionSdk.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                        (Aws.EncryptionSdk.Core.IKeyring)value));
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

        public static long? FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M11_frameLength(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M11_frameLength(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.EncryptionSdk.AwsEncryptionSdkConfig
            FromDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig(
                Dafny.Aws.EncryptionSdk._IAwsEncryptionSdkConfig value)
        {
            Dafny.Aws.EncryptionSdk.AwsEncryptionSdkConfig concrete =
                (Dafny.Aws.EncryptionSdk.AwsEncryptionSdkConfig)value;
            Aws.EncryptionSdk.AwsEncryptionSdkConfig converted = new Aws.EncryptionSdk.AwsEncryptionSdkConfig();
            if (concrete.commitmentPolicy.is_Some)
                converted.CommitmentPolicy =
                    (Aws.EncryptionSdk.Core.CommitmentPolicy)
                    FromDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                        concrete.commitmentPolicy);
            if (concrete.maxEncryptedDataKeys.is_Some)
                converted.MaxEncryptedDataKeys =
                    (long)FromDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
                        concrete.maxEncryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk._IAwsEncryptionSdkConfig
            ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig(
                Aws.EncryptionSdk.AwsEncryptionSdkConfig value)
        {
            Aws.EncryptionSdk.Core.CommitmentPolicy var_commitmentPolicy = value.IsSetCommitmentPolicy()
                ? value.CommitmentPolicy
                : (Aws.EncryptionSdk.Core.CommitmentPolicy)null;
            long? var_maxEncryptedDataKeys =
                value.IsSetMaxEncryptedDataKeys() ? value.MaxEncryptedDataKeys : (long?)null;
            return new Dafny.Aws.EncryptionSdk.AwsEncryptionSdkConfig(
                ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                    var_commitmentPolicy),
                ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
                    var_maxEncryptedDataKeys));
        }

        public static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static long? FromDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
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

        public static System.IO.MemoryStream FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M17_encryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>
            ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(
                        (System.Collections.Generic.Dictionary<string, string>)value));
        }

        public static Aws.EncryptionSdk.Core.IKeyring FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.IKeyring)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.IKeyring>
            ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M7_keyring(Aws.EncryptionSdk.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S16_KeyringReference(
                        (Aws.EncryptionSdk.Core.IKeyring)value));
        }

        public static Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                    value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput__M16_materialsManager(
                Aws.EncryptionSdk.Core.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CryptographicMaterialsManagerReference(
                        (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)value));
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

        public static Aws.EncryptionSdk.EncryptInput FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput(
            Dafny.Aws.EncryptionSdk._IEncryptInput value)
        {
            Dafny.Aws.EncryptionSdk.EncryptInput concrete = (Dafny.Aws.EncryptionSdk.EncryptInput)value;
            Aws.EncryptionSdk.EncryptInput converted = new Aws.EncryptionSdk.EncryptInput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M9_plaintext(
                    concrete.plaintext);
            if (concrete.encryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M17_encryptionContext(
                        concrete.encryptionContext);
            if (concrete.materialsManager.is_Some)
                converted.MaterialsManager =
                    (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_materialsManager(
                        concrete.materialsManager);
            if (concrete.keyring.is_Some)
                converted.Keyring =
                    (Aws.EncryptionSdk.Core.IKeyring)FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M7_keyring(
                        concrete.keyring);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
                    FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_algorithmSuiteId(
                        concrete.algorithmSuiteId);
            if (concrete.frameLength.is_Some)
                converted.FrameLength =
                    (long)FromDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M11_frameLength(concrete.frameLength);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk._IEncryptInput ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput(
            Aws.EncryptionSdk.EncryptInput value)
        {
            System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.IsSetEncryptionContext()
                ? value.EncryptionContext
                : (System.Collections.Generic.Dictionary<string, string>)null;
            Aws.EncryptionSdk.Core.ICryptographicMaterialsManager var_materialsManager = value.IsSetMaterialsManager()
                ? value.MaterialsManager
                : (Aws.EncryptionSdk.Core.ICryptographicMaterialsManager)null;
            Aws.EncryptionSdk.Core.IKeyring var_keyring =
                value.IsSetKeyring() ? value.Keyring : (Aws.EncryptionSdk.Core.IKeyring)null;
            Aws.EncryptionSdk.Core.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (Aws.EncryptionSdk.Core.AlgorithmSuiteId)null;
            long? var_frameLength = value.IsSetFrameLength() ? value.FrameLength : (long?)null;
            return new Dafny.Aws.EncryptionSdk.EncryptInput(
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M17_encryptionContext(var_encryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_materialsManager(var_materialsManager),
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M7_keyring(var_keyring),
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M16_algorithmSuiteId(var_algorithmSuiteId),
                ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput__M11_frameLength(var_frameLength));
        }

        public static Aws.EncryptionSdk.DecryptOutput FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput(
            Dafny.Aws.EncryptionSdk._IDecryptOutput value)
        {
            Dafny.Aws.EncryptionSdk.DecryptOutput concrete = (Dafny.Aws.EncryptionSdk.DecryptOutput)value;
            Aws.EncryptionSdk.DecryptOutput converted = new Aws.EncryptionSdk.DecryptOutput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M9_plaintext(
                    concrete.plaintext);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M17_encryptionContext(
                    concrete.encryptionContext);
            converted.AlgorithmSuiteId =
                (Aws.EncryptionSdk.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            return converted;
        }

        public static Dafny.Aws.EncryptionSdk._IDecryptOutput ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput(
            Aws.EncryptionSdk.DecryptOutput value)
        {
            return new Dafny.Aws.EncryptionSdk.DecryptOutput(
                ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput__M16_algorithmSuiteId(value.AlgorithmSuiteId));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N13_encryptionSdk__N4_core__S17_EncryptionContext(value);
        }

        public static Aws.EncryptionSdk.AwsEncryptionSdkBaseException
            FromDafny_CommonError_AwsEncryptionSdkBaseException(
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException value)
        {
            if (value is Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException)
                return FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException(
                    (Dafny.Aws.EncryptionSdk.AwsEncryptionSdkException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException
            ToDafny_CommonError_AwsEncryptionSdkBaseException(Aws.EncryptionSdk.AwsEncryptionSdkBaseException value)
        {
            if (value is Aws.EncryptionSdk.AwsEncryptionSdkException)
                return ToDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkException(
                    (Aws.EncryptionSdk.AwsEncryptionSdkException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
