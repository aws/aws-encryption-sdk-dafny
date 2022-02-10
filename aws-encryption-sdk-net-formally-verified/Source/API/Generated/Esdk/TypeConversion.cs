// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Crypto;

namespace Aws.Esdk
{
    internal static class TypeConversion
    {
        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S13_EncryptOutput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S13_EncryptOutput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static long? FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long> ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(
            long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
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

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M5_value(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.Crypto.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(
                        (Aws.Crypto.ICryptographicMaterialsManager)value));
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

        public static Aws.Crypto.AlgorithmSuiteId FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(
            Wrappers_Compile._IOption<Dafny.Aws.Crypto._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.Crypto.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._IAlgorithmSuiteId>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(Aws.Crypto.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_AlgorithmSuiteId((Aws.Crypto.AlgorithmSuiteId)value));
        }

        public static Aws.Esdk.ConfigurationDefaults
            FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M14_configDefaults(
                Dafny.Aws.Esdk._IConfigurationDefaults value)
        {
            return FromDafny_N3_aws__N4_esdk__S21_ConfigurationDefaults(value);
        }

        public static Dafny.Aws.Esdk._IConfigurationDefaults
            ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M14_configDefaults(
                Aws.Esdk.ConfigurationDefaults value)
        {
            return ToDafny_N3_aws__N4_esdk__S21_ConfigurationDefaults(value);
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
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

        public static Aws.Esdk.AwsEncryptionSdkClientConfig FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig(
            Dafny.Aws.Esdk._IAwsEncryptionSdkClientConfig value)
        {
            Dafny.Aws.Esdk.AwsEncryptionSdkClientConfig concrete = (Dafny.Aws.Esdk.AwsEncryptionSdkClientConfig)value;
            Aws.Esdk.AwsEncryptionSdkClientConfig converted = new Aws.Esdk.AwsEncryptionSdkClientConfig();
            if (concrete.commitmentPolicy.is_Some)
                converted.CommitmentPolicy =
                    (Aws.Crypto.CommitmentPolicy)
                    FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M16_commitmentPolicy(
                        concrete.commitmentPolicy);
            if (concrete.maxEncryptedDataKeys.is_Some)
                converted.MaxEncryptedDataKeys =
                    (long)FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M20_maxEncryptedDataKeys(
                        concrete.maxEncryptedDataKeys);
            converted.ConfigDefaults =
                (Aws.Esdk.ConfigurationDefaults)
                FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M14_configDefaults(
                    concrete.configDefaults);
            return converted;
        }

        public static Dafny.Aws.Esdk._IAwsEncryptionSdkClientConfig
            ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig(Aws.Esdk.AwsEncryptionSdkClientConfig value)
        {
            return new Dafny.Aws.Esdk.AwsEncryptionSdkClientConfig(
                ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M16_commitmentPolicy(value.CommitmentPolicy),
                ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M20_maxEncryptedDataKeys(
                    value.MaxEncryptedDataKeys),
                ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M14_configDefaults(value.ConfigDefaults));
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

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Crypto.IKeyring)null
                : FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(Aws.Crypto.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_KeyringReference((Aws.Crypto.IKeyring)value));
        }

        public static Aws.Esdk.DecryptOutput FromDafny_N3_aws__N4_esdk__S13_DecryptOutput(
            Dafny.Aws.Esdk._IDecryptOutput value)
        {
            Dafny.Aws.Esdk.DecryptOutput concrete = (Dafny.Aws.Esdk.DecryptOutput)value;
            Aws.Esdk.DecryptOutput converted = new Aws.Esdk.DecryptOutput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(concrete.plaintext);
            return converted;
        }

        public static Dafny.Aws.Esdk._IDecryptOutput ToDafny_N3_aws__N4_esdk__S13_DecryptOutput(
            Aws.Esdk.DecryptOutput value)
        {
            return new Dafny.Aws.Esdk.DecryptOutput(
                ToDafny_N3_aws__N4_esdk__S13_DecryptOutput__M9_plaintext(value.Plaintext));
        }

        public static Aws.Esdk.EncryptInput FromDafny_N3_aws__N4_esdk__S12_EncryptInput(
            Dafny.Aws.Esdk._IEncryptInput value)
        {
            Dafny.Aws.Esdk.EncryptInput concrete = (Dafny.Aws.Esdk.EncryptInput)value;
            Aws.Esdk.EncryptInput converted = new Aws.Esdk.EncryptInput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(concrete.plaintext);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(concrete.encryptionContext);
            if (concrete.materialsManager != null)
                converted.MaterialsManager =
                    (Aws.Crypto.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(concrete.materialsManager);
            if (concrete.keyring != null)
                converted.Keyring =
                    (Aws.Crypto.IKeyring)FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(concrete.keyring);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.Crypto.AlgorithmSuiteId)FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(
                        concrete.algorithmSuiteId);
            if (concrete.frameLength.is_Some)
                converted.FrameLength =
                    (long)FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(concrete.frameLength);
            if (concrete.maxPlaintextLength.is_Some)
                converted.MaxPlaintextLength =
                    (long)FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M18_maxPlaintextLength(concrete
                        .maxPlaintextLength);
            return converted;
        }

        public static Dafny.Aws.Esdk._IEncryptInput ToDafny_N3_aws__N4_esdk__S12_EncryptInput(
            Aws.Esdk.EncryptInput value)
        {
            return new Dafny.Aws.Esdk.EncryptInput(
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(value.MaterialsManager),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M7_keyring(value.Keyring),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_algorithmSuiteId(value.AlgorithmSuiteId),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M11_frameLength(value.FrameLength),
                ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M18_maxPlaintextLength(value.MaxPlaintextLength));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N6_crypto__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
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

        public static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }

        public static Aws.Esdk.EncryptOutput FromDafny_N3_aws__N4_esdk__S13_EncryptOutput(
            Dafny.Aws.Esdk._IEncryptOutput value)
        {
            Dafny.Aws.Esdk.EncryptOutput concrete = (Dafny.Aws.Esdk.EncryptOutput)value;
            Aws.Esdk.EncryptOutput converted = new Aws.Esdk.EncryptOutput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N4_esdk__S13_EncryptOutput__M10_ciphertext(
                    concrete.ciphertext);
            return converted;
        }

        public static Dafny.Aws.Esdk._IEncryptOutput ToDafny_N3_aws__N4_esdk__S13_EncryptOutput(
            Aws.Esdk.EncryptOutput value)
        {
            return new Dafny.Aws.Esdk.EncryptOutput(
                ToDafny_N3_aws__N4_esdk__S13_EncryptOutput__M10_ciphertext(value.Ciphertext));
        }

        public static Aws.Esdk.ConfigurationDefaults FromDafny_N3_aws__N4_esdk__S21_ConfigurationDefaults(
            Dafny.Aws.Esdk._IConfigurationDefaults value)
        {
            if (value.is_V1) return Aws.Esdk.ConfigurationDefaults.V1;
            throw new System.ArgumentException("Invalid Aws.Esdk.ConfigurationDefaults value");
        }

        public static Dafny.Aws.Esdk._IConfigurationDefaults ToDafny_N3_aws__N4_esdk__S21_ConfigurationDefaults(
            Aws.Esdk.ConfigurationDefaults value)
        {
            if (Aws.Esdk.ConfigurationDefaults.V1.Equals(value)) return Dafny.Aws.Esdk.ConfigurationDefaults.create();
            throw new System.ArgumentException("Invalid Aws.Esdk.ConfigurationDefaults value");
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

        public static Aws.Crypto.ICryptographicMaterialsManager
            FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.Crypto.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M16_materialsManager(
                Aws.Crypto.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S38_CryptographicMaterialsManagerReference(
                        (Aws.Crypto.ICryptographicMaterialsManager)value));
        }

        public static long? FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M20_maxEncryptedDataKeys(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M20_maxEncryptedDataKeys(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static string FromDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException__M7_message(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException__M7_message(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
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

        public static long? FromDafny_N3_aws__N4_esdk__S12_EncryptInput__M18_maxPlaintextLength(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long> ToDafny_N3_aws__N4_esdk__S12_EncryptInput__M18_maxPlaintextLength(
            long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static string FromDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N6_crypto__S17_EncryptionContext__M3_key(string value)
        {
            return ToDafny_N3_aws__N6_crypto__S9_Utf8Bytes(value);
        }

        public static Aws.Crypto.IKeyring FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Crypto.IKeyring)null
                : FromDafny_N3_aws__N6_crypto__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto.IKeyring>
            ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(Aws.Crypto.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto.IKeyring>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_KeyringReference((Aws.Crypto.IKeyring)value));
        }

        public static Aws.Esdk.AwsEncryptionSdkClientException
            FromDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException(
                Dafny.Aws.Esdk.AwsEncryptionSdkClientException value)
        {
            return new Aws.Esdk.AwsEncryptionSdkClientException(
                FromDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException__M7_message(value.message));
        }

        public static Dafny.Aws.Esdk.AwsEncryptionSdkClientException
            ToDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException(Aws.Esdk.AwsEncryptionSdkClientException value)
        {
            Dafny.Aws.Esdk.AwsEncryptionSdkClientException converted =
                new Dafny.Aws.Esdk.AwsEncryptionSdkClientException();
            converted.message = ToDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException__M7_message(value.Message);
            return converted;
        }

        public static Aws.Esdk.DecryptInput FromDafny_N3_aws__N4_esdk__S12_DecryptInput(
            Dafny.Aws.Esdk._IDecryptInput value)
        {
            Dafny.Aws.Esdk.DecryptInput concrete = (Dafny.Aws.Esdk.DecryptInput)value;
            Aws.Esdk.DecryptInput converted = new Aws.Esdk.DecryptInput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M10_ciphertext(
                    concrete.ciphertext);
            if (concrete.materialsManager != null)
                converted.MaterialsManager =
                    (Aws.Crypto.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(concrete.materialsManager);
            if (concrete.keyring != null)
                converted.Keyring =
                    (Aws.Crypto.IKeyring)FromDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.Esdk._IDecryptInput ToDafny_N3_aws__N4_esdk__S12_DecryptInput(
            Aws.Esdk.DecryptInput value)
        {
            return new Dafny.Aws.Esdk.DecryptInput(
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M10_ciphertext(value.Ciphertext),
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M16_materialsManager(value.MaterialsManager),
                ToDafny_N3_aws__N4_esdk__S12_DecryptInput__M7_keyring(value.Keyring));
        }

        public static Aws.Crypto.CommitmentPolicy
            FromDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M16_commitmentPolicy(
                Wrappers_Compile._IOption<Dafny.Aws.Crypto._ICommitmentPolicy> value)
        {
            return value.is_None
                ? (Aws.Crypto.CommitmentPolicy)null
                : FromDafny_N3_aws__N6_crypto__S16_CommitmentPolicy(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Crypto._ICommitmentPolicy>
            ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig__M16_commitmentPolicy(
                Aws.Crypto.CommitmentPolicy value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Crypto._ICommitmentPolicy>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Crypto._ICommitmentPolicy>.create_Some(
                    ToDafny_N3_aws__N6_crypto__S16_CommitmentPolicy((Aws.Crypto.CommitmentPolicy)value));
        }

        public static Aws.Esdk.AwsEncryptionSdkException FromDafny_CommonError_AwsEncryptionSdkException(
            Dafny.Aws.Esdk.IAwsEncryptionSdkException value)
        {
            if (value is Dafny.Aws.Esdk.AwsEncryptionSdkClientException)
                return FromDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException(
                    (Dafny.Aws.Esdk.AwsEncryptionSdkClientException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.Esdk.IAwsEncryptionSdkException ToDafny_CommonError_AwsEncryptionSdkException(
            Aws.Esdk.AwsEncryptionSdkException value)
        {
            if (value is Aws.Esdk.AwsEncryptionSdkClientException)
                return ToDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientException(
                    (Aws.Esdk.AwsEncryptionSdkClientException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
