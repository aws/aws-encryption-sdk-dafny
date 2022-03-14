// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Encryption.Core;

namespace Aws.Encryption
{
    internal static class TypeConversion
    {
        public static System.IO.MemoryStream FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Encryption.DecryptOutput FromDafny_N3_aws__N10_encryption__S13_DecryptOutput(
            Dafny.Aws.Encryption._IDecryptOutput value)
        {
            Dafny.Aws.Encryption.DecryptOutput concrete = (Dafny.Aws.Encryption.DecryptOutput)value;
            Aws.Encryption.DecryptOutput converted = new Aws.Encryption.DecryptOutput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M9_plaintext(
                    concrete.plaintext);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M17_encryptionContext(concrete.encryptionContext);
            converted.AlgorithmSuiteId =
                (Aws.Encryption.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            return converted;
        }

        public static Dafny.Aws.Encryption._IDecryptOutput ToDafny_N3_aws__N10_encryption__S13_DecryptOutput(
            Aws.Encryption.DecryptOutput value)
        {
            return new Dafny.Aws.Encryption.DecryptOutput(
                ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M16_algorithmSuiteId(value.AlgorithmSuiteId));
        }

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_algorithmSuiteId(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.AlgorithmSuiteId)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>
            ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._IAlgorithmSuiteId>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(
                        (Aws.Encryption.Core.AlgorithmSuiteId)value));
        }

        public static Aws.Encryption.Core.IKeyring FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IKeyring)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring>
            ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M7_keyring(Aws.Encryption.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference((Aws.Encryption.Core.IKeyring)value));
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

        public static Aws.Encryption.AwsEncryptionSdkException
            FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException(
                Dafny.Aws.Encryption.AwsEncryptionSdkException value)
        {
            return new Aws.Encryption.AwsEncryptionSdkException(
                FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException__M7_message(value.message));
        }

        public static Dafny.Aws.Encryption.AwsEncryptionSdkException
            ToDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException(
                Aws.Encryption.AwsEncryptionSdkException value)
        {
            Dafny.Aws.Encryption.AwsEncryptionSdkException converted =
                new Dafny.Aws.Encryption.AwsEncryptionSdkException();
            converted.message =
                ToDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException__M7_message(value.Message);
            return converted;
        }

        public static Aws.Encryption.IAwsEncryptionSdk FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkReference(
            Dafny.Aws.Encryption.IAwsEncryptionSdk value)
        {
            return new AwsEncryptionSdk(value);
        }

        public static Dafny.Aws.Encryption.IAwsEncryptionSdk
            ToDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkReference(Aws.Encryption.IAwsEncryptionSdk value)
        {
            if (value is AwsEncryptionSdk valueWithImpl)
            {
                return valueWithImpl._impl;
            }

            throw new System.ArgumentException(
                "Custom implementations of Aws.Encryption.IAwsEncryptionSdk are not supported yet");
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

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M16_algorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static long? FromDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long>
            ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }

        public static Aws.Encryption.EncryptInput FromDafny_N3_aws__N10_encryption__S12_EncryptInput(
            Dafny.Aws.Encryption._IEncryptInput value)
        {
            Dafny.Aws.Encryption.EncryptInput concrete = (Dafny.Aws.Encryption.EncryptInput)value;
            Aws.Encryption.EncryptInput converted = new Aws.Encryption.EncryptInput();
            converted.Plaintext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M9_plaintext(
                    concrete.plaintext);
            if (concrete.encryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M17_encryptionContext(
                        concrete.encryptionContext);
            if (concrete.materialsManager.is_Some)
                converted.MaterialsManager =
                    (Aws.Encryption.Core.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_materialsManager(concrete.materialsManager);
            if (concrete.keyring.is_Some)
                converted.Keyring =
                    (Aws.Encryption.Core.IKeyring)FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M7_keyring(
                        concrete.keyring);
            if (concrete.algorithmSuiteId.is_Some)
                converted.AlgorithmSuiteId =
                    (Aws.Encryption.Core.AlgorithmSuiteId)
                    FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            if (concrete.frameLength.is_Some)
                converted.FrameLength =
                    (long)FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M11_frameLength(concrete.frameLength);
            return converted;
        }

        public static Dafny.Aws.Encryption._IEncryptInput ToDafny_N3_aws__N10_encryption__S12_EncryptInput(
            Aws.Encryption.EncryptInput value)
        {
            System.Collections.Generic.Dictionary<string, string> var_encryptionContext = value.IsSetEncryptionContext()
                ? value.EncryptionContext
                : (System.Collections.Generic.Dictionary<string, string>)null;
            Aws.Encryption.Core.ICryptographicMaterialsManager var_materialsManager = value.IsSetMaterialsManager()
                ? value.MaterialsManager
                : (Aws.Encryption.Core.ICryptographicMaterialsManager)null;
            Aws.Encryption.Core.IKeyring var_keyring =
                value.IsSetKeyring() ? value.Keyring : (Aws.Encryption.Core.IKeyring)null;
            Aws.Encryption.Core.AlgorithmSuiteId var_algorithmSuiteId = value.IsSetAlgorithmSuiteId()
                ? value.AlgorithmSuiteId
                : (Aws.Encryption.Core.AlgorithmSuiteId)null;
            long? var_frameLength = value.IsSetFrameLength() ? value.FrameLength : (long?)null;
            return new Dafny.Aws.Encryption.EncryptInput(
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M9_plaintext(value.Plaintext),
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M17_encryptionContext(var_encryptionContext),
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_materialsManager(var_materialsManager),
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M7_keyring(var_keyring),
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_algorithmSuiteId(var_algorithmSuiteId),
                ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M11_frameLength(var_frameLength));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Aws.Encryption.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                    value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M16_materialsManager(
                Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                        (Aws.Encryption.Core.ICryptographicMaterialsManager)value));
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

        public static Aws.Encryption.EncryptOutput FromDafny_N3_aws__N10_encryption__S13_EncryptOutput(
            Dafny.Aws.Encryption._IEncryptOutput value)
        {
            Dafny.Aws.Encryption.EncryptOutput concrete = (Dafny.Aws.Encryption.EncryptOutput)value;
            Aws.Encryption.EncryptOutput converted = new Aws.Encryption.EncryptOutput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M10_ciphertext(
                    concrete.ciphertext);
            converted.EncryptionContext =
                (System.Collections.Generic.Dictionary<string, string>)
                FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M17_encryptionContext(concrete.encryptionContext);
            converted.AlgorithmSuiteId =
                (Aws.Encryption.Core.AlgorithmSuiteId)
                FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M16_algorithmSuiteId(concrete.algorithmSuiteId);
            return converted;
        }

        public static Dafny.Aws.Encryption._IEncryptOutput ToDafny_N3_aws__N10_encryption__S13_EncryptOutput(
            Aws.Encryption.EncryptOutput value)
        {
            return new Dafny.Aws.Encryption.EncryptOutput(
                ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M10_ciphertext(value.Ciphertext),
                ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M17_encryptionContext(value.EncryptionContext),
                ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M16_algorithmSuiteId(value.AlgorithmSuiteId));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M17_encryptionContext(
                Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>> value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>
            ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value);
        }

        public static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static string FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException__M7_message(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException__M7_message(
            string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }

        public static Aws.Encryption.DecryptInput FromDafny_N3_aws__N10_encryption__S12_DecryptInput(
            Dafny.Aws.Encryption._IDecryptInput value)
        {
            Dafny.Aws.Encryption.DecryptInput concrete = (Dafny.Aws.Encryption.DecryptInput)value;
            Aws.Encryption.DecryptInput converted = new Aws.Encryption.DecryptInput();
            converted.Ciphertext =
                (System.IO.MemoryStream)FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M10_ciphertext(
                    concrete.ciphertext);
            if (concrete.materialsManager.is_Some)
                converted.MaterialsManager =
                    (Aws.Encryption.Core.ICryptographicMaterialsManager)
                    FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M16_materialsManager(concrete.materialsManager);
            if (concrete.keyring.is_Some)
                converted.Keyring =
                    (Aws.Encryption.Core.IKeyring)FromDafny_N3_aws__N10_encryption__S12_DecryptInput__M7_keyring(
                        concrete.keyring);
            return converted;
        }

        public static Dafny.Aws.Encryption._IDecryptInput ToDafny_N3_aws__N10_encryption__S12_DecryptInput(
            Aws.Encryption.DecryptInput value)
        {
            Aws.Encryption.Core.ICryptographicMaterialsManager var_materialsManager = value.IsSetMaterialsManager()
                ? value.MaterialsManager
                : (Aws.Encryption.Core.ICryptographicMaterialsManager)null;
            Aws.Encryption.Core.IKeyring var_keyring =
                value.IsSetKeyring() ? value.Keyring : (Aws.Encryption.Core.IKeyring)null;
            return new Dafny.Aws.Encryption.DecryptInput(
                ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M10_ciphertext(value.Ciphertext),
                ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M16_materialsManager(var_materialsManager),
                ToDafny_N3_aws__N10_encryption__S12_DecryptInput__M7_keyring(var_keyring));
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
            FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M17_encryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>
            ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M17_encryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S17_EncryptionContext(
                        (System.Collections.Generic.Dictionary<string, string>)value));
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

        public static Aws.Encryption.Core.IKeyring FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M7_keyring(
            Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.IKeyring)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.IKeyring>
            ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M7_keyring(Aws.Encryption.Core.IKeyring value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.IKeyring>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_KeyringReference((Aws.Encryption.Core.IKeyring)value));
        }

        public static Aws.Encryption.AwsEncryptionSdkConfig
            FromDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig(
                Dafny.Aws.Encryption._IAwsEncryptionSdkConfig value)
        {
            Dafny.Aws.Encryption.AwsEncryptionSdkConfig concrete = (Dafny.Aws.Encryption.AwsEncryptionSdkConfig)value;
            Aws.Encryption.AwsEncryptionSdkConfig converted = new Aws.Encryption.AwsEncryptionSdkConfig();
            if (concrete.commitmentPolicy.is_Some)
                converted.CommitmentPolicy =
                    (Aws.Encryption.Core.CommitmentPolicy)
                    FromDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                        concrete.commitmentPolicy);
            if (concrete.maxEncryptedDataKeys.is_Some)
                converted.MaxEncryptedDataKeys =
                    (long)FromDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
                        concrete.maxEncryptedDataKeys);
            return converted;
        }

        public static Dafny.Aws.Encryption._IAwsEncryptionSdkConfig
            ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig(Aws.Encryption.AwsEncryptionSdkConfig value)
        {
            Aws.Encryption.Core.CommitmentPolicy var_commitmentPolicy = value.IsSetCommitmentPolicy()
                ? value.CommitmentPolicy
                : (Aws.Encryption.Core.CommitmentPolicy)null;
            long? var_maxEncryptedDataKeys =
                value.IsSetMaxEncryptedDataKeys() ? value.MaxEncryptedDataKeys : (long?)null;
            return new Dafny.Aws.Encryption.AwsEncryptionSdkConfig(
                ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(var_commitmentPolicy),
                ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M20_maxEncryptedDataKeys(
                    var_maxEncryptedDataKeys));
        }

        public static Aws.Encryption.Core.CommitmentPolicy
            FromDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._ICommitmentPolicy> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.CommitmentPolicy)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core._ICommitmentPolicy>
            ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig__M16_commitmentPolicy(
                Aws.Encryption.Core.CommitmentPolicy value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._ICommitmentPolicy>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core._ICommitmentPolicy>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S16_CommitmentPolicy(
                        (Aws.Encryption.Core.CommitmentPolicy)value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N10_encryption__S13_EncryptOutput__M10_ciphertext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__S13_EncryptOutput__M10_ciphertext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static long? FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M11_frameLength(
            Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }

        public static Wrappers_Compile._IOption<long> ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M11_frameLength(
            long? value)
        {
            return value == null
                ? Wrappers_Compile.Option<long>.create_None()
                : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
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

        public static Aws.Encryption.Core.AlgorithmSuiteId
            FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M16_algorithmSuiteId(
                Dafny.Aws.Encryption.Core._IAlgorithmSuiteId value)
        {
            return FromDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Dafny.Aws.Encryption.Core._IAlgorithmSuiteId
            ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M16_algorithmSuiteId(
                Aws.Encryption.Core.AlgorithmSuiteId value)
        {
            return ToDafny_N3_aws__N10_encryption__N4_core__S16_AlgorithmSuiteId(value);
        }

        public static Aws.Encryption.Core.ICryptographicMaterialsManager
            FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_materialsManager(
                Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager> value)
        {
            return value.is_None
                ? (Aws.Encryption.Core.ICryptographicMaterialsManager)null
                : FromDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                    value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>
            ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M16_materialsManager(
                Aws.Encryption.Core.ICryptographicMaterialsManager value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>.create_None()
                : Wrappers_Compile.Option<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager>.create_Some(
                    ToDafny_N3_aws__N10_encryption__N4_core__S38_CryptographicMaterialsManagerReference(
                        (Aws.Encryption.Core.ICryptographicMaterialsManager)value));
        }

        public static System.IO.MemoryStream FromDafny_N3_aws__N10_encryption__S12_EncryptInput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__S12_EncryptInput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
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

        public static System.IO.MemoryStream FromDafny_N3_aws__N10_encryption__S13_DecryptOutput__M9_plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_aws__N10_encryption__S13_DecryptOutput__M9_plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N6_smithy__N3_api__S4_Blob(value);
        }

        public static Aws.Encryption.AwsEncryptionSdkBaseException FromDafny_CommonError_AwsEncryptionSdkBaseException(
            Dafny.Aws.Encryption.IAwsEncryptionSdkException value)
        {
            if (value is Dafny.Aws.Encryption.AwsEncryptionSdkException)
                return FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException(
                    (Dafny.Aws.Encryption.AwsEncryptionSdkException)value);
            throw new System.ArgumentException("Unknown exception type");
        }

        public static Dafny.Aws.Encryption.IAwsEncryptionSdkException ToDafny_CommonError_AwsEncryptionSdkBaseException(
            Aws.Encryption.AwsEncryptionSdkBaseException value)
        {
            if (value is Aws.Encryption.AwsEncryptionSdkException)
                return ToDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkException(
                    (Aws.Encryption.AwsEncryptionSdkException)value);
            throw new System.ArgumentException("Unknown exception type");
        }
    }
}
