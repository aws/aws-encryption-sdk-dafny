// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Linq;
using Aws.Crypto;

namespace Com.Amazonaws.Kms
{
    internal static class TypeConversion
    {
        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.GrantListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member(
                Dafny.Com.Amazonaws.Kms._IGrantListEntry value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IGrantListEntry
            ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member(
                Amazon.KeyManagementService.Model.GrantListEntry value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec> value)
        {
            return new System.Collections.Generic.List<string>(value.Elements
                .Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member)
                .Select<Amazon.KeyManagementService.SigningAlgorithmSpec, string>(x => x));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(
                System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>.FromArray(value
                .Select<string, Amazon.KeyManagementService.SigningAlgorithmSpec>(x => x)
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member).ToArray());
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(
                string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(
                System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value);
        }

        public static Amazon.KeyManagementService.KeyUsageType FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(
            Dafny.Com.Amazonaws.Kms._IKeyUsageType value)
        {
            if (value.is_SIGN__VERIFY) return Amazon.KeyManagementService.KeyUsageType.SIGN_VERIFY;
            if (value.is_ENCRYPT__DECRYPT) return Amazon.KeyManagementService.KeyUsageType.ENCRYPT_DECRYPT;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyUsageType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IKeyUsageType ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(
            Amazon.KeyManagementService.KeyUsageType value)
        {
            if (Amazon.KeyManagementService.KeyUsageType.SIGN_VERIFY.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyUsageType.create_SIGN__VERIFY();
            if (Amazon.KeyManagementService.KeyUsageType.ENCRYPT_DECRYPT.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyUsageType.create_ENCRYPT__DECRYPT();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyUsageType value");
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(
                Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreResponse value)
        {
            Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse concrete =
                (Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse) value;
            Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse converted =
                new Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse();
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(
                Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(
                Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionRequest concrete =
                (Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionRequest) value;
            Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest converted =
                new Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(
                    concrete.KeyId);
            if (concrete.PendingWindowInDays.is_Some)
                converted.PendingWindowInDays =
                    (int)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(
                        concrete.PendingWindowInDays);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(
                Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(
                    value.PendingWindowInDays));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(
                System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
        }

        public static Amazon.KeyManagementService.DataKeyPairSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(
                Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(
                Amazon.KeyManagementService.DataKeyPairSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
        }

        public static Amazon.KeyManagementService.CustomerMasterKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(
                Amazon.KeyManagementService.CustomerMasterKeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(
                        (Amazon.KeyManagementService.CustomerMasterKeySpec) value));
        }

        public static Amazon.KeyManagementService.Model.EncryptRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(Dafny.Com.Amazonaws.Kms._IEncryptRequest value)
        {
            Dafny.Com.Amazonaws.Kms.EncryptRequest concrete = (Dafny.Com.Amazonaws.Kms.EncryptRequest) value;
            Amazon.KeyManagementService.Model.EncryptRequest converted =
                new Amazon.KeyManagementService.Model.EncryptRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(concrete.KeyId);
            converted.Plaintext =
                (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(
                    concrete.Plaintext);
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(concrete.GrantTokens);
            if (concrete.EncryptionAlgorithm.is_Some)
                converted.EncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(
                        concrete.EncryptionAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IEncryptRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(
            Amazon.KeyManagementService.Model.EncryptRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.EncryptRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(value.Plaintext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(value.GrantTokens),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(
                    value.EncryptionAlgorithm));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static Amazon.KeyManagementService.Model.InvalidAliasNameException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(
                Dafny.Com.Amazonaws.Kms._IInvalidAliasNameException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidAliasNameException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidAliasNameException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidAliasNameException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidAliasNameException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException(
                Amazon.KeyManagementService.Model.InvalidAliasNameException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidAliasNameException(message);
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextRequest) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest();
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            converted.KeyId =
                (string)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(
                    concrete.KeyId);
            converted.KeyPairSpec =
                (Amazon.KeyManagementService.DataKeyPairSpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(
                    concrete.KeyPairSpec);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(
                Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(
                    value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(
                    value.KeyPairSpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(
                    value.GrantTokens));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static int FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(int value)
        {
            return value;
        }

        public static int ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(int value)
        {
            return value;
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.DisableKeyRotationRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(
                Dafny.Com.Amazonaws.Kms._IDisableKeyRotationRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DisableKeyRotationRequest concrete =
                (Dafny.Com.Amazonaws.Kms.DisableKeyRotationRequest) value;
            Amazon.KeyManagementService.Model.DisableKeyRotationRequest converted =
                new Amazon.KeyManagementService.Model.DisableKeyRotationRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(
                    concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDisableKeyRotationRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(
                Amazon.KeyManagementService.Model.DisableKeyRotationRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DisableKeyRotationRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(value.KeyId));
        }

        public static Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(
                Dafny.Com.Amazonaws.Kms._ICloudHsmClusterInvalidConfigurationException value)
        {
            Dafny.Com.Amazonaws.Kms.CloudHsmClusterInvalidConfigurationException concrete =
                (Dafny.Com.Amazonaws.Kms.CloudHsmClusterInvalidConfigurationException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICloudHsmClusterInvalidConfigurationException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException(
                Amazon.KeyManagementService.Model.CloudHsmClusterInvalidConfigurationException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CloudHsmClusterInvalidConfigurationException(message);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value);
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value);
        }

        public static Amazon.KeyManagementService.MultiRegionKeyType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.MultiRegionKeyType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(
                Amazon.KeyManagementService.MultiRegionKeyType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType(
                        (Amazon.KeyManagementService.MultiRegionKeyType) value));
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoresListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(value);
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member(
                Amazon.KeyManagementService.Model.CustomKeyStoresListEntry value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec value)
        {
            if (value.is_SYMMETRIC__DEFAULT)
                return Amazon.KeyManagementService.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT;
            if (value.is_RSAES__OAEP__SHA__1)
                return Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1;
            if (value.is_RSAES__OAEP__SHA__256)
                return Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.EncryptionAlgorithmSpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT.Equals(value))
                return Dafny.Com.Amazonaws.Kms.EncryptionAlgorithmSpec.create_SYMMETRIC__DEFAULT();
            if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1.Equals(value))
                return Dafny.Com.Amazonaws.Kms.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1();
            if (Amazon.KeyManagementService.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.EncryptionAlgorithmSpec value");
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.KeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(
            Dafny.Com.Amazonaws.Kms._IKeySpec value)
        {
            if (value.is_RSA__2048) return Amazon.KeyManagementService.KeySpec.RSA_2048;
            if (value.is_RSA__3072) return Amazon.KeyManagementService.KeySpec.RSA_3072;
            if (value.is_RSA__4096) return Amazon.KeyManagementService.KeySpec.RSA_4096;
            if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P256;
            if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P384;
            if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.KeySpec.ECC_NIST_P521;
            if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.KeySpec.ECC_SECG_P256K1;
            if (value.is_SYMMETRIC__DEFAULT) return Amazon.KeyManagementService.KeySpec.SYMMETRIC_DEFAULT;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeySpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(
            Amazon.KeyManagementService.KeySpec value)
        {
            if (Amazon.KeyManagementService.KeySpec.RSA_2048.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_RSA__2048();
            if (Amazon.KeyManagementService.KeySpec.RSA_3072.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_RSA__3072();
            if (Amazon.KeyManagementService.KeySpec.RSA_4096.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_RSA__4096();
            if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_ECC__NIST__P256();
            if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_ECC__NIST__P384();
            if (Amazon.KeyManagementService.KeySpec.ECC_NIST_P521.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_ECC__NIST__P521();
            if (Amazon.KeyManagementService.KeySpec.ECC_SECG_P256K1.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_ECC__SECG__P256K1();
            if (Amazon.KeyManagementService.KeySpec.SYMMETRIC_DEFAULT.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeySpec.create_SYMMETRIC__DEFAULT();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeySpec value");
        }

        public static Amazon.KeyManagementService.OriginType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IOriginType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.OriginType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IOriginType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(
                Amazon.KeyManagementService.OriginType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IOriginType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IOriginType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(
                        (Amazon.KeyManagementService.OriginType) value));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(
            System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static Amazon.KeyManagementService.Model.MultiRegionKey
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(Dafny.Com.Amazonaws.Kms._IMultiRegionKey value)
        {
            Dafny.Com.Amazonaws.Kms.MultiRegionKey concrete = (Dafny.Com.Amazonaws.Kms.MultiRegionKey) value;
            Amazon.KeyManagementService.Model.MultiRegionKey converted =
                new Amazon.KeyManagementService.Model.MultiRegionKey();
            if (concrete.Arn.is_Some)
                converted.Arn =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(concrete.Arn);
            if (concrete.Region.is_Some)
                converted.Region =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(concrete.Region);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IMultiRegionKey ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(
            Amazon.KeyManagementService.Model.MultiRegionKey value)
        {
            return new Dafny.Com.Amazonaws.Kms.MultiRegionKey(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(value.Arn),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(value.Region));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.WrappingKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(
                Dafny.Com.Amazonaws.Kms._IWrappingKeySpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IWrappingKeySpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(
                Amazon.KeyManagementService.WrappingKeySpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(value);
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static Amazon.KeyManagementService.MessageType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMessageType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.MessageType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMessageType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(
                Amazon.KeyManagementService.MessageType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMessageType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMessageType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(
                        (Amazon.KeyManagementService.MessageType) value));
        }

        public static Amazon.KeyManagementService.Model.SignResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(Dafny.Com.Amazonaws.Kms._ISignResponse value)
        {
            Dafny.Com.Amazonaws.Kms.SignResponse concrete = (Dafny.Com.Amazonaws.Kms.SignResponse) value;
            Amazon.KeyManagementService.Model.SignResponse converted =
                new Amazon.KeyManagementService.Model.SignResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(concrete.KeyId);
            if (concrete.Signature.is_Some)
                converted.Signature =
                    (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(
                        concrete.Signature);
            if (concrete.SigningAlgorithm.is_Some)
                converted.SigningAlgorithm =
                    (Amazon.KeyManagementService.SigningAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(
                        concrete.SigningAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ISignResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(
            Amazon.KeyManagementService.Model.SignResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.SignResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(value.Signature),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(value.SigningAlgorithm));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static int FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(int value)
        {
            return value;
        }

        public static int ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(int value)
        {
            return value;
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.Model.GetPublicKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(
                Dafny.Com.Amazonaws.Kms._IGetPublicKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GetPublicKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.GetPublicKeyRequest) value;
            Amazon.KeyManagementService.Model.GetPublicKeyRequest converted =
                new Amazon.KeyManagementService.Model.GetPublicKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(concrete.KeyId);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetPublicKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(
                Amazon.KeyManagementService.Model.GetPublicKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetPublicKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest__M11_GrantTokens(value.GrantTokens));
        }

        public static Amazon.KeyManagementService.Model.KeyMetadata
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.KeyMetadata) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(
                Amazon.KeyManagementService.Model.KeyMetadata value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(
                        (Amazon.KeyManagementService.Model.KeyMetadata) value));
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(
            bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.Model.ReEncryptResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(
                Dafny.Com.Amazonaws.Kms._IReEncryptResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ReEncryptResponse concrete = (Dafny.Com.Amazonaws.Kms.ReEncryptResponse) value;
            Amazon.KeyManagementService.Model.ReEncryptResponse converted =
                new Amazon.KeyManagementService.Model.ReEncryptResponse();
            if (concrete.CiphertextBlob.is_Some)
                converted.CiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(
                        concrete.CiphertextBlob);
            if (concrete.SourceKeyId.is_Some)
                converted.SourceKeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(
                        concrete.SourceKeyId);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(concrete.KeyId);
            if (concrete.SourceEncryptionAlgorithm.is_Some)
                converted.SourceEncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(
                        concrete.SourceEncryptionAlgorithm);
            if (concrete.DestinationEncryptionAlgorithm.is_Some)
                converted.DestinationEncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(
                        concrete.DestinationEncryptionAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IReEncryptResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(
                Amazon.KeyManagementService.Model.ReEncryptResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ReEncryptResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(value.SourceKeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(
                    value.SourceEncryptionAlgorithm),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M30_DestinationEncryptionAlgorithm(
                    value.DestinationEncryptionAlgorithm));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Amazon.KeyManagementService.Model.InvalidGrantTokenException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(
                Dafny.Com.Amazonaws.Kms._IInvalidGrantTokenException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidGrantTokenException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidGrantTokenException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidGrantTokenException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidGrantTokenException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException(
                Amazon.KeyManagementService.Model.InvalidGrantTokenException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidGrantTokenException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.DecryptResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(Dafny.Com.Amazonaws.Kms._IDecryptResponse value)
        {
            Dafny.Com.Amazonaws.Kms.DecryptResponse concrete = (Dafny.Com.Amazonaws.Kms.DecryptResponse) value;
            Amazon.KeyManagementService.Model.DecryptResponse converted =
                new Amazon.KeyManagementService.Model.DecryptResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(concrete.KeyId);
            if (concrete.Plaintext.is_Some)
                converted.Plaintext =
                    (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(
                        concrete.Plaintext);
            if (concrete.EncryptionAlgorithm.is_Some)
                converted.EncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(
                        concrete.EncryptionAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDecryptResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(
                Amazon.KeyManagementService.Model.DecryptResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.DecryptResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(value.Plaintext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(
                    value.EncryptionAlgorithm));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static Amazon.KeyManagementService.Model.LimitExceededException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(
                Dafny.Com.Amazonaws.Kms._ILimitExceededException value)
        {
            Dafny.Com.Amazonaws.Kms.LimitExceededException concrete =
                (Dafny.Com.Amazonaws.Kms.LimitExceededException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.LimitExceededException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ILimitExceededException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException(
                Amazon.KeyManagementService.Model.LimitExceededException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.LimitExceededException(message);
        }

        public static Amazon.KeyManagementService.Model.RetireGrantRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(
                Dafny.Com.Amazonaws.Kms._IRetireGrantRequest value)
        {
            Dafny.Com.Amazonaws.Kms.RetireGrantRequest concrete = (Dafny.Com.Amazonaws.Kms.RetireGrantRequest) value;
            Amazon.KeyManagementService.Model.RetireGrantRequest converted =
                new Amazon.KeyManagementService.Model.RetireGrantRequest();
            if (concrete.GrantToken.is_Some)
                converted.GrantToken =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(
                        concrete.GrantToken);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(concrete.KeyId);
            if (concrete.GrantId.is_Some)
                converted.GrantId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(
                        concrete.GrantId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IRetireGrantRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(
                Amazon.KeyManagementService.Model.RetireGrantRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.RetireGrantRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(value.GrantToken),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(value.GrantId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
        }

        public static bool?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(
                Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry> value)
        {
            return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.Model.InvalidArnException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(
                Dafny.Com.Amazonaws.Kms._IInvalidArnException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidArnException concrete = (Dafny.Com.Amazonaws.Kms.InvalidArnException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidArnException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidArnException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException(
                Amazon.KeyManagementService.Model.InvalidArnException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidArnException(message);
        }

        public static Amazon.KeyManagementService.Model.GenerateRandomResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(
                Dafny.Com.Amazonaws.Kms._IGenerateRandomResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateRandomResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateRandomResponse) value;
            Amazon.KeyManagementService.Model.GenerateRandomResponse converted =
                new Amazon.KeyManagementService.Model.GenerateRandomResponse();
            if (concrete.Plaintext.is_Some)
                converted.Plaintext =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(
                        concrete.Plaintext);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateRandomResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(
                Amazon.KeyManagementService.Model.GenerateRandomResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateRandomResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(value.Plaintext));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(
                Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static Amazon.KeyManagementService.Model.InvalidMarkerException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(
                Dafny.Com.Amazonaws.Kms._IInvalidMarkerException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidMarkerException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidMarkerException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidMarkerException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidMarkerException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException(
                Amazon.KeyManagementService.Model.InvalidMarkerException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidMarkerException(message);
        }

        public static Amazon.KeyManagementService.Model.KMSInternalException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(
                Dafny.Com.Amazonaws.Kms._IKMSInternalException value)
        {
            Dafny.Com.Amazonaws.Kms.KMSInternalException
                concrete = (Dafny.Com.Amazonaws.Kms.KMSInternalException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.KMSInternalException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IKMSInternalException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException(
                Amazon.KeyManagementService.Model.KMSInternalException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.KMSInternalException(message);
        }

        public static Amazon.KeyManagementService.CustomerMasterKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(
                Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec value)
        {
            if (value.is_RSA__2048) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_2048;
            if (value.is_RSA__3072) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_3072;
            if (value.is_RSA__4096) return Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_4096;
            if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P256;
            if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P384;
            if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P521;
            if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_SECG_P256K1;
            if (value.is_SYMMETRIC__DEFAULT) return Amazon.KeyManagementService.CustomerMasterKeySpec.SYMMETRIC_DEFAULT;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.CustomerMasterKeySpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(
                Amazon.KeyManagementService.CustomerMasterKeySpec value)
        {
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_2048.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_RSA__2048();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_3072.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_RSA__3072();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.RSA_4096.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_RSA__4096();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_ECC__NIST__P256();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_ECC__NIST__P384();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_NIST_P521.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_ECC__NIST__P521();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.ECC_SECG_P256K1.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_ECC__SECG__P256K1();
            if (Amazon.KeyManagementService.CustomerMasterKeySpec.SYMMETRIC_DEFAULT.Equals(value))
                return Dafny.Com.Amazonaws.Kms.CustomerMasterKeySpec.create_SYMMETRIC__DEFAULT();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.CustomerMasterKeySpec value");
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.Model.UntagResourceRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(
                Dafny.Com.Amazonaws.Kms._IUntagResourceRequest value)
        {
            Dafny.Com.Amazonaws.Kms.UntagResourceRequest
                concrete = (Dafny.Com.Amazonaws.Kms.UntagResourceRequest) value;
            Amazon.KeyManagementService.Model.UntagResourceRequest converted =
                new Amazon.KeyManagementService.Model.UntagResourceRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(concrete.KeyId);
            converted.TagKeys =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(concrete.TagKeys);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUntagResourceRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(
                Amazon.KeyManagementService.Model.UntagResourceRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.UntagResourceRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(value.TagKeys));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.Tag FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(
            Dafny.Com.Amazonaws.Kms._ITag value)
        {
            Dafny.Com.Amazonaws.Kms.Tag concrete = (Dafny.Com.Amazonaws.Kms.Tag) value;
            Amazon.KeyManagementService.Model.Tag converted = new Amazon.KeyManagementService.Model.Tag();
            converted.TagKey = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(concrete.TagKey);
            converted.TagValue =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(concrete.TagValue);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ITag ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(
            Amazon.KeyManagementService.Model.Tag value)
        {
            return new Dafny.Com.Amazonaws.Kms.Tag(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(value.TagKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(value.TagValue));
        }

        public static Amazon.KeyManagementService.DataKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.DataKeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(
                Amazon.KeyManagementService.DataKeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(
                        (Amazon.KeyManagementService.DataKeySpec) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(
                Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreRequest concrete =
                (Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreRequest) value;
            Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest converted =
                new Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest();
            converted.CustomKeyStoreId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    concrete.CustomKeyStoreId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(
                Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId));
        }

        public static Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(
                Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse) value;
            Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse converted =
                new Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse();
            if (concrete.KeyRotationEnabled.is_Some)
                converted.KeyRotationEnabled =
                    (bool)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(
                        concrete.KeyRotationEnabled);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(
                Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse__M18_KeyRotationEnabled(
                    value.KeyRotationEnabled));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_GrantNameType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M8_TagValue(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagValueType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType((string) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.KeyUnavailableException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(
                Dafny.Com.Amazonaws.Kms._IKeyUnavailableException value)
        {
            Dafny.Com.Amazonaws.Kms.KeyUnavailableException concrete =
                (Dafny.Com.Amazonaws.Kms.KeyUnavailableException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.KeyUnavailableException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IKeyUnavailableException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_KeyUnavailableException(
                Amazon.KeyManagementService.Model.KeyUnavailableException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.KeyUnavailableException(message);
        }

        public static Amazon.KeyManagementService.Model.ListAliasesRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(
                Dafny.Com.Amazonaws.Kms._IListAliasesRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ListAliasesRequest concrete = (Dafny.Com.Amazonaws.Kms.ListAliasesRequest) value;
            Amazon.KeyManagementService.Model.ListAliasesRequest converted =
                new Amazon.KeyManagementService.Model.ListAliasesRequest();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(concrete.KeyId);
            if (concrete.Limit.is_Some)
                converted.Limit =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(concrete.Limit);
            if (concrete.Marker.is_Some)
                converted.Marker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(concrete.Marker);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListAliasesRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(
                Amazon.KeyManagementService.Model.ListAliasesRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListAliasesRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M5_Limit(value.Limit),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(value.Marker));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value);
        }

        public static Amazon.KeyManagementService.GrantOperation
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(Dafny.Com.Amazonaws.Kms._IGrantOperation value)
        {
            if (value.is_Decrypt) return Amazon.KeyManagementService.GrantOperation.Decrypt;
            if (value.is_Encrypt) return Amazon.KeyManagementService.GrantOperation.Encrypt;
            if (value.is_GenerateDataKey) return Amazon.KeyManagementService.GrantOperation.GenerateDataKey;
            if (value.is_GenerateDataKeyWithoutPlaintext)
                return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyWithoutPlaintext;
            if (value.is_ReEncryptFrom) return Amazon.KeyManagementService.GrantOperation.ReEncryptFrom;
            if (value.is_ReEncryptTo) return Amazon.KeyManagementService.GrantOperation.ReEncryptTo;
            if (value.is_Sign) return Amazon.KeyManagementService.GrantOperation.Sign;
            if (value.is_Verify) return Amazon.KeyManagementService.GrantOperation.Verify;
            if (value.is_GetPublicKey) return Amazon.KeyManagementService.GrantOperation.GetPublicKey;
            if (value.is_CreateGrant) return Amazon.KeyManagementService.GrantOperation.CreateGrant;
            if (value.is_RetireGrant) return Amazon.KeyManagementService.GrantOperation.RetireGrant;
            if (value.is_DescribeKey) return Amazon.KeyManagementService.GrantOperation.DescribeKey;
            if (value.is_GenerateDataKeyPair) return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPair;
            if (value.is_GenerateDataKeyPairWithoutPlaintext)
                return Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPairWithoutPlaintext;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.GrantOperation value");
        }

        public static Dafny.Com.Amazonaws.Kms._IGrantOperation ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(
            Amazon.KeyManagementService.GrantOperation value)
        {
            if (Amazon.KeyManagementService.GrantOperation.Decrypt.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_Decrypt();
            if (Amazon.KeyManagementService.GrantOperation.Encrypt.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_Encrypt();
            if (Amazon.KeyManagementService.GrantOperation.GenerateDataKey.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_GenerateDataKey();
            if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyWithoutPlaintext.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_GenerateDataKeyWithoutPlaintext();
            if (Amazon.KeyManagementService.GrantOperation.ReEncryptFrom.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_ReEncryptFrom();
            if (Amazon.KeyManagementService.GrantOperation.ReEncryptTo.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_ReEncryptTo();
            if (Amazon.KeyManagementService.GrantOperation.Sign.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_Sign();
            if (Amazon.KeyManagementService.GrantOperation.Verify.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_Verify();
            if (Amazon.KeyManagementService.GrantOperation.GetPublicKey.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_GetPublicKey();
            if (Amazon.KeyManagementService.GrantOperation.CreateGrant.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_CreateGrant();
            if (Amazon.KeyManagementService.GrantOperation.RetireGrant.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_RetireGrant();
            if (Amazon.KeyManagementService.GrantOperation.DescribeKey.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_DescribeKey();
            if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPair.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_GenerateDataKeyPair();
            if (Amazon.KeyManagementService.GrantOperation.GenerateDataKeyPairWithoutPlaintext.Equals(value))
                return Dafny.Com.Amazonaws.Kms.GrantOperation.create_GenerateDataKeyPairWithoutPlaintext();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.GrantOperation value");
        }

        public static Amazon.KeyManagementService.MessageType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMessageType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.MessageType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMessageType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(
                Amazon.KeyManagementService.MessageType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMessageType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMessageType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(
                        (Amazon.KeyManagementService.MessageType) value));
        }

        public static Amazon.KeyManagementService.Model.GetKeyPolicyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(
                Dafny.Com.Amazonaws.Kms._IGetKeyPolicyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GetKeyPolicyRequest concrete = (Dafny.Com.Amazonaws.Kms.GetKeyPolicyRequest) value;
            Amazon.KeyManagementService.Model.GetKeyPolicyRequest converted =
                new Amazon.KeyManagementService.Model.GetKeyPolicyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(concrete.KeyId);
            converted.PolicyName =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(
                    concrete.PolicyName);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetKeyPolicyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(
                Amazon.KeyManagementService.Model.GetKeyPolicyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetKeyPolicyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M10_PolicyName(value.PolicyName));
        }

        public static bool FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(bool value)
        {
            return value;
        }

        public static bool ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(bool value)
        {
            return value;
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.Model.ImportKeyMaterialRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(
                Dafny.Com.Amazonaws.Kms._IImportKeyMaterialRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ImportKeyMaterialRequest concrete =
                (Dafny.Com.Amazonaws.Kms.ImportKeyMaterialRequest) value;
            Amazon.KeyManagementService.Model.ImportKeyMaterialRequest converted =
                new Amazon.KeyManagementService.Model.ImportKeyMaterialRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(concrete.KeyId);
            converted.ImportToken =
                (System.IO.MemoryStream)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(
                    concrete.ImportToken);
            converted.EncryptedKeyMaterial =
                (System.IO.MemoryStream)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(
                    concrete.EncryptedKeyMaterial);
            if (concrete.ValidTo.is_Some)
                converted.ValidTo =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(
                        concrete.ValidTo);
            if (concrete.ExpirationModel.is_Some)
                converted.ExpirationModel =
                    (Amazon.KeyManagementService.ExpirationModelType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(
                        concrete.ExpirationModel);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IImportKeyMaterialRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(
                Amazon.KeyManagementService.Model.ImportKeyMaterialRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ImportKeyMaterialRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M11_ImportToken(value.ImportToken),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M20_EncryptedKeyMaterial(
                    value.EncryptedKeyMaterial),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M7_ValidTo(value.ValidTo),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(
                    value.ExpirationModel));
        }

        public static Amazon.KeyManagementService.Model.ReplicateKeyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(
                Dafny.Com.Amazonaws.Kms._IReplicateKeyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse
                concrete = (Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse) value;
            Amazon.KeyManagementService.Model.ReplicateKeyResponse converted =
                new Amazon.KeyManagementService.Model.ReplicateKeyResponse();
            if (concrete.ReplicaKeyMetadata.is_Some)
                converted.ReplicaKeyMetadata =
                    (Amazon.KeyManagementService.Model.KeyMetadata)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(
                        concrete.ReplicaKeyMetadata);
            if (concrete.ReplicaPolicy.is_Some)
                converted.ReplicaPolicy =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(
                        concrete.ReplicaPolicy);
            if (concrete.ReplicaTags.is_Some)
                converted.ReplicaTags =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(
                        concrete.ReplicaTags);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IReplicateKeyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(
                Amazon.KeyManagementService.Model.ReplicateKeyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ReplicateKeyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(
                    value.ReplicaKeyMetadata),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(value.ReplicaPolicy),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(value.ReplicaTags));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType((string) value));
        }

        public static Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(
                Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreRequest concrete =
                (Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreRequest) value;
            Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest converted =
                new Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest();
            converted.CustomKeyStoreId =
                (string)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    concrete.CustomKeyStoreId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(
                Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.DescribeKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(
                Dafny.Com.Amazonaws.Kms._IDescribeKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DescribeKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.DescribeKeyRequest) value;
            Amazon.KeyManagementService.Model.DescribeKeyRequest converted =
                new Amazon.KeyManagementService.Model.DescribeKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(concrete.KeyId);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDescribeKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(
                Amazon.KeyManagementService.Model.DescribeKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DescribeKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest__M11_GrantTokens(value.GrantTokens));
        }

        public static Amazon.KeyManagementService.KeyUsageType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyUsageType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(
                Amazon.KeyManagementService.KeyUsageType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(
                        (Amazon.KeyManagementService.KeyUsageType) value));
        }

        public static Amazon.KeyManagementService.Model.DisabledException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(
                Dafny.Com.Amazonaws.Kms._IDisabledException value)
        {
            Dafny.Com.Amazonaws.Kms.DisabledException concrete = (Dafny.Com.Amazonaws.Kms.DisabledException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.DisabledException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IDisabledException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisabledException(
                Amazon.KeyManagementService.Model.DisabledException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.DisabledException(message);
        }

        public static Amazon.KeyManagementService.Model.AliasListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(Dafny.Com.Amazonaws.Kms._IAliasListEntry value)
        {
            Dafny.Com.Amazonaws.Kms.AliasListEntry concrete = (Dafny.Com.Amazonaws.Kms.AliasListEntry) value;
            Amazon.KeyManagementService.Model.AliasListEntry converted =
                new Amazon.KeyManagementService.Model.AliasListEntry();
            if (concrete.AliasName.is_Some)
                converted.AliasName =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(
                        concrete.AliasName);
            if (concrete.AliasArn.is_Some)
                converted.AliasArn =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(concrete.AliasArn);
            if (concrete.TargetKeyId.is_Some)
                converted.TargetKeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(
                        concrete.TargetKeyId);
            if (concrete.CreationDate.is_Some)
                converted.CreationDate =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(
                        concrete.CreationDate);
            if (concrete.LastUpdatedDate.is_Some)
                converted.LastUpdatedDate =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(
                        concrete.LastUpdatedDate);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IAliasListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(
            Amazon.KeyManagementService.Model.AliasListEntry value)
        {
            return new Dafny.Com.Amazonaws.Kms.AliasListEntry(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M9_AliasName(value.AliasName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M8_AliasArn(value.AliasArn),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M11_TargetKeyId(value.TargetKeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M12_CreationDate(value.CreationDate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(value.LastUpdatedDate));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static Amazon.KeyManagementService.OriginType FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(
            Dafny.Com.Amazonaws.Kms._IOriginType value)
        {
            if (value.is_AWS__KMS) return Amazon.KeyManagementService.OriginType.AWS_KMS;
            if (value.is_EXTERNAL) return Amazon.KeyManagementService.OriginType.EXTERNAL;
            if (value.is_AWS__CLOUDHSM) return Amazon.KeyManagementService.OriginType.AWS_CLOUDHSM;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.OriginType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IOriginType ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(
            Amazon.KeyManagementService.OriginType value)
        {
            if (Amazon.KeyManagementService.OriginType.AWS_KMS.Equals(value))
                return Dafny.Com.Amazonaws.Kms.OriginType.create_AWS__KMS();
            if (Amazon.KeyManagementService.OriginType.EXTERNAL.Equals(value))
                return Dafny.Com.Amazonaws.Kms.OriginType.create_EXTERNAL();
            if (Amazon.KeyManagementService.OriginType.AWS_CLOUDHSM.Equals(value))
                return Dafny.Com.Amazonaws.Kms.OriginType.create_AWS__CLOUDHSM();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.OriginType value");
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KeyStorePasswordType((string) value));
        }

        public static Amazon.KeyManagementService.DataKeyPairSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec value)
        {
            if (value.is_RSA__2048) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_2048;
            if (value.is_RSA__3072) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_3072;
            if (value.is_RSA__4096) return Amazon.KeyManagementService.DataKeyPairSpec.RSA_4096;
            if (value.is_ECC__NIST__P256) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P256;
            if (value.is_ECC__NIST__P384) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P384;
            if (value.is_ECC__NIST__P521) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P521;
            if (value.is_ECC__SECG__P256K1) return Amazon.KeyManagementService.DataKeyPairSpec.ECC_SECG_P256K1;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeyPairSpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(Amazon.KeyManagementService.DataKeyPairSpec value)
        {
            if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_2048.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_RSA__2048();
            if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_3072.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_RSA__3072();
            if (Amazon.KeyManagementService.DataKeyPairSpec.RSA_4096.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_RSA__4096();
            if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_ECC__NIST__P256();
            if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_ECC__NIST__P384();
            if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_NIST_P521.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_ECC__NIST__P521();
            if (Amazon.KeyManagementService.DataKeyPairSpec.ECC_SECG_P256K1.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeyPairSpec.create_ECC__SECG__P256K1();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeyPairSpec value");
        }

        public static Amazon.KeyManagementService.Model.MultiRegionConfiguration
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.MultiRegionConfiguration) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(
                Amazon.KeyManagementService.Model.MultiRegionConfiguration value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration(
                        (Amazon.KeyManagementService.Model.MultiRegionConfiguration) value));
        }

        public static Amazon.KeyManagementService.Model.CloudHsmClusterInUseException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(
                Dafny.Com.Amazonaws.Kms._ICloudHsmClusterInUseException value)
        {
            Dafny.Com.Amazonaws.Kms.CloudHsmClusterInUseException concrete =
                (Dafny.Com.Amazonaws.Kms.CloudHsmClusterInUseException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CloudHsmClusterInUseException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICloudHsmClusterInUseException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_CloudHsmClusterInUseException(
                Amazon.KeyManagementService.Model.CloudHsmClusterInUseException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CloudHsmClusterInUseException(message);
        }

        public static Amazon.KeyManagementService.Model.UpdateAliasRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(
                Dafny.Com.Amazonaws.Kms._IUpdateAliasRequest value)
        {
            Dafny.Com.Amazonaws.Kms.UpdateAliasRequest concrete = (Dafny.Com.Amazonaws.Kms.UpdateAliasRequest) value;
            Amazon.KeyManagementService.Model.UpdateAliasRequest converted =
                new Amazon.KeyManagementService.Model.UpdateAliasRequest();
            converted.AliasName =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(
                    concrete.AliasName);
            converted.TargetKeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(
                    concrete.TargetKeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUpdateAliasRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(
                Amazon.KeyManagementService.Model.UpdateAliasRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.UpdateAliasRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M9_AliasName(value.AliasName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(value.TargetKeyId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag__M6_TagKey(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(
            Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(
            System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S44_CloudHsmClusterInvalidConfigurationException__M7_message(
                string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.Model.MultiRegionKey
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionKey> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.MultiRegionKey) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(
                Amazon.KeyManagementService.Model.MultiRegionKey value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(
                        (Amazon.KeyManagementService.Model.MultiRegionKey) value));
        }

        public static Amazon.KeyManagementService.Model.CreateKeyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(
                Dafny.Com.Amazonaws.Kms._ICreateKeyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.CreateKeyResponse concrete = (Dafny.Com.Amazonaws.Kms.CreateKeyResponse) value;
            Amazon.KeyManagementService.Model.CreateKeyResponse converted =
                new Amazon.KeyManagementService.Model.CreateKeyResponse();
            if (concrete.KeyMetadata.is_Some)
                converted.KeyMetadata =
                    (Amazon.KeyManagementService.Model.KeyMetadata)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(
                        concrete.KeyMetadata);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateKeyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(
                Amazon.KeyManagementService.Model.CreateKeyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateKeyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse__M11_KeyMetadata(value.KeyMetadata));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static Amazon.KeyManagementService.WrappingKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(Dafny.Com.Amazonaws.Kms._IWrappingKeySpec value)
        {
            if (value.is_RSA__2048) return Amazon.KeyManagementService.WrappingKeySpec.RSA_2048;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.WrappingKeySpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IWrappingKeySpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_WrappingKeySpec(Amazon.KeyManagementService.WrappingKeySpec value)
        {
            if (Amazon.KeyManagementService.WrappingKeySpec.RSA_2048.Equals(value))
                return Dafny.Com.Amazonaws.Kms.WrappingKeySpec.create();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.WrappingKeySpec value");
        }

        public static Amazon.KeyManagementService.Model.ListKeyPoliciesRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(
                Dafny.Com.Amazonaws.Kms._IListKeyPoliciesRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ListKeyPoliciesRequest concrete =
                (Dafny.Com.Amazonaws.Kms.ListKeyPoliciesRequest) value;
            Amazon.KeyManagementService.Model.ListKeyPoliciesRequest converted =
                new Amazon.KeyManagementService.Model.ListKeyPoliciesRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(concrete.KeyId);
            if (concrete.Limit.is_Some)
                converted.Limit =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(concrete.Limit);
            if (concrete.Marker.is_Some)
                converted.Marker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(
                        concrete.Marker);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListKeyPoliciesRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(
                Amazon.KeyManagementService.Model.ListKeyPoliciesRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListKeyPoliciesRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(value.Limit),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(value.Marker));
        }

        public static Amazon.KeyManagementService.KeyState FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(
            Dafny.Com.Amazonaws.Kms._IKeyState value)
        {
            if (value.is_Creating) return Amazon.KeyManagementService.KeyState.Creating;
            if (value.is_Enabled) return Amazon.KeyManagementService.KeyState.Enabled;
            if (value.is_Disabled) return Amazon.KeyManagementService.KeyState.Disabled;
            if (value.is_PendingDeletion) return Amazon.KeyManagementService.KeyState.PendingDeletion;
            if (value.is_PendingImport) return Amazon.KeyManagementService.KeyState.PendingImport;
            if (value.is_PendingReplicaDeletion) return Amazon.KeyManagementService.KeyState.PendingReplicaDeletion;
            if (value.is_Unavailable) return Amazon.KeyManagementService.KeyState.Unavailable;
            if (value.is_Updating) return Amazon.KeyManagementService.KeyState.Updating;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyState value");
        }

        public static Dafny.Com.Amazonaws.Kms._IKeyState ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(
            Amazon.KeyManagementService.KeyState value)
        {
            if (Amazon.KeyManagementService.KeyState.Creating.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_Creating();
            if (Amazon.KeyManagementService.KeyState.Enabled.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_Enabled();
            if (Amazon.KeyManagementService.KeyState.Disabled.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_Disabled();
            if (Amazon.KeyManagementService.KeyState.PendingDeletion.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_PendingDeletion();
            if (Amazon.KeyManagementService.KeyState.PendingImport.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_PendingImport();
            if (Amazon.KeyManagementService.KeyState.PendingReplicaDeletion.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_PendingReplicaDeletion();
            if (Amazon.KeyManagementService.KeyState.Unavailable.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_Unavailable();
            if (Amazon.KeyManagementService.KeyState.Updating.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyState.create_Updating();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyState value");
        }

        public static Amazon.KeyManagementService.Model.AliasListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member(
                Dafny.Com.Amazonaws.Kms._IAliasListEntry value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IAliasListEntry
            ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member(
                Amazon.KeyManagementService.Model.AliasListEntry value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry(value);
        }

        public static System.DateTime FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(Dafny.ISequence<char> value)
        {
            System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
            string timestampString = new string(value.Elements);
            return System.DateTime.ParseExact(timestampString, "s", culture);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(System.DateTime value)
        {
            System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
            string timestampString = value.ToString("s", culture);
            return Dafny.Sequence<char>.FromString(timestampString);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.TagException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(Dafny.Com.Amazonaws.Kms._ITagException value)
        {
            Dafny.Com.Amazonaws.Kms.TagException concrete = (Dafny.Com.Amazonaws.Kms.TagException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.TagException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ITagException ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException(
            Amazon.KeyManagementService.Model.TagException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.TagException(message);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(
                Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(value);
        }

        public static Dafny.ISequence<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M7_TagKeys(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value);
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.KeyState
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyState> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyState) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyState>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(
                Amazon.KeyManagementService.KeyState value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyState>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyState>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState((Amazon.KeyManagementService.KeyState) value));
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse();
            if (concrete.PrivateKeyCiphertextBlob.is_Some)
                converted.PrivateKeyCiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(
                        concrete.PrivateKeyCiphertextBlob);
            if (concrete.PrivateKeyPlaintext.is_Some)
                converted.PrivateKeyPlaintext =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(
                        concrete.PrivateKeyPlaintext);
            if (concrete.PublicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(
                        concrete.PublicKey);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(
                        concrete.KeyId);
            if (concrete.KeyPairSpec.is_Some)
                converted.KeyPairSpec =
                    (Amazon.KeyManagementService.DataKeyPairSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(
                        concrete.KeyPairSpec);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(
                Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(
                    value.PrivateKeyCiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(
                    value.PrivateKeyPlaintext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(value.PublicKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(
                    value.KeyPairSpec));
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyResponse converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyResponse();
            if (concrete.CiphertextBlob.is_Some)
                converted.CiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(
                        concrete.CiphertextBlob);
            if (concrete.Plaintext.is_Some)
                converted.Plaintext =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(
                        concrete.Plaintext);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(
                        concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(
                Amazon.KeyManagementService.Model.GenerateDataKeyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(
                    value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M9_Plaintext(value.Plaintext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(value.KeyId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(
            string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(
                Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusRequest) value;
            Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest converted =
                new Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(
                    concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetKeyRotationStatusRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(
                Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetKeyRotationStatusRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest__M5_KeyId(value.KeyId));
        }

        public static Amazon.KeyManagementService.KeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(Amazon.KeyManagementService.KeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
        }

        public static bool FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(bool value)
        {
            return value;
        }

        public static bool ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(bool value)
        {
            return value;
        }

        public static Amazon.KeyManagementService.Model.MultiRegionConfiguration
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration(
                Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration value)
        {
            Dafny.Com.Amazonaws.Kms.MultiRegionConfiguration concrete =
                (Dafny.Com.Amazonaws.Kms.MultiRegionConfiguration) value;
            Amazon.KeyManagementService.Model.MultiRegionConfiguration converted =
                new Amazon.KeyManagementService.Model.MultiRegionConfiguration();
            if (concrete.MultiRegionKeyType.is_Some)
                converted.MultiRegionKeyType =
                    (Amazon.KeyManagementService.MultiRegionKeyType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(
                        concrete.MultiRegionKeyType);
            if (concrete.PrimaryKey.is_Some)
                converted.PrimaryKey =
                    (Amazon.KeyManagementService.Model.MultiRegionKey)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(
                        concrete.PrimaryKey);
            if (concrete.ReplicaKeys.is_Some)
                converted.ReplicaKeys =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(
                        concrete.ReplicaKeys);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IMultiRegionConfiguration
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration(
                Amazon.KeyManagementService.Model.MultiRegionConfiguration value)
        {
            return new Dafny.Com.Amazonaws.Kms.MultiRegionConfiguration(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M18_MultiRegionKeyType(
                    value.MultiRegionKeyType),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M10_PrimaryKey(value.PrimaryKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(value.ReplicaKeys));
        }

        public static Amazon.KeyManagementService.Model.GrantListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(Dafny.Com.Amazonaws.Kms._IGrantListEntry value)
        {
            Dafny.Com.Amazonaws.Kms.GrantListEntry concrete = (Dafny.Com.Amazonaws.Kms.GrantListEntry) value;
            Amazon.KeyManagementService.Model.GrantListEntry converted =
                new Amazon.KeyManagementService.Model.GrantListEntry();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(concrete.KeyId);
            if (concrete.GrantId.is_Some)
                converted.GrantId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(concrete.GrantId);
            if (concrete.Name.is_Some)
                converted.Name =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(concrete.Name);
            if (concrete.CreationDate.is_Some)
                converted.CreationDate =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(
                        concrete.CreationDate);
            if (concrete.GranteePrincipal.is_Some)
                converted.GranteePrincipal =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(
                        concrete.GranteePrincipal);
            if (concrete.RetiringPrincipal.is_Some)
                converted.RetiringPrincipal =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(
                        concrete.RetiringPrincipal);
            if (concrete.IssuingAccount.is_Some)
                converted.IssuingAccount =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(
                        concrete.IssuingAccount);
            if (concrete.Operations.is_Some)
                converted.Operations =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(concrete.Operations);
            if (concrete.Constraints.is_Some)
                converted.Constraints =
                    (Amazon.KeyManagementService.Model.GrantConstraints)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(concrete.Constraints);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGrantListEntry ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry(
            Amazon.KeyManagementService.Model.GrantListEntry value)
        {
            return new Dafny.Com.Amazonaws.Kms.GrantListEntry(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M7_GrantId(value.GrantId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M4_Name(value.Name),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(value.CreationDate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(value.GranteePrincipal),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M17_RetiringPrincipal(
                    value.RetiringPrincipal),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M14_IssuingAccount(value.IssuingAccount),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(value.Operations),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(value.Constraints));
        }

        public static Amazon.KeyManagementService.Model.DecryptRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(Dafny.Com.Amazonaws.Kms._IDecryptRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DecryptRequest concrete = (Dafny.Com.Amazonaws.Kms.DecryptRequest) value;
            Amazon.KeyManagementService.Model.DecryptRequest converted =
                new Amazon.KeyManagementService.Model.DecryptRequest();
            converted.CiphertextBlob =
                (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(
                    concrete.CiphertextBlob);
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(concrete.GrantTokens);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(concrete.KeyId);
            if (concrete.EncryptionAlgorithm.is_Some)
                converted.EncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(
                        concrete.EncryptionAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDecryptRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(
            Amazon.KeyManagementService.Model.DecryptRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DecryptRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M14_CiphertextBlob(value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(value.GrantTokens),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(
                    value.EncryptionAlgorithm));
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member).ToArray());
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.DescribeKeyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(
                Dafny.Com.Amazonaws.Kms._IDescribeKeyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.DescribeKeyResponse concrete = (Dafny.Com.Amazonaws.Kms.DescribeKeyResponse) value;
            Amazon.KeyManagementService.Model.DescribeKeyResponse converted =
                new Amazon.KeyManagementService.Model.DescribeKeyResponse();
            if (concrete.KeyMetadata.is_Some)
                converted.KeyMetadata =
                    (Amazon.KeyManagementService.Model.KeyMetadata)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(
                        concrete.KeyMetadata);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDescribeKeyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(
                Amazon.KeyManagementService.Model.DescribeKeyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.DescribeKeyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(value.KeyMetadata));
        }

        public static Amazon.KeyManagementService.Model.InvalidCiphertextException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(
                Dafny.Com.Amazonaws.Kms._IInvalidCiphertextException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidCiphertextException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidCiphertextException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidCiphertextException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidCiphertextException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidCiphertextException(
                Amazon.KeyManagementService.Model.InvalidCiphertextException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidCiphertextException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.ExpirationModelType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(
                Dafny.Com.Amazonaws.Kms._IExpirationModelType value)
        {
            if (value.is_KEY__MATERIAL__EXPIRES)
                return Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_EXPIRES;
            if (value.is_KEY__MATERIAL__DOES__NOT__EXPIRE)
                return Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ExpirationModelType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IExpirationModelType
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(
                Amazon.KeyManagementService.ExpirationModelType value)
        {
            if (Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_EXPIRES.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ExpirationModelType.create_KEY__MATERIAL__EXPIRES();
            if (Amazon.KeyManagementService.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ExpirationModelType.create_KEY__MATERIAL__DOES__NOT__EXPIRE();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ExpirationModelType value");
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M3_Arn(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(
            string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(
                Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreResponse value)
        {
            Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse concrete =
                (Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse) value;
            Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse converted =
                new Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse();
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(
                Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreResponse();
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.KeyMetadata
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.KeyMetadata) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse__M11_KeyMetadata(
                Amazon.KeyManagementService.Model.KeyMetadata value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(
                        (Amazon.KeyManagementService.Model.KeyMetadata) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(value);
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M12_CreationDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static Amazon.KeyManagementService.Model.GetParametersForImportResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(
                Dafny.Com.Amazonaws.Kms._IGetParametersForImportResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse) value;
            Amazon.KeyManagementService.Model.GetParametersForImportResponse converted =
                new Amazon.KeyManagementService.Model.GetParametersForImportResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(
                        concrete.KeyId);
            if (concrete.ImportToken.is_Some)
                converted.ImportToken =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(
                        concrete.ImportToken);
            if (concrete.PublicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(
                        concrete.PublicKey);
            if (concrete.ParametersValidTo.is_Some)
                converted.ParametersValidTo =
                    (System.DateTime)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(
                        concrete.ParametersValidTo);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetParametersForImportResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(
                Amazon.KeyManagementService.Model.GetParametersForImportResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetParametersForImportResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M11_ImportToken(
                    value.ImportToken),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M9_PublicKey(value.PublicKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(
                    value.ParametersValidTo));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return new System.Collections.Generic.List<string>(value.Elements
                .Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member)
                .Select<Amazon.KeyManagementService.EncryptionAlgorithmSpec, string>(x => x));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(
                System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.FromArray(value
                .Select<string, Amazon.KeyManagementService.EncryptionAlgorithmSpec>(x => x)
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member).ToArray());
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M13_ReplicaPolicy(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M10_GrantToken(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.ListResourceTagsResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(
                Dafny.Com.Amazonaws.Kms._IListResourceTagsResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse concrete =
                (Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse) value;
            Amazon.KeyManagementService.Model.ListResourceTagsResponse converted =
                new Amazon.KeyManagementService.Model.ListResourceTagsResponse();
            if (concrete.Tags.is_Some)
                converted.Tags =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(concrete.Tags);
            if (concrete.NextMarker.is_Some)
                converted.NextMarker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(
                        concrete.NextMarker);
            if (concrete.Truncated.is_Some)
                converted.Truncated =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(
                        concrete.Truncated);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListResourceTagsResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(
                Amazon.KeyManagementService.Model.ListResourceTagsResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListResourceTagsResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(value.Tags),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(value.NextMarker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(value.Truncated));
        }

        public static Amazon.KeyManagementService.Model.GrantConstraints
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IGrantConstraints> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.GrantConstraints) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IGrantConstraints>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(
                Amazon.KeyManagementService.Model.GrantConstraints value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IGrantConstraints>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IGrantConstraints>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(
                        (Amazon.KeyManagementService.Model.GrantConstraints) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse();
            if (concrete.PrivateKeyCiphertextBlob.is_Some)
                converted.PrivateKeyCiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(
                        concrete.PrivateKeyCiphertextBlob);
            if (concrete.PublicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(
                        concrete.PublicKey);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(
                        concrete.KeyId);
            if (concrete.KeyPairSpec.is_Some)
                converted.KeyPairSpec =
                    (Amazon.KeyManagementService.DataKeyPairSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(
                        concrete.KeyPairSpec);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairWithoutPlaintextResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(
                Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairWithoutPlaintextResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(
                    value.PrivateKeyCiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(
                    value.PublicKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(
                    value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(
                    value.KeyPairSpec));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M5_KeyId(
                string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(
                Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreResponse value)
        {
            Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse concrete =
                (Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse) value;
            Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse converted =
                new Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse();
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(
                Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreResponse();
        }

        public static Amazon.KeyManagementService.Model.TagResourceRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(
                Dafny.Com.Amazonaws.Kms._ITagResourceRequest value)
        {
            Dafny.Com.Amazonaws.Kms.TagResourceRequest concrete = (Dafny.Com.Amazonaws.Kms.TagResourceRequest) value;
            Amazon.KeyManagementService.Model.TagResourceRequest converted =
                new Amazon.KeyManagementService.Model.TagResourceRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(concrete.KeyId);
            converted.Tags =
                (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(concrete.Tags);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ITagResourceRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(
                Amazon.KeyManagementService.Model.TagResourceRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.TagResourceRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest__M4_Tags(value.Tags));
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextRequest) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(
                    concrete.KeyId);
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            if (concrete.KeySpec.is_Some)
                converted.KeySpec =
                    (Amazon.KeyManagementService.DataKeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(
                        concrete.KeySpec);
            if (concrete.NumberOfBytes.is_Some)
                converted.NumberOfBytes =
                    (int)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(
                        concrete.NumberOfBytes);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(
                Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M7_KeySpec(
                    value.KeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(
                    value.NumberOfBytes),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M11_GrantTokens(
                    value.GrantTokens));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
                    .create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
                    .create_Some(
                        ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(
                            (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_LimitExceededException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static Amazon.KeyManagementService.Model.IncorrectKeyMaterialException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(
                Dafny.Com.Amazonaws.Kms._IIncorrectKeyMaterialException value)
        {
            Dafny.Com.Amazonaws.Kms.IncorrectKeyMaterialException concrete =
                (Dafny.Com.Amazonaws.Kms.IncorrectKeyMaterialException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.IncorrectKeyMaterialException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IIncorrectKeyMaterialException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectKeyMaterialException(
                Amazon.KeyManagementService.Model.IncorrectKeyMaterialException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.IncorrectKeyMaterialException(message);
        }

        public static Amazon.KeyManagementService.Model.MalformedPolicyDocumentException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(
                Dafny.Com.Amazonaws.Kms._IMalformedPolicyDocumentException value)
        {
            Dafny.Com.Amazonaws.Kms.MalformedPolicyDocumentException concrete =
                (Dafny.Com.Amazonaws.Kms.MalformedPolicyDocumentException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.MalformedPolicyDocumentException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IMalformedPolicyDocumentException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_MalformedPolicyDocumentException(
                Amazon.KeyManagementService.Model.MalformedPolicyDocumentException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.MalformedPolicyDocumentException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
        }

        public static Amazon.KeyManagementService.GrantOperation
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member(
                Dafny.Com.Amazonaws.Kms._IGrantOperation value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IGrantOperation
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member(
                Amazon.KeyManagementService.GrantOperation value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantOperation(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(
            Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(
            System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static Amazon.KeyManagementService.Model.GrantConstraints
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(
                Dafny.Com.Amazonaws.Kms._IGrantConstraints value)
        {
            Dafny.Com.Amazonaws.Kms.GrantConstraints concrete = (Dafny.Com.Amazonaws.Kms.GrantConstraints) value;
            Amazon.KeyManagementService.Model.GrantConstraints converted =
                new Amazon.KeyManagementService.Model.GrantConstraints();
            if (concrete.EncryptionContextSubset.is_Some)
                converted.EncryptionContextSubset =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(
                        concrete.EncryptionContextSubset);
            if (concrete.EncryptionContextEquals.is_Some)
                converted.EncryptionContextEquals =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(
                        concrete.EncryptionContextEquals);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGrantConstraints
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(
                Amazon.KeyManagementService.Model.GrantConstraints value)
        {
            return new Dafny.Com.Amazonaws.Kms.GrantConstraints(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(
                    value.EncryptionContextSubset),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(
                    value.EncryptionContextEquals));
        }

        public static Amazon.KeyManagementService.CustomerMasterKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(
                Amazon.KeyManagementService.CustomerMasterKeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(
                        (Amazon.KeyManagementService.CustomerMasterKeySpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.Model.MultiRegionKey
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member(
                Dafny.Com.Amazonaws.Kms._IMultiRegionKey value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IMultiRegionKey
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member(
                Amazon.KeyManagementService.Model.MultiRegionKey value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey(value);
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoreInvalidStateException value)
        {
            Dafny.Com.Amazonaws.Kms.CustomKeyStoreInvalidStateException concrete =
                (Dafny.Com.Amazonaws.Kms.CustomKeyStoreInvalidStateException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoreInvalidStateException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S35_CustomKeyStoreInvalidStateException(
                Amazon.KeyManagementService.Model.CustomKeyStoreInvalidStateException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CustomKeyStoreInvalidStateException(message);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse__M9_Plaintext(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest__M7_GrantId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_EncryptionContextKey(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M24_PrivateKeyCiphertextBlob(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.DataKeyPairSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.DataKeyPairSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M11_KeyPairSpec(
                Amazon.KeyManagementService.DataKeyPairSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(
                        (Amazon.KeyManagementService.DataKeyPairSpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyType(value);
        }

        public static Amazon.KeyManagementService.Model.InvalidKeyUsageException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(
                Dafny.Com.Amazonaws.Kms._IInvalidKeyUsageException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidKeyUsageException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidKeyUsageException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidKeyUsageException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidKeyUsageException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_InvalidKeyUsageException(
                Amazon.KeyManagementService.Model.InvalidKeyUsageException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidKeyUsageException(message);
        }

        public static Amazon.KeyManagementService.KeyManagerType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyManagerType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyManagerType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyManagerType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(
                Amazon.KeyManagementService.KeyManagerType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyManagerType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyManagerType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType(
                        (Amazon.KeyManagementService.KeyManagerType) value));
        }

        public static Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(
                Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse concrete =
                (Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse) value;
            Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse converted =
                new Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(
                        concrete.KeyId);
            if (concrete.DeletionDate.is_Some)
                converted.DeletionDate =
                    (System.DateTime)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(
                        concrete.DeletionDate);
            if (concrete.KeyState.is_Some)
                converted.KeyState =
                    (Amazon.KeyManagementService.KeyState)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(
                        concrete.KeyState);
            if (concrete.PendingWindowInDays.is_Some)
                converted.PendingWindowInDays =
                    (int)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(
                        concrete.PendingWindowInDays);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IScheduleKeyDeletionResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(
                Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ScheduleKeyDeletionResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(
                    value.DeletionDate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M8_KeyState(value.KeyState),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(
                    value.PendingWindowInDays));
        }

        public static Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(
                Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreRequest concrete =
                (Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreRequest) value;
            Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest converted =
                new Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest();
            converted.CustomKeyStoreId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    concrete.CustomKeyStoreId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDeleteCustomKeyStoreRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(
                Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DeleteCustomKeyStoreRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId));
        }

        public static Amazon.KeyManagementService.Model.InvalidGrantIdException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(
                Dafny.Com.Amazonaws.Kms._IInvalidGrantIdException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidGrantIdException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidGrantIdException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidGrantIdException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidGrantIdException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException(
                Amazon.KeyManagementService.Model.InvalidGrantIdException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidGrantIdException(message);
        }

        public static Amazon.KeyManagementService.Model.GetKeyPolicyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(
                Dafny.Com.Amazonaws.Kms._IGetKeyPolicyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse
                concrete = (Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse) value;
            Amazon.KeyManagementService.Model.GetKeyPolicyResponse converted =
                new Amazon.KeyManagementService.Model.GetKeyPolicyResponse();
            if (concrete.Policy.is_Some)
                converted.Policy =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(
                        concrete.Policy);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetKeyPolicyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(
                Amazon.KeyManagementService.Model.GetKeyPolicyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetKeyPolicyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse__M6_Policy(value.Policy));
        }

        public static Amazon.KeyManagementService.AlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(
                Dafny.Com.Amazonaws.Kms._IAlgorithmSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(
                Amazon.KeyManagementService.AlgorithmSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M9_PublicKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.AlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(Dafny.Com.Amazonaws.Kms._IAlgorithmSpec value)
        {
            if (value.is_RSAES__PKCS1__V1__5) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_PKCS1_V1_5;
            if (value.is_RSAES__OAEP__SHA__1) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_1;
            if (value.is_RSAES__OAEP__SHA__256) return Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_256;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.AlgorithmSpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IAlgorithmSpec ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AlgorithmSpec(
            Amazon.KeyManagementService.AlgorithmSpec value)
        {
            if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_PKCS1_V1_5.Equals(value))
                return Dafny.Com.Amazonaws.Kms.AlgorithmSpec.create_RSAES__PKCS1__V1__5();
            if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_1.Equals(value))
                return Dafny.Com.Amazonaws.Kms.AlgorithmSpec.create_RSAES__OAEP__SHA__1();
            if (Amazon.KeyManagementService.AlgorithmSpec.RSAES_OAEP_SHA_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.AlgorithmSpec.create_RSAES__OAEP__SHA__256();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.AlgorithmSpec value");
        }

        public static Amazon.KeyManagementService.KeyUsageType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyUsageType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(
                Amazon.KeyManagementService.KeyUsageType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(
                        (Amazon.KeyManagementService.KeyUsageType) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse();
            if (concrete.CiphertextBlob.is_Some)
                converted.CiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(
                        concrete.CiphertextBlob);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(
                        concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyWithoutPlaintextResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(
                Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyWithoutPlaintextResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(
                    value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(
                    value.KeyId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest__M16_CustomKeyStoreId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_CustomKeyStoreIdType(value);
        }

        public static Amazon.KeyManagementService.Model.CreateGrantResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(
                Dafny.Com.Amazonaws.Kms._ICreateGrantResponse value)
        {
            Dafny.Com.Amazonaws.Kms.CreateGrantResponse concrete = (Dafny.Com.Amazonaws.Kms.CreateGrantResponse) value;
            Amazon.KeyManagementService.Model.CreateGrantResponse converted =
                new Amazon.KeyManagementService.Model.CreateGrantResponse();
            if (concrete.GrantToken.is_Some)
                converted.GrantToken =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(
                        concrete.GrantToken);
            if (concrete.GrantId.is_Some)
                converted.GrantId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(
                        concrete.GrantId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateGrantResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(
                Amazon.KeyManagementService.Model.CreateGrantResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateGrantResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M10_GrantToken(value.GrantToken),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(value.GrantId));
        }

        public static Amazon.KeyManagementService.DataKeySpec FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(
            Dafny.Com.Amazonaws.Kms._IDataKeySpec value)
        {
            if (value.is_AES__256) return Amazon.KeyManagementService.DataKeySpec.AES_256;
            if (value.is_AES__128) return Amazon.KeyManagementService.DataKeySpec.AES_128;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeySpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._IDataKeySpec ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(
            Amazon.KeyManagementService.DataKeySpec value)
        {
            if (Amazon.KeyManagementService.DataKeySpec.AES_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeySpec.create_AES__256();
            if (Amazon.KeyManagementService.DataKeySpec.AES_128.Equals(value))
                return Dafny.Com.Amazonaws.Kms.DataKeySpec.create_AES__128();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.DataKeySpec value");
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_AWSAccountIdType((string) value));
        }

        public static Amazon.KeyManagementService.ConnectionErrorCodeType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType(
                Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType value)
        {
            if (value.is_INVALID__CREDENTIALS)
                return Amazon.KeyManagementService.ConnectionErrorCodeType.INVALID_CREDENTIALS;
            if (value.is_CLUSTER__NOT__FOUND)
                return Amazon.KeyManagementService.ConnectionErrorCodeType.CLUSTER_NOT_FOUND;
            if (value.is_NETWORK__ERRORS) return Amazon.KeyManagementService.ConnectionErrorCodeType.NETWORK_ERRORS;
            if (value.is_INTERNAL__ERROR) return Amazon.KeyManagementService.ConnectionErrorCodeType.INTERNAL_ERROR;
            if (value.is_INSUFFICIENT__CLOUDHSM__HSMS)
                return Amazon.KeyManagementService.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS;
            if (value.is_USER__LOCKED__OUT) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOCKED_OUT;
            if (value.is_USER__NOT__FOUND) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_NOT_FOUND;
            if (value.is_USER__LOGGED__IN) return Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOGGED_IN;
            if (value.is_SUBNET__NOT__FOUND)
                return Amazon.KeyManagementService.ConnectionErrorCodeType.SUBNET_NOT_FOUND;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionErrorCodeType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType(
                Amazon.KeyManagementService.ConnectionErrorCodeType value)
        {
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.INVALID_CREDENTIALS.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_INVALID__CREDENTIALS();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.CLUSTER_NOT_FOUND.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_CLUSTER__NOT__FOUND();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.NETWORK_ERRORS.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_NETWORK__ERRORS();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.INTERNAL_ERROR.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_INTERNAL__ERROR();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_INSUFFICIENT__CLOUDHSM__HSMS();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOCKED_OUT.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_USER__LOCKED__OUT();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_NOT_FOUND.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_USER__NOT__FOUND();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.USER_LOGGED_IN.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_USER__LOGGED__IN();
            if (Amazon.KeyManagementService.ConnectionErrorCodeType.SUBNET_NOT_FOUND.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionErrorCodeType.create_SUBNET__NOT__FOUND();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionErrorCodeType value");
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>) value));
        }

        public static Amazon.KeyManagementService.Model.ExpiredImportTokenException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(
                Dafny.Com.Amazonaws.Kms._IExpiredImportTokenException value)
        {
            Dafny.Com.Amazonaws.Kms.ExpiredImportTokenException concrete =
                (Dafny.Com.Amazonaws.Kms.ExpiredImportTokenException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.ExpiredImportTokenException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IExpiredImportTokenException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ExpiredImportTokenException(
                Amazon.KeyManagementService.Model.ExpiredImportTokenException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.ExpiredImportTokenException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M14_CiphertextBlob(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.DataKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.DataKeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(
                Amazon.KeyManagementService.DataKeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_DataKeySpec(
                        (Amazon.KeyManagementService.DataKeySpec) value));
        }

        public static Amazon.KeyManagementService.Model.EnableKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(
                Dafny.Com.Amazonaws.Kms._IEnableKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.EnableKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.EnableKeyRequest) value;
            Amazon.KeyManagementService.Model.EnableKeyRequest converted =
                new Amazon.KeyManagementService.Model.EnableKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IEnableKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(
                Amazon.KeyManagementService.Model.EnableKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.EnableKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(value.KeyId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M16_GranteePrincipal(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.EncryptResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(Dafny.Com.Amazonaws.Kms._IEncryptResponse value)
        {
            Dafny.Com.Amazonaws.Kms.EncryptResponse concrete = (Dafny.Com.Amazonaws.Kms.EncryptResponse) value;
            Amazon.KeyManagementService.Model.EncryptResponse converted =
                new Amazon.KeyManagementService.Model.EncryptResponse();
            if (concrete.CiphertextBlob.is_Some)
                converted.CiphertextBlob =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(
                        concrete.CiphertextBlob);
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(concrete.KeyId);
            if (concrete.EncryptionAlgorithm.is_Some)
                converted.EncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(
                        concrete.EncryptionAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IEncryptResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(
                Amazon.KeyManagementService.Model.EncryptResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.EncryptResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M14_CiphertextBlob(value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(
                    value.EncryptionAlgorithm));
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
        }

        public static Amazon.KeyManagementService.Model.GetPublicKeyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(
                Dafny.Com.Amazonaws.Kms._IGetPublicKeyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse
                concrete = (Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse) value;
            Amazon.KeyManagementService.Model.GetPublicKeyResponse converted =
                new Amazon.KeyManagementService.Model.GetPublicKeyResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(concrete.KeyId);
            if (concrete.PublicKey.is_Some)
                converted.PublicKey =
                    (System.IO.MemoryStream)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(concrete.PublicKey);
            if (concrete.CustomerMasterKeySpec.is_Some)
                converted.CustomerMasterKeySpec =
                    (Amazon.KeyManagementService.CustomerMasterKeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(
                        concrete.CustomerMasterKeySpec);
            if (concrete.KeySpec.is_Some)
                converted.KeySpec =
                    (Amazon.KeyManagementService.KeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(concrete.KeySpec);
            if (concrete.KeyUsage.is_Some)
                converted.KeyUsage =
                    (Amazon.KeyManagementService.KeyUsageType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(concrete.KeyUsage);
            if (concrete.EncryptionAlgorithms.is_Some)
                converted.EncryptionAlgorithms =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(
                        concrete.EncryptionAlgorithms);
            if (concrete.SigningAlgorithms.is_Some)
                converted.SigningAlgorithms =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(
                        concrete.SigningAlgorithms);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetPublicKeyResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(
                Amazon.KeyManagementService.Model.GetPublicKeyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetPublicKeyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(value.PublicKey),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(
                    value.CustomerMasterKeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(value.KeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M8_KeyUsage(value.KeyUsage),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(
                    value.EncryptionAlgorithms),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M17_SigningAlgorithms(
                    value.SigningAlgorithms));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M4_Tags(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M24_PrivateKeyCiphertextBlob(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M19_EncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static Amazon.KeyManagementService.DataKeyPairSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.DataKeyPairSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M11_KeyPairSpec(
                Amazon.KeyManagementService.DataKeyPairSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(
                        (Amazon.KeyManagementService.DataKeyPairSpec) value));
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
        }

        public static Amazon.KeyManagementService.KeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M7_KeySpec(
                Amazon.KeyManagementService.KeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S12_TagException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.ConnectionStateType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType(
                Dafny.Com.Amazonaws.Kms._IConnectionStateType value)
        {
            if (value.is_CONNECTED) return Amazon.KeyManagementService.ConnectionStateType.CONNECTED;
            if (value.is_CONNECTING) return Amazon.KeyManagementService.ConnectionStateType.CONNECTING;
            if (value.is_FAILED) return Amazon.KeyManagementService.ConnectionStateType.FAILED;
            if (value.is_DISCONNECTED) return Amazon.KeyManagementService.ConnectionStateType.DISCONNECTED;
            if (value.is_DISCONNECTING) return Amazon.KeyManagementService.ConnectionStateType.DISCONNECTING;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionStateType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IConnectionStateType
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType(
                Amazon.KeyManagementService.ConnectionStateType value)
        {
            if (Amazon.KeyManagementService.ConnectionStateType.CONNECTED.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionStateType.create_CONNECTED();
            if (Amazon.KeyManagementService.ConnectionStateType.CONNECTING.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionStateType.create_CONNECTING();
            if (Amazon.KeyManagementService.ConnectionStateType.FAILED.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionStateType.create_FAILED();
            if (Amazon.KeyManagementService.ConnectionStateType.DISCONNECTED.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionStateType.create_DISCONNECTED();
            if (Amazon.KeyManagementService.ConnectionStateType.DISCONNECTING.Equals(value))
                return Dafny.Com.Amazonaws.Kms.ConnectionStateType.create_DISCONNECTING();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.ConnectionStateType value");
        }

        public static Amazon.KeyManagementService.Model.DeleteAliasRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(
                Dafny.Com.Amazonaws.Kms._IDeleteAliasRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DeleteAliasRequest concrete = (Dafny.Com.Amazonaws.Kms.DeleteAliasRequest) value;
            Amazon.KeyManagementService.Model.DeleteAliasRequest converted =
                new Amazon.KeyManagementService.Model.DeleteAliasRequest();
            converted.AliasName =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(
                    concrete.AliasName);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDeleteAliasRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(
                Amazon.KeyManagementService.Model.DeleteAliasRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DeleteAliasRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest__M9_AliasName(value.AliasName));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation> value)
        {
            return new System.Collections.Generic.List<string>(value.Elements
                .Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member)
                .Select<Amazon.KeyManagementService.GrantOperation, string>(x => x));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>.FromArray(value
                .Select<string, Amazon.KeyManagementService.GrantOperation>(x => x)
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.Model.UnsupportedOperationException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(
                Dafny.Com.Amazonaws.Kms._IUnsupportedOperationException value)
        {
            Dafny.Com.Amazonaws.Kms.UnsupportedOperationException concrete =
                (Dafny.Com.Amazonaws.Kms.UnsupportedOperationException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.UnsupportedOperationException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IUnsupportedOperationException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException(
                Amazon.KeyManagementService.Model.UnsupportedOperationException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.UnsupportedOperationException(message);
        }

        public static Amazon.KeyManagementService.Model.ListResourceTagsRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(
                Dafny.Com.Amazonaws.Kms._IListResourceTagsRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ListResourceTagsRequest concrete =
                (Dafny.Com.Amazonaws.Kms.ListResourceTagsRequest) value;
            Amazon.KeyManagementService.Model.ListResourceTagsRequest converted =
                new Amazon.KeyManagementService.Model.ListResourceTagsRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(concrete.KeyId);
            if (concrete.Limit.is_Some)
                converted.Limit =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(concrete.Limit);
            if (concrete.Marker.is_Some)
                converted.Marker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(
                        concrete.Marker);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListResourceTagsRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(
                Amazon.KeyManagementService.Model.ListResourceTagsRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListResourceTagsRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(value.Limit),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M6_Marker(value.Marker));
        }

        public static bool?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(
                Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(
                bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoreHasCMKsException value)
        {
            Dafny.Com.Amazonaws.Kms.CustomKeyStoreHasCMKsException concrete =
                (Dafny.Com.Amazonaws.Kms.CustomKeyStoreHasCMKsException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoreHasCMKsException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_CustomKeyStoreHasCMKsException(
                Amazon.KeyManagementService.Model.CustomKeyStoreHasCMKsException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CustomKeyStoreHasCMKsException(message);
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyRequest) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyRequest converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(concrete.KeyId);
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            if (concrete.NumberOfBytes.is_Some)
                converted.NumberOfBytes =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(
                        concrete.NumberOfBytes);
            if (concrete.KeySpec.is_Some)
                converted.KeySpec =
                    (Amazon.KeyManagementService.DataKeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(concrete.KeySpec);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(
                Amazon.KeyManagementService.Model.GenerateDataKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M13_NumberOfBytes(
                    value.NumberOfBytes),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M7_KeySpec(value.KeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(value.GrantTokens));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag> value)
        {
            return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag> ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(
            System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._ITag>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.Model.DisableKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(
                Dafny.Com.Amazonaws.Kms._IDisableKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DisableKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.DisableKeyRequest) value;
            Amazon.KeyManagementService.Model.DisableKeyRequest converted =
                new Amazon.KeyManagementService.Model.DisableKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDisableKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(
                Amazon.KeyManagementService.Model.DisableKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DisableKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(value.KeyId));
        }

        public static Amazon.KeyManagementService.Model.ListGrantsRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(
                Dafny.Com.Amazonaws.Kms._IListGrantsRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ListGrantsRequest concrete = (Dafny.Com.Amazonaws.Kms.ListGrantsRequest) value;
            Amazon.KeyManagementService.Model.ListGrantsRequest converted =
                new Amazon.KeyManagementService.Model.ListGrantsRequest();
            if (concrete.Limit.is_Some)
                converted.Limit =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(concrete.Limit);
            if (concrete.Marker.is_Some)
                converted.Marker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(concrete.Marker);
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(concrete.KeyId);
            if (concrete.GrantId.is_Some)
                converted.GrantId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(
                        concrete.GrantId);
            if (concrete.GranteePrincipal.is_Some)
                converted.GranteePrincipal =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(
                        concrete.GranteePrincipal);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListGrantsRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(
                Amazon.KeyManagementService.Model.ListGrantsRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListGrantsRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_Limit(value.Limit),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(value.Marker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M7_GrantId(value.GrantId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M16_GranteePrincipal(
                    value.GranteePrincipal));
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M11_ReplicaTags(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member(
                Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList__M6_member(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value);
        }

        public static Amazon.KeyManagementService.Model.KMSInvalidStateException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(
                Dafny.Com.Amazonaws.Kms._IKMSInvalidStateException value)
        {
            Dafny.Com.Amazonaws.Kms.KMSInvalidStateException concrete =
                (Dafny.Com.Amazonaws.Kms.KMSInvalidStateException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.KMSInvalidStateException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IKMSInvalidStateException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_KMSInvalidStateException(
                Amazon.KeyManagementService.Model.KMSInvalidStateException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.KMSInvalidStateException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static bool?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S22_EncryptionContextValue(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M10_Operations(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_UnsupportedOperationException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoreNameInUseException value)
        {
            Dafny.Com.Amazonaws.Kms.CustomKeyStoreNameInUseException concrete =
                (Dafny.Com.Amazonaws.Kms.CustomKeyStoreNameInUseException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoreNameInUseException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CustomKeyStoreNameInUseException(
                Amazon.KeyManagementService.Model.CustomKeyStoreNameInUseException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CustomKeyStoreNameInUseException(message);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static Amazon.KeyManagementService.Model.PutKeyPolicyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(
                Dafny.Com.Amazonaws.Kms._IPutKeyPolicyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.PutKeyPolicyRequest concrete = (Dafny.Com.Amazonaws.Kms.PutKeyPolicyRequest) value;
            Amazon.KeyManagementService.Model.PutKeyPolicyRequest converted =
                new Amazon.KeyManagementService.Model.PutKeyPolicyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(concrete.KeyId);
            converted.PolicyName =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(
                    concrete.PolicyName);
            converted.Policy =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(concrete.Policy);
            if (concrete.BypassPolicyLockoutSafetyCheck.is_Some)
                converted.BypassPolicyLockoutSafetyCheck =
                    (bool)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(
                        concrete.BypassPolicyLockoutSafetyCheck);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IPutKeyPolicyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(
                Amazon.KeyManagementService.Model.PutKeyPolicyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.PutKeyPolicyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M10_PolicyName(value.PolicyName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M6_Policy(value.Policy),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M30_BypassPolicyLockoutSafetyCheck(
                    value.BypassPolicyLockoutSafetyCheck));
        }

        public static Amazon.KeyManagementService.Model.ReEncryptRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(
                Dafny.Com.Amazonaws.Kms._IReEncryptRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ReEncryptRequest concrete = (Dafny.Com.Amazonaws.Kms.ReEncryptRequest) value;
            Amazon.KeyManagementService.Model.ReEncryptRequest converted =
                new Amazon.KeyManagementService.Model.ReEncryptRequest();
            converted.CiphertextBlob =
                (System.IO.MemoryStream)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(
                    concrete.CiphertextBlob);
            if (concrete.SourceEncryptionContext.is_Some)
                converted.SourceEncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(
                        concrete.SourceEncryptionContext);
            if (concrete.SourceKeyId.is_Some)
                converted.SourceKeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(
                        concrete.SourceKeyId);
            converted.DestinationKeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(
                    concrete.DestinationKeyId);
            if (concrete.DestinationEncryptionContext.is_Some)
                converted.DestinationEncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(
                        concrete.DestinationEncryptionContext);
            if (concrete.SourceEncryptionAlgorithm.is_Some)
                converted.SourceEncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(
                        concrete.SourceEncryptionAlgorithm);
            if (concrete.DestinationEncryptionAlgorithm.is_Some)
                converted.DestinationEncryptionAlgorithm =
                    (Amazon.KeyManagementService.EncryptionAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(
                        concrete.DestinationEncryptionAlgorithm);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IReEncryptRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(
                Amazon.KeyManagementService.Model.ReEncryptRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ReEncryptRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(value.CiphertextBlob),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M23_SourceEncryptionContext(
                    value.SourceEncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_SourceKeyId(value.SourceKeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(
                    value.DestinationKeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(
                    value.DestinationEncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M25_SourceEncryptionAlgorithm(
                    value.SourceEncryptionAlgorithm),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M30_DestinationEncryptionAlgorithm(
                    value.DestinationEncryptionAlgorithm),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(value.GrantTokens));
        }

        public static Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(
                Dafny.Com.Amazonaws.Kms._IUpdatePrimaryRegionRequest value)
        {
            Dafny.Com.Amazonaws.Kms.UpdatePrimaryRegionRequest concrete =
                (Dafny.Com.Amazonaws.Kms.UpdatePrimaryRegionRequest) value;
            Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest converted =
                new Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(
                    concrete.KeyId);
            converted.PrimaryRegion =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(
                    concrete.PrimaryRegion);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUpdatePrimaryRegionRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(
                Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.UpdatePrimaryRegionRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M13_PrimaryRegion(
                    value.PrimaryRegion));
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_AliasListEntry__M15_LastUpdatedDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.ListKeyPoliciesResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(
                Dafny.Com.Amazonaws.Kms._IListKeyPoliciesResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse concrete =
                (Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse) value;
            Amazon.KeyManagementService.Model.ListKeyPoliciesResponse converted =
                new Amazon.KeyManagementService.Model.ListKeyPoliciesResponse();
            if (concrete.PolicyNames.is_Some)
                converted.PolicyNames =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(
                        concrete.PolicyNames);
            if (concrete.NextMarker.is_Some)
                converted.NextMarker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(
                        concrete.NextMarker);
            if (concrete.Truncated.is_Some)
                converted.Truncated =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(
                        concrete.Truncated);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListKeyPoliciesResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(
                Amazon.KeyManagementService.Model.ListKeyPoliciesResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListKeyPoliciesResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M11_PolicyNames(value.PolicyNames),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(value.NextMarker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M9_Truncated(value.Truncated));
        }

        public static Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(
                Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresResponse value)
        {
            Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse concrete =
                (Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse) value;
            Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse converted =
                new Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse();
            if (concrete.CustomKeyStores.is_Some)
                converted.CustomKeyStores =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(
                        concrete.CustomKeyStores);
            if (concrete.NextMarker.is_Some)
                converted.NextMarker =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(
                        concrete.NextMarker);
            if (concrete.Truncated.is_Some)
                converted.Truncated =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(
                        concrete.Truncated);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(
                Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(
                    value.CustomKeyStores),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M10_NextMarker(
                    value.NextMarker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(
                    value.Truncated));
        }

        public static Amazon.KeyManagementService.OriginType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IOriginType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.OriginType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IOriginType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(
                Amazon.KeyManagementService.OriginType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IOriginType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IOriginType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_OriginType(
                        (Amazon.KeyManagementService.OriginType) value));
        }

        public static Amazon.KeyManagementService.Model.AlreadyExistsException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(
                Dafny.Com.Amazonaws.Kms._IAlreadyExistsException value)
        {
            Dafny.Com.Amazonaws.Kms.AlreadyExistsException concrete =
                (Dafny.Com.Amazonaws.Kms.AlreadyExistsException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.AlreadyExistsException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IAlreadyExistsException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException(
                Amazon.KeyManagementService.Model.AlreadyExistsException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.AlreadyExistsException(message);
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M5_Limit(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
        }

        public static Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(
                Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairRequest) value;
            Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest converted =
                new Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest();
            if (concrete.EncryptionContext.is_Some)
                converted.EncryptionContext =
                    (System.Collections.Generic.Dictionary<string, string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(
                        concrete.EncryptionContext);
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(
                    concrete.KeyId);
            converted.KeyPairSpec =
                (Amazon.KeyManagementService.DataKeyPairSpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(
                    concrete.KeyPairSpec);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateDataKeyPairRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(
                Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateDataKeyPairRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(
                    value.EncryptionContext),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_KeyPairSpec(
                    value.KeyPairSpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(
                    value.GrantTokens));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.ReplicateKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(
                Dafny.Com.Amazonaws.Kms._IReplicateKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.ReplicateKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.ReplicateKeyRequest) value;
            Amazon.KeyManagementService.Model.ReplicateKeyRequest converted =
                new Amazon.KeyManagementService.Model.ReplicateKeyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(concrete.KeyId);
            converted.ReplicaRegion =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(
                    concrete.ReplicaRegion);
            if (concrete.Policy.is_Some)
                converted.Policy =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(
                        concrete.Policy);
            if (concrete.BypassPolicyLockoutSafetyCheck.is_Some)
                converted.BypassPolicyLockoutSafetyCheck =
                    (bool)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                        concrete.BypassPolicyLockoutSafetyCheck);
            if (concrete.Description.is_Some)
                converted.Description =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(
                        concrete.Description);
            if (concrete.Tags.is_Some)
                converted.Tags =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(concrete.Tags);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IReplicateKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(
                Amazon.KeyManagementService.Model.ReplicateKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.ReplicateKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M13_ReplicaRegion(value.ReplicaRegion),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(value.Policy),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                    value.BypassPolicyLockoutSafetyCheck),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M11_Description(value.Description),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(value.Tags));
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S19_NullableBooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.KeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(
                Amazon.KeyManagementService.KeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_KeySpec((Amazon.KeyManagementService.KeySpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(
                Dafny.Com.Amazonaws.Kms._IDeleteImportedKeyMaterialRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DeleteImportedKeyMaterialRequest concrete =
                (Dafny.Com.Amazonaws.Kms.DeleteImportedKeyMaterialRequest) value;
            Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest converted =
                new Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(
                    concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDeleteImportedKeyMaterialRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(
                Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DeleteImportedKeyMaterialRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest__M5_KeyId(value.KeyId));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry> value)
        {
            return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>.FromArray(
                value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.Model.DependencyTimeoutException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(
                Dafny.Com.Amazonaws.Kms._IDependencyTimeoutException value)
        {
            Dafny.Com.Amazonaws.Kms.DependencyTimeoutException concrete =
                (Dafny.Com.Amazonaws.Kms.DependencyTimeoutException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.DependencyTimeoutException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IDependencyTimeoutException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException(
                Amazon.KeyManagementService.Model.DependencyTimeoutException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.DependencyTimeoutException(message);
        }

        public static Amazon.KeyManagementService.Model.NotFoundException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(
                Dafny.Com.Amazonaws.Kms._INotFoundException value)
        {
            Dafny.Com.Amazonaws.Kms.NotFoundException concrete = (Dafny.Com.Amazonaws.Kms.NotFoundException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.NotFoundException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._INotFoundException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NotFoundException(
                Amazon.KeyManagementService.Model.NotFoundException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.NotFoundException(message);
        }

        public static Amazon.KeyManagementService.ExpirationModelType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IExpirationModelType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.ExpirationModelType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IExpirationModelType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest__M15_ExpirationModel(
                Amazon.KeyManagementService.ExpirationModelType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IExpirationModelType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IExpirationModelType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(
                        (Amazon.KeyManagementService.ExpirationModelType) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(
            string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.ImportKeyMaterialResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(
                Dafny.Com.Amazonaws.Kms._IImportKeyMaterialResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse concrete =
                (Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse) value;
            Amazon.KeyManagementService.Model.ImportKeyMaterialResponse converted =
                new Amazon.KeyManagementService.Model.ImportKeyMaterialResponse();
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IImportKeyMaterialResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(
                Amazon.KeyManagementService.Model.ImportKeyMaterialResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ImportKeyMaterialResponse();
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M4_Tags(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
        }

        public static Amazon.KeyManagementService.Model.KMSInvalidSignatureException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(
                Dafny.Com.Amazonaws.Kms._IKMSInvalidSignatureException value)
        {
            Dafny.Com.Amazonaws.Kms.KMSInvalidSignatureException concrete =
                (Dafny.Com.Amazonaws.Kms.KMSInvalidSignatureException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.KMSInvalidSignatureException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IKMSInvalidSignatureException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S28_KMSInvalidSignatureException(
                Amazon.KeyManagementService.Model.KMSInvalidSignatureException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.KMSInvalidSignatureException(message);
        }

        public static Amazon.KeyManagementService.Model.ListGrantsResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(
                Dafny.Com.Amazonaws.Kms._IListGrantsResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ListGrantsResponse concrete = (Dafny.Com.Amazonaws.Kms.ListGrantsResponse) value;
            Amazon.KeyManagementService.Model.ListGrantsResponse converted =
                new Amazon.KeyManagementService.Model.ListGrantsResponse();
            if (concrete.Grants.is_Some)
                converted.Grants =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(concrete.Grants);
            if (concrete.NextMarker.is_Some)
                converted.NextMarker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(
                        concrete.NextMarker);
            if (concrete.Truncated.is_Some)
                converted.Truncated =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(
                        concrete.Truncated);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListGrantsResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(
                Amazon.KeyManagementService.Model.ListGrantsResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListGrantsResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M6_Grants(value.Grants),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M10_NextMarker(value.NextMarker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse__M9_Truncated(value.Truncated));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M19_EncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse__M9_PublicKey(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S7_ArnType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameType(value);
        }

        public static bool?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static int?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(
                Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest__M13_NumberOfBytes(
                int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.MessageType FromDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(
            Dafny.Com.Amazonaws.Kms._IMessageType value)
        {
            if (value.is_RAW) return Amazon.KeyManagementService.MessageType.RAW;
            if (value.is_DIGEST) return Amazon.KeyManagementService.MessageType.DIGEST;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MessageType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IMessageType ToDafny_N3_com__N9_amazonaws__N3_kms__S11_MessageType(
            Amazon.KeyManagementService.MessageType value)
        {
            if (Amazon.KeyManagementService.MessageType.RAW.Equals(value))
                return Dafny.Com.Amazonaws.Kms.MessageType.create_RAW();
            if (Amazon.KeyManagementService.MessageType.DIGEST.Equals(value))
                return Dafny.Com.Amazonaws.Kms.MessageType.create_DIGEST();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MessageType value");
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(
                Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec value)
        {
            if (value.is_RSASSA__PSS__SHA__256)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_256;
            if (value.is_RSASSA__PSS__SHA__384)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_384;
            if (value.is_RSASSA__PSS__SHA__512)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_512;
            if (value.is_RSASSA__PKCS1__V1__5__SHA__256)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256;
            if (value.is_RSASSA__PKCS1__V1__5__SHA__384)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384;
            if (value.is_RSASSA__PKCS1__V1__5__SHA__512)
                return Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512;
            if (value.is_ECDSA__SHA__256) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_256;
            if (value.is_ECDSA__SHA__384) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_384;
            if (value.is_ECDSA__SHA__512) return Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_512;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.SigningAlgorithmSpec value");
        }

        public static Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__256();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__384();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PSS_SHA_512.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PSS__SHA__512();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__256();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__384();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__512();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_256.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_ECDSA__SHA__256();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_384.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_ECDSA__SHA__384();
            if (Amazon.KeyManagementService.SigningAlgorithmSpec.ECDSA_SHA_512.Equals(value))
                return Dafny.Com.Amazonaws.Kms.SigningAlgorithmSpec.create_ECDSA__SHA__512();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.SigningAlgorithmSpec value");
        }

        public static Amazon.KeyManagementService.Model.KeyMetadata
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.KeyMetadata) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyMetadata>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse__M18_ReplicaKeyMetadata(
                Amazon.KeyManagementService.Model.KeyMetadata value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyMetadata>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(
                        (Amazon.KeyManagementService.Model.KeyMetadata) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse__M7_GrantId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType((string) value));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(
            Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(
            System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.GetParametersForImportRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(
                Dafny.Com.Amazonaws.Kms._IGetParametersForImportRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GetParametersForImportRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GetParametersForImportRequest) value;
            Amazon.KeyManagementService.Model.GetParametersForImportRequest converted =
                new Amazon.KeyManagementService.Model.GetParametersForImportRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(
                    concrete.KeyId);
            converted.WrappingAlgorithm =
                (Amazon.KeyManagementService.AlgorithmSpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(
                    concrete.WrappingAlgorithm);
            converted.WrappingKeySpec =
                (Amazon.KeyManagementService.WrappingKeySpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(
                    concrete.WrappingKeySpec);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGetParametersForImportRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(
                Amazon.KeyManagementService.Model.GetParametersForImportRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GetParametersForImportRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M17_WrappingAlgorithm(
                    value.WrappingAlgorithm),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M15_WrappingKeySpec(
                    value.WrappingKeySpec));
        }

        public static Amazon.KeyManagementService.KeyState
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyState> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyState) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyState>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(
                Amazon.KeyManagementService.KeyState value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyState>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyState>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_KeyState((Amazon.KeyManagementService.KeyState) value));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M15_CustomKeyStores(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>>
                    .create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry>>
                    .create_Some(ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CustomKeyStoresList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.CustomKeyStoresListEntry>)
                        value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member(
                Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_SigningAlgorithmSpecList__M6_member(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M9_Truncated(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_AliasNameType(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse__M14_CiphertextBlob(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.Model.IncorrectKeyException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(
                Dafny.Com.Amazonaws.Kms._IIncorrectKeyException value)
        {
            Dafny.Com.Amazonaws.Kms.IncorrectKeyException concrete =
                (Dafny.Com.Amazonaws.Kms.IncorrectKeyException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.IncorrectKeyException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IIncorrectKeyException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_IncorrectKeyException(
                Amazon.KeyManagementService.Model.IncorrectKeyException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.IncorrectKeyException(message);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextEquals(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M19_EncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.GenerateRandomRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(
                Dafny.Com.Amazonaws.Kms._IGenerateRandomRequest value)
        {
            Dafny.Com.Amazonaws.Kms.GenerateRandomRequest concrete =
                (Dafny.Com.Amazonaws.Kms.GenerateRandomRequest) value;
            Amazon.KeyManagementService.Model.GenerateRandomRequest converted =
                new Amazon.KeyManagementService.Model.GenerateRandomRequest();
            if (concrete.NumberOfBytes.is_Some)
                converted.NumberOfBytes =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(
                        concrete.NumberOfBytes);
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IGenerateRandomRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(
                Amazon.KeyManagementService.Model.GenerateRandomRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.GenerateRandomRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(value.NumberOfBytes),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId));
        }

        public static Amazon.KeyManagementService.CustomerMasterKeySpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.CustomerMasterKeySpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M21_CustomerMasterKeySpec(
                Amazon.KeyManagementService.CustomerMasterKeySpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ICustomerMasterKeySpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CustomerMasterKeySpec(
                        (Amazon.KeyManagementService.CustomerMasterKeySpec) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(
                string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S11_GrantIdType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static Amazon.KeyManagementService.Model.ListAliasesResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(
                Dafny.Com.Amazonaws.Kms._IListAliasesResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ListAliasesResponse concrete = (Dafny.Com.Amazonaws.Kms.ListAliasesResponse) value;
            Amazon.KeyManagementService.Model.ListAliasesResponse converted =
                new Amazon.KeyManagementService.Model.ListAliasesResponse();
            if (concrete.Aliases.is_Some)
                converted.Aliases =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(concrete.Aliases);
            if (concrete.NextMarker.is_Some)
                converted.NextMarker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(
                        concrete.NextMarker);
            if (concrete.Truncated.is_Some)
                converted.Truncated =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(
                        concrete.Truncated);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IListAliasesResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(
                Amazon.KeyManagementService.Model.ListAliasesResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ListAliasesResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(value.Aliases),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M10_NextMarker(value.NextMarker),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(value.Truncated));
        }

        public static Amazon.KeyManagementService.Model.GrantConstraints
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IGrantConstraints> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.Model.GrantConstraints) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IGrantConstraints>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantListEntry__M11_Constraints(
                Amazon.KeyManagementService.Model.GrantConstraints value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IGrantConstraints>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IGrantConstraints>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints(
                        (Amazon.KeyManagementService.Model.GrantConstraints) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(
                Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresRequest value)
        {
            Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresRequest concrete =
                (Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresRequest) value;
            Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest converted =
                new Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest();
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            if (concrete.CustomKeyStoreName.is_Some)
                converted.CustomKeyStoreName =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(
                        concrete.CustomKeyStoreName);
            if (concrete.Limit.is_Some)
                converted.Limit =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(
                        concrete.Limit);
            if (concrete.Marker.is_Some)
                converted.Marker =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(
                        concrete.Marker);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDescribeCustomKeyStoresRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(
                Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.DescribeCustomKeyStoresRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(
                    value.CustomKeyStoreName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M5_Limit(value.Limit),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M6_Marker(value.Marker));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M9_Plaintext(
            System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(
                Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreResponse value)
        {
            Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse concrete =
                (Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse) value;
            Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse converted =
                new Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse();
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IConnectCustomKeyStoreResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(
                Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.ConnectCustomKeyStoreResponse();
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M9_PublicKey(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PublicKeyType((System.IO.MemoryStream) value));
        }

        public static Amazon.KeyManagementService.ExpirationModelType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IExpirationModelType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.ExpirationModelType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IExpirationModelType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(
                Amazon.KeyManagementService.ExpirationModelType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IExpirationModelType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IExpirationModelType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ExpirationModelType(
                        (Amazon.KeyManagementService.ExpirationModelType) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_InvalidArnException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_PrincipalIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest__M6_Policy(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
        }

        public static Amazon.KeyManagementService.ConnectionStateType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IConnectionStateType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.ConnectionStateType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IConnectionStateType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(
                Amazon.KeyManagementService.ConnectionStateType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IConnectionStateType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IConnectionStateType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ConnectionStateType(
                        (Amazon.KeyManagementService.ConnectionStateType) value));
        }

        public static Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(
                Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreRequest value)
        {
            Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreRequest concrete =
                (Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreRequest) value;
            Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest converted =
                new Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest();
            converted.CustomKeyStoreName =
                (string)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(
                    concrete.CustomKeyStoreName);
            converted.CloudHsmClusterId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                    concrete.CloudHsmClusterId);
            converted.TrustAnchorCertificate =
                (string)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(
                    concrete.TrustAnchorCertificate);
            converted.KeyStorePassword =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(
                    concrete.KeyStorePassword);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateCustomKeyStoreRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(
                Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateCustomKeyStoreRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(
                    value.CustomKeyStoreName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                    value.CloudHsmClusterId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M22_TrustAnchorCertificate(
                    value.TrustAnchorCertificate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M16_KeyStorePassword(
                    value.KeyStorePassword));
        }

        public static System.Collections.Generic.List<string> FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(
            Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S10_TagKeyList__M6_member).ToArray());
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static int FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(int value)
        {
            return value;
        }

        public static int ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(int value)
        {
            return value;
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value);
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantOperation>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(
                System.Collections.Generic.List<string> value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S18_GrantOperationList(value);
        }

        public static Amazon.KeyManagementService.Model.CreateAliasRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(
                Dafny.Com.Amazonaws.Kms._ICreateAliasRequest value)
        {
            Dafny.Com.Amazonaws.Kms.CreateAliasRequest concrete = (Dafny.Com.Amazonaws.Kms.CreateAliasRequest) value;
            Amazon.KeyManagementService.Model.CreateAliasRequest converted =
                new Amazon.KeyManagementService.Model.CreateAliasRequest();
            converted.AliasName =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(
                    concrete.AliasName);
            converted.TargetKeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(
                    concrete.TargetKeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateAliasRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(
                Amazon.KeyManagementService.Model.CreateAliasRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateAliasRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M9_AliasName(value.AliasName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest__M11_TargetKeyId(value.TargetKeyId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M11_SourceKeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M9_Signature(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_CloudHsmClusterIdType((string) value));
        }

        public static Amazon.KeyManagementService.Model.IncorrectTrustAnchorException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(
                Dafny.Com.Amazonaws.Kms._IIncorrectTrustAnchorException value)
        {
            Dafny.Com.Amazonaws.Kms.IncorrectTrustAnchorException concrete =
                (Dafny.Com.Amazonaws.Kms.IncorrectTrustAnchorException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.IncorrectTrustAnchorException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IIncorrectTrustAnchorException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S29_IncorrectTrustAnchorException(
                Amazon.KeyManagementService.Model.IncorrectTrustAnchorException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.IncorrectTrustAnchorException(message);
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest__M19_EncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_MultiRegionConfiguration__M11_ReplicaKeys(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DescriptionType(value);
        }

        public static Amazon.KeyManagementService.Model.VerifyResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(Dafny.Com.Amazonaws.Kms._IVerifyResponse value)
        {
            Dafny.Com.Amazonaws.Kms.VerifyResponse concrete = (Dafny.Com.Amazonaws.Kms.VerifyResponse) value;
            Amazon.KeyManagementService.Model.VerifyResponse converted =
                new Amazon.KeyManagementService.Model.VerifyResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(concrete.KeyId);
            if (concrete.SignatureValid.is_Some)
                converted.SignatureValid =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(
                        concrete.SignatureValid);
            if (concrete.SigningAlgorithm.is_Some)
                converted.SigningAlgorithm =
                    (Amazon.KeyManagementService.SigningAlgorithmSpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(
                        concrete.SigningAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IVerifyResponse ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(
            Amazon.KeyManagementService.Model.VerifyResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.VerifyResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(value.SignatureValid),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(value.SigningAlgorithm));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>> value)
        {
            return value.ItemEnumerable.ToDictionary(
                pair => FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(pair.Car),
                pair => FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(pair.Cdr));
        }

        public static Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromCollection(value.Select(pair =>
                new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M3_key(pair.Key),
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType__M5_value(pair.Value))
            ));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey> value)
        {
            return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.MultiRegionKey> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._IMultiRegionKey>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyList__M6_member).ToArray());
        }

        public static System.DateTime?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse__M17_ParametersValidTo(
                System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_GrantConstraints__M23_EncryptionContextSubset(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static Amazon.KeyManagementService.Model.InvalidImportTokenException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(
                Dafny.Com.Amazonaws.Kms._IInvalidImportTokenException value)
        {
            Dafny.Com.Amazonaws.Kms.InvalidImportTokenException concrete =
                (Dafny.Com.Amazonaws.Kms.InvalidImportTokenException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.InvalidImportTokenException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._IInvalidImportTokenException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_InvalidImportTokenException(
                Amazon.KeyManagementService.Model.InvalidImportTokenException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.InvalidImportTokenException(message);
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?) null : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest__M5_Limit(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_LimitType((int) value));
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(
                Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value);
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse__M19_PrivateKeyPlaintext(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList__M6_member(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenType(value);
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M14_SignatureValid(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.ConnectionErrorCodeType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.ConnectionErrorCodeType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(
                Amazon.KeyManagementService.ConnectionErrorCodeType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IConnectionErrorCodeType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ConnectionErrorCodeType(
                        (Amazon.KeyManagementService.ConnectionErrorCodeType) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList(Dafny.ISequence<Dafny.ISequence<char>> value)
        {
            return new System.Collections.Generic.List<string>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member));
        }

        public static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList(
            System.Collections.Generic.List<string> value)
        {
            return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value
                .Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S14_PolicyNameList__M6_member).ToArray());
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse__M10_NextMarker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static Amazon.KeyManagementService.Model.SignRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(Dafny.Com.Amazonaws.Kms._ISignRequest value)
        {
            Dafny.Com.Amazonaws.Kms.SignRequest concrete = (Dafny.Com.Amazonaws.Kms.SignRequest) value;
            Amazon.KeyManagementService.Model.SignRequest converted =
                new Amazon.KeyManagementService.Model.SignRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(concrete.KeyId);
            converted.Message =
                (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(
                    concrete.Message);
            if (concrete.MessageType.is_Some)
                converted.MessageType =
                    (Amazon.KeyManagementService.MessageType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(concrete.MessageType);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(concrete.GrantTokens);
            converted.SigningAlgorithm =
                (Amazon.KeyManagementService.SigningAlgorithmSpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(concrete
                    .SigningAlgorithm);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ISignRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(
            Amazon.KeyManagementService.Model.SignRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.SignRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M7_Message(value.Message),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_MessageType(value.MessageType),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(value.GrantTokens),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M16_SigningAlgorithm(value.SigningAlgorithm));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList(
                Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry> value)
        {
            return new System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry>(
                value.Elements.Select(FromDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member));
        }

        public static Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.GrantListEntry> value)
        {
            return Dafny.Sequence<Dafny.Com.Amazonaws.Kms._IGrantListEntry>.FromArray(
                value.Select(ToDafny_N3_com__N9_amazonaws__N3_kms__S9_GrantList__M6_member).ToArray());
        }

        public static Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(
                Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotRelatedException value)
        {
            Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotRelatedException concrete =
                (Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotRelatedException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotRelatedException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S34_CloudHsmClusterNotRelatedException(
                Amazon.KeyManagementService.Model.CloudHsmClusterNotRelatedException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotRelatedException(message);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M28_DestinationEncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M9_Truncated(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(
                Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreRequest value)
        {
            Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreRequest concrete =
                (Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreRequest) value;
            Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest converted =
                new Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest();
            converted.CustomKeyStoreId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    concrete.CustomKeyStoreId);
            if (concrete.NewCustomKeyStoreName.is_Some)
                converted.NewCustomKeyStoreName =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(
                        concrete.NewCustomKeyStoreName);
            if (concrete.KeyStorePassword.is_Some)
                converted.KeyStorePassword =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(
                        concrete.KeyStorePassword);
            if (concrete.CloudHsmClusterId.is_Some)
                converted.CloudHsmClusterId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                        concrete.CloudHsmClusterId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUpdateCustomKeyStoreRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(
                Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.UpdateCustomKeyStoreRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M21_NewCustomKeyStoreName(
                    value.NewCustomKeyStoreName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M16_KeyStorePassword(
                    value.KeyStorePassword),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest__M17_CloudHsmClusterId(
                    value.CloudHsmClusterId));
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.SigningAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse__M16_SigningAlgorithm(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(
                        (Amazon.KeyManagementService.SigningAlgorithmSpec) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M16_DestinationKeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.CancelKeyDeletionResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(
                Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionResponse value)
        {
            Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse concrete =
                (Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse) value;
            Amazon.KeyManagementService.Model.CancelKeyDeletionResponse converted =
                new Amazon.KeyManagementService.Model.CancelKeyDeletionResponse();
            if (concrete.KeyId.is_Some)
                converted.KeyId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(
                        concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(
                Amazon.KeyManagementService.Model.CancelKeyDeletionResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.CancelKeyDeletionResponse(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse__M5_KeyId(value.KeyId));
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoresListEntry
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry value)
        {
            Dafny.Com.Amazonaws.Kms.CustomKeyStoresListEntry concrete =
                (Dafny.Com.Amazonaws.Kms.CustomKeyStoresListEntry) value;
            Amazon.KeyManagementService.Model.CustomKeyStoresListEntry converted =
                new Amazon.KeyManagementService.Model.CustomKeyStoresListEntry();
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            if (concrete.CustomKeyStoreName.is_Some)
                converted.CustomKeyStoreName =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(
                        concrete.CustomKeyStoreName);
            if (concrete.CloudHsmClusterId.is_Some)
                converted.CloudHsmClusterId =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(
                        concrete.CloudHsmClusterId);
            if (concrete.TrustAnchorCertificate.is_Some)
                converted.TrustAnchorCertificate =
                    (string)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(
                        concrete.TrustAnchorCertificate);
            if (concrete.ConnectionState.is_Some)
                converted.ConnectionState =
                    (Amazon.KeyManagementService.ConnectionStateType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(
                        concrete.ConnectionState);
            if (concrete.ConnectionErrorCode.is_Some)
                converted.ConnectionErrorCode =
                    (Amazon.KeyManagementService.ConnectionErrorCodeType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(
                        concrete.ConnectionErrorCode);
            if (concrete.CreationDate.is_Some)
                converted.CreationDate =
                    (System.DateTime)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(
                        concrete.CreationDate);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoresListEntry
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry(
                Amazon.KeyManagementService.Model.CustomKeyStoresListEntry value)
        {
            return new Dafny.Com.Amazonaws.Kms.CustomKeyStoresListEntry(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M18_CustomKeyStoreName(
                    value.CustomKeyStoreName),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M17_CloudHsmClusterId(
                    value.CloudHsmClusterId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(
                    value.TrustAnchorCertificate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M15_ConnectionState(
                    value.ConnectionState),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M19_ConnectionErrorCode(
                    value.ConnectionErrorCode),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(
                    value.CreationDate));
        }

        public static Amazon.KeyManagementService.Model.KeyMetadata
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(Dafny.Com.Amazonaws.Kms._IKeyMetadata value)
        {
            Dafny.Com.Amazonaws.Kms.KeyMetadata concrete = (Dafny.Com.Amazonaws.Kms.KeyMetadata) value;
            Amazon.KeyManagementService.Model.KeyMetadata converted =
                new Amazon.KeyManagementService.Model.KeyMetadata();
            if (concrete.AWSAccountId.is_Some)
                converted.AWSAccountId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(
                        concrete.AWSAccountId);
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(concrete.KeyId);
            if (concrete.Arn.is_Some)
                converted.Arn = (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(concrete.Arn);
            if (concrete.CreationDate.is_Some)
                converted.CreationDate =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(
                        concrete.CreationDate);
            if (concrete.Enabled.is_Some)
                converted.Enabled =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(concrete.Enabled);
            if (concrete.Description.is_Some)
                converted.Description =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(
                        concrete.Description);
            if (concrete.KeyUsage.is_Some)
                converted.KeyUsage =
                    (Amazon.KeyManagementService.KeyUsageType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(concrete.KeyUsage);
            if (concrete.KeyState.is_Some)
                converted.KeyState =
                    (Amazon.KeyManagementService.KeyState)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(concrete.KeyState);
            if (concrete.DeletionDate.is_Some)
                converted.DeletionDate =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(
                        concrete.DeletionDate);
            if (concrete.ValidTo.is_Some)
                converted.ValidTo =
                    (System.DateTime) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(
                        concrete.ValidTo);
            if (concrete.Origin.is_Some)
                converted.Origin =
                    (Amazon.KeyManagementService.OriginType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(concrete.Origin);
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            if (concrete.CloudHsmClusterId.is_Some)
                converted.CloudHsmClusterId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(
                        concrete.CloudHsmClusterId);
            if (concrete.ExpirationModel.is_Some)
                converted.ExpirationModel =
                    (Amazon.KeyManagementService.ExpirationModelType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(
                        concrete.ExpirationModel);
            if (concrete.KeyManager.is_Some)
                converted.KeyManager =
                    (Amazon.KeyManagementService.KeyManagerType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(concrete.KeyManager);
            if (concrete.CustomerMasterKeySpec.is_Some)
                converted.CustomerMasterKeySpec =
                    (Amazon.KeyManagementService.CustomerMasterKeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(
                        concrete.CustomerMasterKeySpec);
            if (concrete.KeySpec.is_Some)
                converted.KeySpec =
                    (Amazon.KeyManagementService.KeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(concrete.KeySpec);
            if (concrete.EncryptionAlgorithms.is_Some)
                converted.EncryptionAlgorithms =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(
                        concrete.EncryptionAlgorithms);
            if (concrete.SigningAlgorithms.is_Some)
                converted.SigningAlgorithms =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(
                        concrete.SigningAlgorithms);
            if (concrete.MultiRegion.is_Some)
                converted.MultiRegion =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(
                        concrete.MultiRegion);
            if (concrete.MultiRegionConfiguration.is_Some)
                converted.MultiRegionConfiguration =
                    (Amazon.KeyManagementService.Model.MultiRegionConfiguration)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(
                        concrete.MultiRegionConfiguration);
            if (concrete.PendingDeletionWindowInDays.is_Some)
                converted.PendingDeletionWindowInDays =
                    (int) FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(
                        concrete.PendingDeletionWindowInDays);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IKeyMetadata ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata(
            Amazon.KeyManagementService.Model.KeyMetadata value)
        {
            return new Dafny.Com.Amazonaws.Kms.KeyMetadata(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_AWSAccountId(value.AWSAccountId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M3_Arn(value.Arn),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(value.CreationDate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_Enabled(value.Enabled),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_Description(value.Description),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyUsage(value.KeyUsage),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M8_KeyState(value.KeyState),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_DeletionDate(value.DeletionDate),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_ValidTo(value.ValidTo),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M6_Origin(value.Origin),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M16_CustomKeyStoreId(value.CustomKeyStoreId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_CloudHsmClusterId(value.CloudHsmClusterId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M15_ExpirationModel(value.ExpirationModel),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M10_KeyManager(value.KeyManager),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M21_CustomerMasterKeySpec(
                    value.CustomerMasterKeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M7_KeySpec(value.KeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M20_EncryptionAlgorithms(
                    value.EncryptionAlgorithms),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M17_SigningAlgorithms(value.SigningAlgorithms),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M11_MultiRegion(value.MultiRegion),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M24_MultiRegionConfiguration(
                    value.MultiRegionConfiguration),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M27_PendingDeletionWindowInDays(
                    value.PendingDeletionWindowInDays));
        }

        public static System.DateTime?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M12_CreationDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_DependencyTimeoutException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_InvalidMarkerException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(
                Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse__M14_CiphertextBlob(
                System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType((System.IO.MemoryStream) value));
        }

        public static System.DateTime? FromDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_KeyMetadata__M12_CreationDate(System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(
                Dafny.Com.Amazonaws.Kms._IUpdateKeyDescriptionRequest value)
        {
            Dafny.Com.Amazonaws.Kms.UpdateKeyDescriptionRequest concrete =
                (Dafny.Com.Amazonaws.Kms.UpdateKeyDescriptionRequest) value;
            Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest converted =
                new Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(
                    concrete.KeyId);
            converted.Description =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(
                    concrete.Description);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IUpdateKeyDescriptionRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(
                Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.UpdateKeyDescriptionRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest__M11_Description(
                    value.Description));
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._ITag>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M5_KeyId(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType((string) value));
        }

        public static Amazon.KeyManagementService.MultiRegionKeyType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType(
                Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType value)
        {
            if (value.is_PRIMARY) return Amazon.KeyManagementService.MultiRegionKeyType.PRIMARY;
            if (value.is_REPLICA) return Amazon.KeyManagementService.MultiRegionKeyType.REPLICA;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MultiRegionKeyType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IMultiRegionKeyType
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_MultiRegionKeyType(
                Amazon.KeyManagementService.MultiRegionKeyType value)
        {
            if (Amazon.KeyManagementService.MultiRegionKeyType.PRIMARY.Equals(value))
                return Dafny.Com.Amazonaws.Kms.MultiRegionKeyType.create_PRIMARY();
            if (Amazon.KeyManagementService.MultiRegionKeyType.REPLICA.Equals(value))
                return Dafny.Com.Amazonaws.Kms.MultiRegionKeyType.create_REPLICA();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.MultiRegionKeyType value");
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest__M11_TargetKeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest__M6_Marker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static int? FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(
            Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest__M13_NumberOfBytes(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S17_NumberOfBytesType((int) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_AlreadyExistsException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S25_InvalidAliasNameException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(
            Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None
                ? (System.IO.MemoryStream) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<byte>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse__M9_Plaintext(System.IO.MemoryStream value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType((System.IO.MemoryStream) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CustomKeyStoresListEntry__M22_TrustAnchorCertificate(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S26_TrustAnchorCertificateType((string) value));
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(
                Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest__M18_CustomKeyStoreName(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static string
            FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest__M18_CustomKeyStoreName(
                string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType((string) value));
        }

        public static int?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(
                Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M19_PendingWindowInDays(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S14_MultiRegionKey__M6_Region(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_RegionType((string) value));
        }

        public static Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(
                Dafny.Com.Amazonaws.Kms._ICustomKeyStoreNotFoundException value)
        {
            Dafny.Com.Amazonaws.Kms.CustomKeyStoreNotFoundException concrete =
                (Dafny.Com.Amazonaws.Kms.CustomKeyStoreNotFoundException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICustomKeyStoreNotFoundException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_CustomKeyStoreNotFoundException(
                Amazon.KeyManagementService.Model.CustomKeyStoreNotFoundException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CustomKeyStoreNotFoundException(message);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest__M6_Marker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse__M10_NextMarker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest__M6_Marker(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_MarkerType((string) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_InvalidGrantTokenException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.SigningAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.SigningAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse__M16_SigningAlgorithm(
                Amazon.KeyManagementService.SigningAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._ISigningAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S20_SigningAlgorithmSpec(
                        (Amazon.KeyManagementService.SigningAlgorithmSpec) value));
        }

        public static Amazon.KeyManagementService.Model.CreateGrantRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(
                Dafny.Com.Amazonaws.Kms._ICreateGrantRequest value)
        {
            Dafny.Com.Amazonaws.Kms.CreateGrantRequest concrete = (Dafny.Com.Amazonaws.Kms.CreateGrantRequest) value;
            Amazon.KeyManagementService.Model.CreateGrantRequest converted =
                new Amazon.KeyManagementService.Model.CreateGrantRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(concrete.KeyId);
            converted.GranteePrincipal =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(
                    concrete.GranteePrincipal);
            if (concrete.RetiringPrincipal.is_Some)
                converted.RetiringPrincipal =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(
                        concrete.RetiringPrincipal);
            converted.Operations =
                (System.Collections.Generic.List<string>)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(concrete.Operations);
            if (concrete.Constraints.is_Some)
                converted.Constraints =
                    (Amazon.KeyManagementService.Model.GrantConstraints)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(
                        concrete.Constraints);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(
                        concrete.GrantTokens);
            if (concrete.Name.is_Some)
                converted.Name =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(concrete.Name);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateGrantRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(
                Amazon.KeyManagementService.Model.CreateGrantRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateGrantRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M16_GranteePrincipal(
                    value.GranteePrincipal),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M17_RetiringPrincipal(
                    value.RetiringPrincipal),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M10_Operations(value.Operations),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_Constraints(value.Constraints),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M11_GrantTokens(value.GrantTokens),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest__M4_Name(value.Name));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.Model.Tag
            FromDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member(Dafny.Com.Amazonaws.Kms._ITag value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(value);
        }

        public static Dafny.Com.Amazonaws.Kms._ITag ToDafny_N3_com__N9_amazonaws__N3_kms__S7_TagList__M6_member(
            Amazon.KeyManagementService.Model.Tag value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S3_Tag(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Amazon.KeyManagementService.KeyUsageType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.KeyUsageType) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IKeyUsageType>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(
                Amazon.KeyManagementService.KeyUsageType value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IKeyUsageType>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S12_KeyUsageType(
                        (Amazon.KeyManagementService.KeyUsageType) value));
        }

        public static Amazon.KeyManagementService.KeyManagerType
            FromDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType(Dafny.Com.Amazonaws.Kms._IKeyManagerType value)
        {
            if (value.is_AWS) return Amazon.KeyManagementService.KeyManagerType.AWS;
            if (value.is_CUSTOMER) return Amazon.KeyManagementService.KeyManagerType.CUSTOMER;
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyManagerType value");
        }

        public static Dafny.Com.Amazonaws.Kms._IKeyManagerType ToDafny_N3_com__N9_amazonaws__N3_kms__S14_KeyManagerType(
            Amazon.KeyManagementService.KeyManagerType value)
        {
            if (Amazon.KeyManagementService.KeyManagerType.AWS.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyManagerType.create_AWS();
            if (Amazon.KeyManagementService.KeyManagerType.CUSTOMER.Equals(value))
                return Dafny.Com.Amazonaws.Kms.KeyManagerType.create_CUSTOMER();
            throw new System.ArgumentException("Invalid Amazon.KeyManagementService.KeyManagerType value");
        }

        public static System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse__M7_Aliases(
                System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IAliasListEntry>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S9_AliasList(
                        (System.Collections.Generic.List<Amazon.KeyManagementService.Model.AliasListEntry>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S23_InvalidGrantIdException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse__M20_EncryptionAlgorithms(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
                    .create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>>
                    .create_Some(
                        ToDafny_N3_com__N9_amazonaws__N3_kms__S27_EncryptionAlgorithmSpecList(
                            (System.Collections.Generic.List<string>) value));
        }

        public static Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse
            FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(
                Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreResponse value)
        {
            Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse concrete =
                (Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse) value;
            Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse converted =
                new Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse();
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IDisconnectCustomKeyStoreResponse
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(
                Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse value)
        {
            return new Dafny.Com.Amazonaws.Kms.DisconnectCustomKeyStoreResponse();
        }

        public static Amazon.KeyManagementService.Model.RevokeGrantRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(
                Dafny.Com.Amazonaws.Kms._IRevokeGrantRequest value)
        {
            Dafny.Com.Amazonaws.Kms.RevokeGrantRequest concrete = (Dafny.Com.Amazonaws.Kms.RevokeGrantRequest) value;
            Amazon.KeyManagementService.Model.RevokeGrantRequest converted =
                new Amazon.KeyManagementService.Model.RevokeGrantRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(concrete.KeyId);
            converted.GrantId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(concrete.GrantId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IRevokeGrantRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(
                Amazon.KeyManagementService.Model.RevokeGrantRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.RevokeGrantRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest__M7_GrantId(value.GrantId));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S10_PolicyType((string) value));
        }

        public static int?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(
                Wrappers_Compile._IOption<int> value)
        {
            return value.is_None
                ? (int?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType(value.Extract());
        }

        public static Wrappers_Compile._IOption<int>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest__M19_PendingWindowInDays(int? value)
        {
            return value == null
                ? Wrappers_Compile.Option<int>.create_None()
                : Wrappers_Compile.Option<int>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_PendingWindowInDaysType((int) value));
        }

        public static Amazon.KeyManagementService.Model.CancelKeyDeletionRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(
                Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionRequest value)
        {
            Dafny.Com.Amazonaws.Kms.CancelKeyDeletionRequest concrete =
                (Dafny.Com.Amazonaws.Kms.CancelKeyDeletionRequest) value;
            Amazon.KeyManagementService.Model.CancelKeyDeletionRequest converted =
                new Amazon.KeyManagementService.Model.CancelKeyDeletionRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICancelKeyDeletionRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(
                Amazon.KeyManagementService.Model.CancelKeyDeletionRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.CancelKeyDeletionRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest__M5_KeyId(value.KeyId));
        }

        public static Amazon.KeyManagementService.DataKeyPairSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(
                Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
        }

        public static Dafny.Com.Amazonaws.Kms._IDataKeyPairSpec
            ToDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest__M11_KeyPairSpec(
                Amazon.KeyManagementService.DataKeyPairSpec value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DataKeyPairSpec(value);
        }

        public static bool? FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(
            Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None
                ? (bool?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType(value.Extract());
        }

        public static Wrappers_Compile._IOption<bool>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse__M9_Truncated(bool? value)
        {
            return value == null
                ? Wrappers_Compile.Option<bool>.create_None()
                : Wrappers_Compile.Option<bool>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S11_BooleanType((bool) value));
        }

        public static Amazon.KeyManagementService.Model.EnableKeyRotationRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(
                Dafny.Com.Amazonaws.Kms._IEnableKeyRotationRequest value)
        {
            Dafny.Com.Amazonaws.Kms.EnableKeyRotationRequest concrete =
                (Dafny.Com.Amazonaws.Kms.EnableKeyRotationRequest) value;
            Amazon.KeyManagementService.Model.EnableKeyRotationRequest converted =
                new Amazon.KeyManagementService.Model.EnableKeyRotationRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(concrete.KeyId);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IEnableKeyRotationRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(
                Amazon.KeyManagementService.Model.EnableKeyRotationRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.EnableKeyRotationRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest__M5_KeyId(value.KeyId));
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(
            Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S22_CustomKeyStoreNameType(
            string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(
            Dafny.ISequence<char> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static Dafny.ISequence<char> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(
            string value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S9_KeyIdType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(
                Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotFoundException value)
        {
            Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotFoundException concrete =
                (Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotFoundException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotFoundException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S32_CloudHsmClusterNotFoundException(
                Amazon.KeyManagementService.Model.CloudHsmClusterNotFoundException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotFoundException(message);
        }

        public static System.Collections.Generic.Dictionary<string, string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(
                Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.Dictionary<string, string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest__M17_EncryptionContext(
                System.Collections.Generic.Dictionary<string, string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S21_EncryptionContextType(
                        (System.Collections.Generic.Dictionary<string, string>) value));
        }

        public static string FromDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message(
            Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (string) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S20_KMSInternalException__M7_message(string value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType((string) value));
        }

        public static Amazon.KeyManagementService.Model.VerifyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(Dafny.Com.Amazonaws.Kms._IVerifyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.VerifyRequest concrete = (Dafny.Com.Amazonaws.Kms.VerifyRequest) value;
            Amazon.KeyManagementService.Model.VerifyRequest converted =
                new Amazon.KeyManagementService.Model.VerifyRequest();
            converted.KeyId =
                (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(concrete.KeyId);
            converted.Message =
                (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(
                    concrete.Message);
            if (concrete.MessageType.is_Some)
                converted.MessageType =
                    (Amazon.KeyManagementService.MessageType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(concrete.MessageType);
            converted.Signature =
                (System.IO.MemoryStream) FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(
                    concrete.Signature);
            converted.SigningAlgorithm =
                (Amazon.KeyManagementService.SigningAlgorithmSpec)
                FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(
                    concrete.SigningAlgorithm);
            if (concrete.GrantTokens.is_Some)
                converted.GrantTokens =
                    (System.Collections.Generic.List<string>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(concrete.GrantTokens);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._IVerifyRequest ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(
            Amazon.KeyManagementService.Model.VerifyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.VerifyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M5_KeyId(value.KeyId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(value.Message),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_MessageType(value.MessageType),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(value.Signature),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M16_SigningAlgorithm(value.SigningAlgorithm),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M11_GrantTokens(value.GrantTokens));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M7_Message(
            System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S13_PlaintextType(value);
        }

        public static System.Collections.Generic.List<string>
            FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(
                Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value)
        {
            return value.is_None
                ? (System.Collections.Generic.List<string>) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest__M11_GrantTokens(
                System.Collections.Generic.List<string> value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S14_GrantTokenList(
                        (System.Collections.Generic.List<string>) value));
        }

        public static System.IO.MemoryStream FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(
            Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Dafny.ISequence<byte> ToDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest__M9_Signature(
            System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Amazon.KeyManagementService.Model.CreateKeyRequest
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(
                Dafny.Com.Amazonaws.Kms._ICreateKeyRequest value)
        {
            Dafny.Com.Amazonaws.Kms.CreateKeyRequest concrete = (Dafny.Com.Amazonaws.Kms.CreateKeyRequest) value;
            Amazon.KeyManagementService.Model.CreateKeyRequest converted =
                new Amazon.KeyManagementService.Model.CreateKeyRequest();
            if (concrete.Policy.is_Some)
                converted.Policy =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(concrete.Policy);
            if (concrete.Description.is_Some)
                converted.Description =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(
                        concrete.Description);
            if (concrete.KeyUsage.is_Some)
                converted.KeyUsage =
                    (Amazon.KeyManagementService.KeyUsageType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(concrete.KeyUsage);
            if (concrete.CustomerMasterKeySpec.is_Some)
                converted.CustomerMasterKeySpec =
                    (Amazon.KeyManagementService.CustomerMasterKeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(
                        concrete.CustomerMasterKeySpec);
            if (concrete.KeySpec.is_Some)
                converted.KeySpec =
                    (Amazon.KeyManagementService.KeySpec)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(concrete.KeySpec);
            if (concrete.Origin.is_Some)
                converted.Origin =
                    (Amazon.KeyManagementService.OriginType)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(concrete.Origin);
            if (concrete.CustomKeyStoreId.is_Some)
                converted.CustomKeyStoreId =
                    (string) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(
                        concrete.CustomKeyStoreId);
            if (concrete.BypassPolicyLockoutSafetyCheck.is_Some)
                converted.BypassPolicyLockoutSafetyCheck =
                    (bool)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                        concrete.BypassPolicyLockoutSafetyCheck);
            if (concrete.Tags.is_Some)
                converted.Tags =
                    (System.Collections.Generic.List<Amazon.KeyManagementService.Model.Tag>)
                    FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(concrete.Tags);
            if (concrete.MultiRegion.is_Some)
                converted.MultiRegion =
                    (bool) FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(
                        concrete.MultiRegion);
            return converted;
        }

        public static Dafny.Com.Amazonaws.Kms._ICreateKeyRequest
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(
                Amazon.KeyManagementService.Model.CreateKeyRequest value)
        {
            return new Dafny.Com.Amazonaws.Kms.CreateKeyRequest(
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Policy(value.Policy),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_Description(value.Description),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M8_KeyUsage(value.KeyUsage),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M21_CustomerMasterKeySpec(
                    value.CustomerMasterKeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M7_KeySpec(value.KeySpec),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M6_Origin(value.Origin),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M16_CustomKeyStoreId(
                    value.CustomKeyStoreId),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M30_BypassPolicyLockoutSafetyCheck(
                    value.BypassPolicyLockoutSafetyCheck),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M4_Tags(value.Tags),
                ToDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest__M11_MultiRegion(value.MultiRegion));
        }

        public static Amazon.KeyManagementService.EncryptionAlgorithmSpec
            FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(
                Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec> value)
        {
            return value.is_None
                ? (Amazon.KeyManagementService.EncryptionAlgorithmSpec) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse__M25_SourceEncryptionAlgorithm(
                Amazon.KeyManagementService.EncryptionAlgorithmSpec value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_None()
                : Wrappers_Compile.Option<Dafny.Com.Amazonaws.Kms._IEncryptionAlgorithmSpec>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S23_EncryptionAlgorithmSpec(
                        (Amazon.KeyManagementService.EncryptionAlgorithmSpec) value));
        }

        public static System.DateTime?
            FromDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(
                Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None
                ? (System.DateTime?) null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType(value.Extract());
        }

        public static Wrappers_Compile._IOption<Dafny.ISequence<char>>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse__M12_DeletionDate(
                System.DateTime? value)
        {
            return value == null
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S8_DateType((System.DateTime) value));
        }

        public static System.IO.MemoryStream
            FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(
                Dafny.ISequence<byte> value)
        {
            return FromDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Dafny.ISequence<byte>
            ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest__M14_CiphertextBlob(System.IO.MemoryStream value)
        {
            return ToDafny_N3_com__N9_amazonaws__N3_kms__S14_CiphertextType(value);
        }

        public static Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException
            FromDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(
                Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotActiveException value)
        {
            Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotActiveException concrete =
                (Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotActiveException) value;
            string message = concrete.message.is_Some
                ? null
                : FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(concrete.message.Extract());
            return new Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException(message);
        }

        public static Dafny.Com.Amazonaws.Kms._ICloudHsmClusterNotActiveException
            ToDafny_N3_com__N9_amazonaws__N3_kms__S33_CloudHsmClusterNotActiveException(
                Amazon.KeyManagementService.Model.CloudHsmClusterNotActiveException value)
        {
            Wrappers_Compile._IOption<Dafny.ISequence<char>> message = System.String.IsNullOrEmpty(value.Message)
                ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None()
                : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(
                    ToDafny_N3_com__N9_amazonaws__N3_kms__S16_ErrorMessageType(value.Message));
            return new Dafny.Com.Amazonaws.Kms.CloudHsmClusterNotActiveException(message);
        }
    }
}
