// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon;
using Amazon.KeyManagementService;
using Aws.Crypto;

namespace TestVectors
{
    public static class MaterialProviderFactory
    {
        public static ICryptographicMaterialsManager DecryptCmm(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            CreateDefaultCryptographicMaterialsManagerInput input = new CreateDefaultCryptographicMaterialsManagerInput
            {
                Keyring = CreateDecryptKeyring(vector, keys)
            };
            return materialProviders.CreateDefaultCryptographicMaterialsManager(input);
        }

        private static IKeyring CreateDecryptKeyring(TestVector vector, Dictionary<string, Key> keys) {
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            List<IKeyring> children = new List<IKeyring>();
            foreach (MasterKey keyInfo in vector.MasterKeys)
            {
                // Some keyrings, like discovery KMS keyrings, do not specify keys
                Key key = keyInfo.Key == null ? null : keys[keyInfo.Key];
                children.Add(CreateKeyring(keyInfo, key));
            }
            CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput
            {
                Generator = null,
                ChildKeyrings = children
            };

            return materialProviders.CreateMultiKeyring(createMultiKeyringInput);
        }
        private static IKeyring CreateKeyring(MasterKey keyInfo, Key key) {
            // TODO: maybe make this a class variable so we're not constantly re-creating it
            IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();

            if (keyInfo.Type == "aws-kms") {
                CreateStrictAwsKmsKeyringInput createKeyringInput = new CreateStrictAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateStrictAwsKmsKeyring(createKeyringInput);
            } else if (keyInfo.Type == "aws-kms-mrk-aware") {
                CreateMrkAwareStrictAwsKmsKeyringInput createKeyringInput = new CreateMrkAwareStrictAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateMrkAwareStrictAwsKmsKeyring(createKeyringInput);
            } else if (keyInfo.Type == "aws-kms-mrk-aware-discovery") {
                CreateMrkAwareDiscoveryAwsKmsKeyringInput createKeyringInput = new CreateMrkAwareDiscoveryAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(keyInfo.DefaultMrkRegion)),
                    Region = keyInfo.DefaultMrkRegion
                };
                return materialProviders.CreateMrkAwareDiscoveryAwsKmsKeyring(createKeyringInput);
            } else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "aes") {
                CreateRawAesKeyringInput createKeyringInput = new CreateRawAesKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    WrappingKey = new MemoryStream(Convert.FromBase64String(key.Material)),
                    WrappingAlg = AesAlgorithmFromBits(key.Bits),
                };

                return materialProviders.CreateRawAesKeyring(createKeyringInput);
            } else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "private") {
                PaddingScheme padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                byte[] privateKey = RSAEncryption.RSA.ParsePEMString(key.Material);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PrivateKey = new MemoryStream(privateKey)
                };
                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            } else if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "public") {
                PaddingScheme padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                byte[] publicKey = RSAEncryption.RSA.ParsePEMString(key.Material);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PublicKey = new MemoryStream(publicKey)
                };
                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            }
            else {
                throw new Exception("Unsupported keyring type!");
            }
        }
        private static AesWrappingAlg AesAlgorithmFromBits(ushort bits) {
            return bits switch {
                128 => AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16,
                192 => AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16,
                256 => AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16,
                _ => throw new Exception("Unsupported AES wrapping algorithm")
            };
        }

        private static PaddingScheme RSAPaddingFromStrings(string strAlg, string strHash) {
            return (strAlg, strHash) switch {
                ("pkcs1", _) => PaddingScheme.PKCS1,
                ("oaep-mgf1", "sha1") => PaddingScheme.OAEP_SHA1_MGF1,
                ("oaep-mgf1", "sha256") => PaddingScheme.OAEP_SHA256_MGF1,
                ("oaep-mgf1", "sha384") => PaddingScheme.OAEP_SHA384_MGF1,
                ("oaep-mgf1", "sha512") => PaddingScheme.OAEP_SHA512_MGF1,
                _ => throw new Exception("Unsupported RSA Padding " + strAlg + strHash)
            };
        }

        private static RegionEndpoint GetRegionForArn(string keyId)
        {
            string[] split = keyId.Split(":");
            string region = split[3];
            return RegionEndpoint.GetBySystemName(region);
        }
    }

}
