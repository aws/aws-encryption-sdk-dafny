// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Diagnostics;
using Newtonsoft.Json;
using Amazon;
using Amazon.DynamoDBv2;
using Amazon.KeyManagementService;
using AWS.Cryptography.KeyStore;
using AWS.Cryptography.MaterialProviders;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;

using RSAEncryption;

namespace TestVectors
{
    public enum CryptoOperation
    {
        ENCRYPT, DECRYPT
    }

    public static class MaterialProviderFactory
    {
        private static readonly MaterialProviders materialProviders = new(new MaterialProvidersConfig());
        private static KeyVectorsConfig keyVectorsConfig = new KeyVectorsConfig();
        private static KeyVectors keyVectors;

        public static ICryptographicMaterialsManager CreateDecryptCmm(
            DecryptVector vector,
            Dictionary<string, Key> keys, 
            string vectorId
            ) {
            ICryptographicMaterialsManager cmm;
            ICryptographicMaterialsManager defaultCMM = materialProviders.CreateDefaultCryptographicMaterialsManager(
                new CreateDefaultCryptographicMaterialsManagerInput
                {
                    Keyring = CreateDecryptKeyring(vector, keys)
                });
            switch (vector.CMM)
            {
                case "RequiredEncryptionContext":
                    if (vector.EncryptionContext is null)
                    {
                        throw new Utils.InvalidDecryptVectorException(
                            $"RequiredEncryptionContext requires Encryption Context! ID = {vector}");
                    }
                    CreateRequiredEncryptionContextCMMInput requiredCMM = new CreateRequiredEncryptionContextCMMInput
                    {
                        UnderlyingCMM = defaultCMM,
                        RequiredEncryptionContextKeys = new List<string>(vector.EncryptionContext.Keys)
                    };
                    cmm = materialProviders.CreateRequiredEncryptionContextCMM(requiredCMM);
                    break;
                default:
                    cmm = defaultCMM;
                    break;
            }
            return cmm; 
        }

        private static IKeyring CreateDecryptKeyring(DecryptVector vector, Dictionary<string, Key> keys) {
            List<IKeyring> children = new List<IKeyring>();
            Debug.Assert(vector.MasterKeys != null, "vector.MasterKeys != null");
            foreach (MasterKey keyInfo in vector.MasterKeys)
            {
                // Some keyrings, like discovery KMS keyrings, do not specify keys
                Key key = keyInfo.Key == null ? null : keys[keyInfo.Key];
                children.Add(CreateKeyring(keyInfo, key, CryptoOperation.DECRYPT));
            }
            CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput
            {
                Generator = null,
                ChildKeyrings = children
            };

            return materialProviders.CreateMultiKeyring(createMultiKeyringInput);
        }

        public static ICryptographicMaterialsManager CreateEncryptCmm(EncryptVector vector,
            Dictionary<string, Key> keys)
        {
            ICryptographicMaterialsManager cmm;
            ICryptographicMaterialsManager defaultCMM = materialProviders.CreateDefaultCryptographicMaterialsManager(
                new CreateDefaultCryptographicMaterialsManagerInput
                {
                    Keyring = CreateEncryptKeyring(vector, keys)
                });
            switch (vector.Scenario.CMM)
            {
                case "RequiredEncryptionContext":
                    CreateRequiredEncryptionContextCMMInput requiredCMM = new CreateRequiredEncryptionContextCMMInput
                    {
                        UnderlyingCMM = defaultCMM,
                        RequiredEncryptionContextKeys = new List<string>(vector.Scenario.EncryptionContext.Keys)
                    };
                    cmm = materialProviders.CreateRequiredEncryptionContextCMM(requiredCMM);
                    break;
                default:
                    cmm = defaultCMM;
                    break;
            }
            return cmm;
        }
        

        private static IKeyring CreateEncryptKeyring(EncryptVector vector, Dictionary<string, Key> keys)
        {
            IList<MasterKey> masterKeys = vector.Scenario.MasterKeys;
            Debug.Assert(masterKeys.Count >= 1);

            Key generatorKey = keys[masterKeys[0].Key];
            Console.WriteLine(generatorKey.BranchKey);
            IKeyring generatorKeyring = CreateKeyring(masterKeys[0], generatorKey, CryptoOperation.ENCRYPT);

            List<IKeyring> children = masterKeys
                .Skip(1)
                .Select(masterKey =>
                {
                    Key key = keys[masterKey.Key];
                    return CreateKeyring(masterKey, key, CryptoOperation.ENCRYPT);
                })
                .ToList();

            CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput
            {
                Generator = generatorKeyring,
                ChildKeyrings = children
            };
            return materialProviders.CreateMultiKeyring(createMultiKeyringInput);
        }

        private static IKeyring CreateKeyring(MasterKey keyInfo, Key key, CryptoOperation operation) {
            if (keyInfo.Type == "aws-kms") {
                CreateAwsKmsKeyringInput createKeyringInput = new CreateAwsKmsKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateAwsKmsKeyring(createKeyringInput);
            }
            if (keyInfo.Type == "aws-kms-mrk-aware") {
                CreateAwsKmsMrkKeyringInput createKeyringInput = new CreateAwsKmsMrkKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn(key.Id)),
                    KmsKeyId = key.Id,
                };
                return materialProviders.CreateAwsKmsMrkKeyring(createKeyringInput);
            }

            if (keyInfo.Type == "aws-kms-mrk-aware-discovery" && operation == CryptoOperation.DECRYPT) {
                AWS.Cryptography.MaterialProviders.DiscoveryFilter filter = null;
                if (keyInfo.AwsKmsDiscoveryFilter != null)
                {
                    filter = new AWS.Cryptography.MaterialProviders.DiscoveryFilter
                    {
                        AccountIds = (List<string>)keyInfo.AwsKmsDiscoveryFilter.AccountIds,
                        Partition = keyInfo.AwsKmsDiscoveryFilter.Partition,
                    };
                }

                CreateAwsKmsMrkDiscoveryKeyringInput createKeyringInput = new CreateAwsKmsMrkDiscoveryKeyringInput
                {
                    KmsClient = new AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(keyInfo.DefaultMrkRegion)),
                    Region = keyInfo.DefaultMrkRegion,
                    DiscoveryFilter = filter,
                };
                return materialProviders.CreateAwsKmsMrkDiscoveryKeyring(createKeyringInput);
            }

            if (keyInfo.Type == "aws-kms-hierarchy") {
                // keyInfo.Type = "static-branch-key-1";
                if (keyVectors == null) {
                    keyVectorsConfig.KeyManifestPath = "/Users/lucmcdon/Desktop/workplace/aws-encryption-sdk-python/net_vectors_test/312_hkeyring_manifest/keys.json";
                    keyVectors = new KeyVectors(keyVectorsConfig);
                }

                string jsonString = JsonConvert.SerializeObject(keyInfo);

                var stream = new MemoryStream();
                var writer = new StreamWriter(stream);
                writer.Write(jsonString);
                writer.Flush();
                stream.Position = 0;

                var getKeyDescriptionInput = new GetKeyDescriptionInput();
                getKeyDescriptionInput.Json = stream;

                var desc = keyVectors.GetKeyDescription(getKeyDescriptionInput);

                var testVectorKeyringInput = new TestVectorKeyringInput();
                testVectorKeyringInput.KeyDescription = desc.KeyDescription;
                
                var keyring = keyVectors.CreateTestVectorKeyring(
                    testVectorKeyringInput
                );

                Console.WriteLine(keyring);

                return keyring;

                // // TODO: When we have different keys, include the keystore KMS key ARN in the manifest.
                // var kmsConfig = new KMSConfiguration { KmsKeyArn = "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126" };
                // // Create an AWS KMS Configuration to use with your KeyStore.
                // // The KMS Configuration MUST have the right access to the resources in the KeyStore.
                // var keystoreConfig = new KeyStoreConfig
                // {
                //     // Client MUST have permissions to decrypt kmsConfig.KmsKeyArn
                //     KmsClient = new AmazonKeyManagementServiceClient(GetRegionForArn("arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126")),
                //     KmsConfiguration = kmsConfig,
                //     // TODO: Don't hardcode
                //     DdbTableName = "KeyStoreDdbTable",
                //     DdbClient = new AmazonDynamoDBClient(GetRegionForArn("arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126")),
                //     // TODO: Don't hardcode
                //     LogicalKeyStoreName = "KeyStoreDdbTable"
                // };
                // var keystore = new KeyStore(keystoreConfig);

                

                // Console.WriteLine(key.Id);
                // Console.WriteLine(key.BranchKeyVersion);

                // // Create an AWS Hierarchical Keyring with the branch key id supplier
                // var createKeyringInput = new CreateAwsKmsHierarchicalKeyringInput
                // {
                //     KeyStore = keystore,
                //     BranchKeyId = key.Id,
                //     Cache = new CacheType { Default = new DefaultCache{EntryCapacity = 100} },
                //     TtlSeconds = 0
                // };
                // return materialProviders.CreateAwsKmsHierarchicalKeyring(createKeyringInput);
                
            }

            if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "aes") {
                CreateRawAesKeyringInput createKeyringInput = new CreateRawAesKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    WrappingKey = new MemoryStream(Convert.FromBase64String(key.Material)),
                    WrappingAlg = AesAlgorithmFromBits(key.Bits),
                };

                return materialProviders.CreateRawAesKeyring(createKeyringInput);
            }

            if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "private") {
                PaddingScheme padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                byte[] privateKey = RSA.ParsePEMString(key.Material);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PrivateKey = new MemoryStream(privateKey)
                };

                // Extract the public key if we need to encrypt
                if (operation == CryptoOperation.ENCRYPT)
                {
                    byte[] publicKey = RSA.GetPublicKeyFromPrivateKeyPemString(key.Material);
                    createKeyringInput.PublicKey = new MemoryStream(publicKey);
                }

                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            }

            if (keyInfo.Type == "raw" && keyInfo.EncryptionAlgorithm == "rsa" && key.Type == "public") {
                PaddingScheme padding = RSAPaddingFromStrings(keyInfo.PaddingAlgorithm, keyInfo.PaddingHash);
                byte[] publicKey = RSA.ParsePEMString(key.Material);
                CreateRawRsaKeyringInput createKeyringInput = new CreateRawRsaKeyringInput
                {
                    KeyNamespace = keyInfo.ProviderId,
                    KeyName = key.Id,
                    PaddingScheme = padding,
                    PublicKey = new MemoryStream(publicKey)
                };
                return materialProviders.CreateRawRsaKeyring(createKeyringInput);
            }

            // string operationStr = operation == CryptoOperation.ENCRYPT
            //     ? "encryption"
            //     : "decryption";
            throw new Exception($"Unsupported keyring {keyInfo.Type} type for {operation}");
        }

        private static AesWrappingAlg AesAlgorithmFromBits(ushort bits) {
            switch (bits) {
                case 128:
                    return AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16;
                case 192:
                    return AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16;
                case 256:
                    return AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16;
                default: throw new Exception("Unsupported AES wrapping algorithm");
            }
        }

        private static PaddingScheme RSAPaddingFromStrings(string strAlg, string strHash) {
            switch (strAlg)
            {
                case "pkcs1":
                    return PaddingScheme.PKCS1;
                case "oaep-mgf1":
                    switch (strHash)
                    {
                        case "sha1": return PaddingScheme.OAEP_SHA1_MGF1;
                        case "sha256": return PaddingScheme.OAEP_SHA256_MGF1;
                        case "sha384": return PaddingScheme.OAEP_SHA384_MGF1;
                        case "sha512": return PaddingScheme.OAEP_SHA512_MGF1;
                    }
                    break;
            }
            throw new Exception("Unsupported RSA Padding " + strAlg + strHash);
        }

        private static RegionEndpoint GetRegionForArn(string keyId)
        {
            try
            {
                Arn arn = Arn.Parse(keyId);
                return RegionEndpoint.GetBySystemName(arn.Region);
            } catch (ArgumentException)
            {
                // Some of our test vector key definitions use a variety of
                // malformed key ids.
                // These are usually meant to fail (since decryption requires
                // matching configured key arns to ciphertext key arns),
                // but in order for them to fail correctly
                // we need to at least be able to create our client,
                // so we choose a default region
                return RegionEndpoint.GetBySystemName("us-west-2");

            }
        }
    }

}
