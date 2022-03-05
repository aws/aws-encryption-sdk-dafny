// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using Aws.Crypto;
using Aws.Esdk;
using ConfigurationDefaults = Aws.Esdk.ConfigurationDefaults;

namespace TestVectors {
    class Generator
    {
        static void Main(string[] args)
        {
            var encryptManifestFileOpt = new Option<FileInfo>(name: "--encrypt-manifest")
            {
                IsRequired = true
            };
            var outputDirOpt = new Option<DirectoryInfo>(name: "--output-dir")
            {
                IsRequired = true
            };

            var rootCommand = new RootCommand { encryptManifestFileOpt, outputDirOpt };
            rootCommand.SetHandler((FileInfo encryptManifestFile, DirectoryInfo outputDir) =>
            {
                new Generator(encryptManifestFile, outputDir).Run();
            }, encryptManifestFileOpt, outputDirOpt);
            rootCommand.Invoke(args);
        }

        private readonly EncryptManifest _encryptManifest;
        private readonly KeyManifest _keyManifest;
        private readonly DirectoryInfo _outputDir;
        private readonly DirectoryInfo _plaintextDir;
        private readonly DirectoryInfo _ciphertextDir;

        public Generator(FileInfo encryptManifestFile, DirectoryInfo outputDir)
        {
            _encryptManifest = Utils.LoadObjectFromPath<EncryptManifest>(encryptManifestFile.FullName);
            Console.Error.WriteLine(
                $"Loaded {_encryptManifest.VectorMap.Count} vectors from {encryptManifestFile.FullName}");
            string keysPath = Utils.ManifestUriToPath(_encryptManifest.KeysUri, encryptManifestFile.FullName);
            _keyManifest = Utils.LoadObjectFromPath<KeyManifest>(keysPath);

            if (!outputDir.Exists)
            {
                outputDir.Create();
            }

            if (outputDir.GetFileSystemInfos().Length != 0)
            {
                throw new ArgumentException("Output directory not empty");
            }

            _outputDir = outputDir;
            _plaintextDir = outputDir.CreateSubdirectory("plaintexts");
            _ciphertextDir = outputDir.CreateSubdirectory("ciphertexts");
        }

        public void Run()
        {
            var plaintexts = GeneratePlaintexts(_encryptManifest.PlaintextSizes);
            Utils.WriteNamedDataMap(_plaintextDir, plaintexts);
            Console.Error.WriteLine($"Wrote {plaintexts.Count} plaintext files");

            foreach (var (id, vector) in _encryptManifest.VectorMap)
            {
                try
                {
                    var ciphertext = GenerateDecryptVector(vector, plaintexts);
                    Utils.WriteBinaryFile(_ciphertextDir, id, ciphertext);
                    Console.Error.WriteLine($"Wrote ciphertext file for vector {id}");
                }
                catch (AwsEncryptionSdkException ex)
                {
                    throw new ApplicationException($"Failed to encrypt vector {id}", ex);
                }
            }

            // TODO copy key manifest

            // TODO write decrypt manifest
        }

        private static Dictionary<string, MemoryStream> GeneratePlaintexts(Dictionary<string, uint> sizes)
        {
            var plaintexts = new Dictionary<string, MemoryStream>();
            foreach (var (name, size) in sizes)
            {
                if (size > int.MaxValue)
                {
                    throw new ArgumentException($"Can't generate a {size}-byte plaintext");
                }

                var buffer = new MemoryStream((int)size);
                RandomNumberGenerator.Fill(buffer.GetBuffer());
                plaintexts.Add(name, buffer);
            }

            return plaintexts;
        }

        // We don't have a better way to query this information right now.
        // This could be use case for Smithy enums' "tags" property, that we'd need to support in codegen.
        // https://awslabs.github.io/smithy/1.0/spec/core/constraint-traits.html#enum-trait
        private static readonly AlgorithmSuiteId[] COMMITTING_ALGORITHM_SUITES = {
            AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
            AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
        };

        private MemoryStream GenerateDecryptVector(
            EncryptVector vector, Dictionary<string, MemoryStream> plaintexts)
        {
            EncryptScenario scenario = vector.Scenario;

            AlgorithmSuiteId algSuiteId = new AlgorithmSuiteId("0x" + scenario.Algorithm);
            Debug.Assert(AlgorithmSuiteId.Values.Contains(algSuiteId));

            CommitmentPolicy commitmentPolicy = COMMITTING_ALGORITHM_SUITES.Contains(algSuiteId)
                ? CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
                : CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            AwsEncryptionSdkClientConfig config = new AwsEncryptionSdkClientConfig
            {
                ConfigDefaults = ConfigurationDefaults.V1,
                CommitmentPolicy = commitmentPolicy
            };
            IAwsEncryptionSdk client = new AwsEncryptionSdkClient(config);
            ICryptographicMaterialsManager cmm = MaterialProviderFactory.CreateEncryptCmm(vector, _keyManifest.Keys);

            EncryptInput encryptInput = new EncryptInput
            {
                AlgorithmSuiteId = algSuiteId,
                EncryptionContext = scenario.EncryptionContext,
                FrameLength = scenario.FrameSize,
                MaterialsManager = cmm,
                Plaintext = plaintexts[scenario.PlaintextName]
            };
            return client.Encrypt(encryptInput).Ciphertext;
        }
    }
}
