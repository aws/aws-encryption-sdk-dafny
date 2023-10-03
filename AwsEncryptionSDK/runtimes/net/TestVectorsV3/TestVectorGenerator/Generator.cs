// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace TestVectors {
    class Generator
    {
        private const string OutputKeysManifestUri = "file://keys.json";

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
            var quietOpt = new Option<bool>(name: "--quiet");

            var rootCommand = new RootCommand { encryptManifestFileOpt, outputDirOpt, quietOpt };
            rootCommand.SetHandler((FileInfo encryptManifestFile, DirectoryInfo outputDir, bool quiet) =>
            {
                new Generator(encryptManifestFile, outputDir, quiet).Run();
            }, encryptManifestFileOpt, outputDirOpt, quietOpt);
            rootCommand.Invoke(args);
        }

        private readonly EncryptManifest _encryptManifest;
        private readonly KeyManifest _keyManifest;
        private readonly DirectoryInfo _outputDir;
        private readonly DirectoryInfo _plaintextDir;
        private readonly DirectoryInfo _ciphertextDir;
        private readonly bool _quiet;

        private Generator(FileInfo encryptManifestFile, DirectoryInfo outputDir, bool quiet)
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

            _quiet = quiet;
        }

        private void Run()
        {
            var plaintexts = GeneratePlaintexts(_encryptManifest.PlaintextSizes);
            Utils.WriteNamedDataMap(_plaintextDir, plaintexts);
            Console.Error.WriteLine($"Wrote {plaintexts.Count} plaintext files");

            var targetedVectors = _encryptManifest.VectorMap
                .Where(pair => ShouldTargetVector(pair.Key, pair.Value))
                .ToList();
            var totalVectorCount = _encryptManifest.VectorMap.Count;
            Console.Error.WriteLine($"Targeting {targetedVectors.Count} out of {totalVectorCount} vectors");
            GenerateAndWriteVectors(targetedVectors, plaintexts);
            Console.Error.WriteLine($"Wrote {targetedVectors.Count} ciphertexts");

            DecryptManifest decryptManifest = GenerateDecryptManifest(targetedVectors, plaintexts);
            string decryptManifestPath = Path.Join(_outputDir.FullName, "manifest.json");
            Utils.WriteObjectToPath(decryptManifest, decryptManifestPath);
            Console.Error.WriteLine("Wrote decrypt vector manifest");

            // TODO resolve KMS aliases to ARNs, instead of copying them over
            var keysPath = Utils.ManifestUriToPath(OutputKeysManifestUri, decryptManifestPath);
            Utils.WriteObjectToPath(_keyManifest, keysPath);
            Console.Error.WriteLine("Wrote key manifest");
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
        // This could be a use case for Smithy enums' "tags" property, that we'd need to support in codegen.
        // https://awslabs.github.io/smithy/1.0/spec/core/constraint-traits.html#enum-trait
        private static readonly AlgorithmSuiteId[] COMMITTING_ALGORITHM_SUITES = {
            AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
            AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
        };

        /// <summary>
        /// Returns whether the generator should attempt to encrypt the given vector.
        /// Useful for selecting particular vectors when debugging.
        /// </summary>
        private bool ShouldTargetVector(string id, EncryptVector vector)
        {
            // We don't support encrypting unframed messages.
            return vector.Scenario.FrameSize != 0;
        }

        private void GenerateAndWriteVectors(
            IList<KeyValuePair<string, EncryptVector>> targetedVectors, Dictionary<string, MemoryStream> plaintexts)
        {
            foreach (var (id, vector) in targetedVectors)
            {
                try
                {
                    var ciphertext = GenerateDecryptVector(vector, plaintexts);
                    Utils.WriteBinaryFile(_ciphertextDir, id, ciphertext);
                    if (!_quiet)
                    {
                        Console.Error.WriteLine($"Wrote ciphertext file for vector {id}");
                    }
                }
                catch (AwsEncryptionSdkException ex)
                {
                    throw new ApplicationException($"Failed to encrypt vector {id}", ex);
                }
            }
        }

        private DecryptManifest GenerateDecryptManifest(
            IList<KeyValuePair<string, EncryptVector>> targetedVectors, Dictionary<string, MemoryStream> plaintexts)
        {
            var decryptVectors = new Dictionary<string, DecryptVector>();
            foreach (var (id, encryptVector) in targetedVectors)
            {
                var plaintextPath = "file://" + Path.Join(_plaintextDir.Name, encryptVector.Scenario.PlaintextName);
                var ciphertextPath = "file://" + Path.Join(_ciphertextDir.Name, id);
                decryptVectors[id] = new DecryptVector
                {
                    Ciphertext = ciphertextPath,
                    MasterKeys = encryptVector.Scenario.MasterKeys,
                    Result = new DecryptResult
                    {
                        Output = new DecryptOutput { Plaintext = plaintextPath }
                    }
                };
            }

            return new DecryptManifest
            {
                Meta = new ManifestMeta
                {
                    Type = "awses-decrypt",
                    // This manifest format is described by version 3 of "AWS Encryption SDK Message Decryption":
                    // https://github.com/awslabs/aws-crypto-tools-test-vector-framework/blob/master/features/0004-awses-message-decryption.md
                    //
                    // Although the Python ESDK's test vector handler would correctly handle/decrypt the vectors,
                    // it incorrectly rejects the version "3" during manifest loading,
                    // so for expedience we'll just advertise what Python can handle.
                    // TODO: fix Python's vector handler version validation, and change this value to 3
                    Version = 2
                },
                Client = new Client
                {
                    Name = "awslabs/aws-encryption-sdk-dafny",
                    // TODO pass this by env var
                    Version = "0.1.0-alpha"
                },
                KeysUri = OutputKeysManifestUri,
                VectorMap = decryptVectors
            };
        }

        private MemoryStream GenerateDecryptVector(
            EncryptVector vector, Dictionary<string, MemoryStream> plaintexts)
        {
            EncryptScenario scenario = vector.Scenario;

            AlgorithmSuiteId algSuiteId = new AlgorithmSuiteId("0x" + scenario.Algorithm);
            Debug.Assert(AlgorithmSuiteId.Values.Contains(algSuiteId));

            CommitmentPolicy commitmentPolicy = COMMITTING_ALGORITHM_SUITES.Contains(algSuiteId)
                ? CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
                : CommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            AwsEncryptionSdkConfig config = new AwsEncryptionSdkConfig
            {
                CommitmentPolicy = commitmentPolicy
            };
            IAwsEncryptionSdk client = AwsEncryptionSdkFactory.CreateAwsEncryptionSdk(config);
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
