// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.CommandLine;
using System.Security.Cryptography;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;

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
        private RandomNumberGenerator _randomNumberGenerator;

        private Generator(FileInfo encryptManifestFile, DirectoryInfo outputDir, bool quiet)
        {
            _randomNumberGenerator = RandomNumberGenerator.Create();
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
            string decryptManifestPath = Path.Combine(_outputDir.FullName, "manifest.json");
            Utils.WriteObjectToPath(decryptManifest, decryptManifestPath);
            Console.Error.WriteLine("Wrote decrypt vector manifest");

            // TODO resolve KMS aliases to ARNs, instead of copying them over
            var keysPath = Utils.ManifestUriToPath(OutputKeysManifestUri, decryptManifestPath);
            Utils.WriteObjectToPath(_keyManifest, keysPath);
            Console.Error.WriteLine("Wrote key manifest");
        }

        private Dictionary<string, MemoryStream> GeneratePlaintexts(Dictionary<string, uint> sizes)
        {
            var plaintexts = new Dictionary<string, MemoryStream>();
            foreach (var entry in sizes)
            {
                if (entry.Value > int.MaxValue)
                {
                    throw new ArgumentException($"Can't generate a {entry.Value}-byte plaintext");
                }
                var bytes = new byte[(int)entry.Value];
                _randomNumberGenerator.GetBytes(bytes);
                var buffer = new MemoryStream(bytes);
                plaintexts.Add(entry.Key, buffer);
            }

            return plaintexts;
        }

        private static readonly ESDKAlgorithmSuiteId[] COMMITTING_ALGORITHM_SUITES = {
            ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
            ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
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
            IList<KeyValuePair<string, EncryptVector>> targetedVectors, 
            Dictionary<string, MemoryStream> plaintexts
            ) 
        {
            foreach (var entry in targetedVectors)
            {
                try
                {
                    var ciphertext = GenerateDecryptVector(entry.Value, plaintexts);
                    Utils.WriteBinaryFile(_ciphertextDir, entry.Key, ciphertext);
                    if (!_quiet)
                    {
                        Console.Error.WriteLine($"Wrote ciphertext file for vector {entry.Key}");
                    }
                }
                catch (AwsEncryptionSdkException ex)
                {
                    throw new ApplicationException($"Failed to encrypt vector {entry.Key}", ex);
                }
            }
        }

        private DecryptManifest GenerateDecryptManifest(
            IList<KeyValuePair<string, EncryptVector>> targetedVectors, Dictionary<string, MemoryStream> plaintexts)
        {
            var decryptVectors = new Dictionary<string, DecryptVector>();
            foreach (var entry in targetedVectors)
            {
                var plaintextPath = "file://" + Path.Combine(_plaintextDir.Name, entry.Value.Scenario.PlaintextName);
                var ciphertextPath = "file://" + Path.Combine(_ciphertextDir.Name, entry.Key);
                decryptVectors[entry.Key] = new DecryptVector
                {
                    Ciphertext = ciphertextPath,
                    MasterKeys = entry.Value.Scenario.MasterKeys,
                    CMM = entry.Value.Scenario.CMM,
                    EncryptionContext = entry.Value.Scenario.EncryptionContext,
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
                    Version = 4
                },
                Client = new Client
                {
                    Name = "ESDK-NET",
                    // TODO pass this by env var
                    Version = "4.0.0"
                },
                KeysUri = OutputKeysManifestUri,
                VectorMap = decryptVectors
            };
        }

        private MemoryStream GenerateDecryptVector(
            EncryptVector vector, Dictionary<string, MemoryStream> plaintexts)
        {
            EncryptScenario scenario = vector.Scenario;

            ESDKAlgorithmSuiteId algSuiteId = new ESDKAlgorithmSuiteId("0x" + scenario.Algorithm);

            ESDKCommitmentPolicy commitmentPolicy = COMMITTING_ALGORITHM_SUITES.Contains(algSuiteId)
                ? ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
                : ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT;
            AwsEncryptionSdkConfig config = new AwsEncryptionSdkConfig
            {
                CommitmentPolicy = commitmentPolicy
            };
            ESDK encryptionSdk = new ESDK(config);
            ICryptographicMaterialsManager cmm = MaterialProviderFactory.CreateEncryptCmm(vector, _keyManifest.Keys);

            EncryptInput encryptInput = new EncryptInput
            {
                AlgorithmSuiteId = algSuiteId,
                EncryptionContext = scenario.EncryptionContext,
                FrameLength = scenario.FrameSize,
                MaterialsManager = cmm,
                Plaintext = plaintexts[scenario.PlaintextName]
            };
            return encryptionSdk.Encrypt(encryptInput).Ciphertext;
        }
    }
}
