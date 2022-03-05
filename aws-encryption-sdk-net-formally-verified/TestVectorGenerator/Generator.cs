// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics;
using System.IO;
using System.Security.Cryptography;

namespace TestVectors {
    class Generator
    {
        static void Main(string[] args)
        {
            var encryptManifestFileOpt = new Option<FileInfo>(name: "--encrypt-manifest");
            encryptManifestFileOpt.IsRequired = true;
            var outputDirOpt = new Option<DirectoryInfo>(name: "--output-dir");
            outputDirOpt.IsRequired = true;

            var rootCommand = new RootCommand { encryptManifestFileOpt, outputDirOpt };
            rootCommand.SetHandler((FileInfo encryptManifestFile, DirectoryInfo outputDir) =>
            {
                new Generator(encryptManifestFile, outputDir).Run();
            }, encryptManifestFileOpt, outputDirOpt);
            rootCommand.Invoke(args);
        }

        private readonly EncryptManifest _encryptManifest;
        private readonly DirectoryInfo _outputDir;
        private readonly DirectoryInfo _plaintextDir;
        private readonly DirectoryInfo _ciphertextDir;

        public Generator(FileInfo encryptManifestFile, DirectoryInfo outputDir)
        {
            _encryptManifest = Utils.LoadObjectFromPath<EncryptManifest>(encryptManifestFile.FullName);
            Console.Error.WriteLine(
                $"Loaded {_encryptManifest.VectorMap.Count} vectors from {encryptManifestFile.FullName}");

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
            WritePlaintextFiles(plaintexts);
            Console.Error.WriteLine($"Wrote {plaintexts.Count} plaintext files");
        }

        private static Dictionary<string, MemoryStream> GeneratePlaintexts(Dictionary<string, uint> sizes)
        {
            Dictionary<string, MemoryStream> plaintexts = new Dictionary<string, MemoryStream>();
            foreach (var nameSizePair in sizes)
            {
                uint size = nameSizePair.Value;
                if (size > int.MaxValue)
                {
                    throw new ArgumentException($"Can't generate a {size}-byte plaintext");
                }
                MemoryStream buffer = new MemoryStream((int) size);
                RandomNumberGenerator.Fill(buffer.GetBuffer());
                plaintexts.Add(nameSizePair.Key, buffer);
            }

            return plaintexts;
        }

        private void WritePlaintextFiles(Dictionary<string, MemoryStream> plaintexts)
        {
            foreach (var nameBufferPair in plaintexts)
            {
                string path = Path.Join(_plaintextDir.FullName, nameBufferPair.Key);
                FileInfo fileInfo = new FileInfo(path);
                Debug.Assert(!fileInfo.Exists);
                fileInfo.Create();
            }
        }
    }
}
