// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections.Generic;
using Newtonsoft.Json;

namespace TestVectors
{
    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        [JsonProperty("decrypt")]
        public bool Decrypt { get; set; }
        [JsonProperty("encrypt")]
        public bool Encrypt { get; set; }
        [JsonRequired]
        [JsonProperty("type")]
        public string Type { get; set; }
        [JsonRequired]
        [JsonProperty("key-id")]
        public string Id { get; set; }
        [JsonProperty("algorithm")]
        public string Algorithm { get; set; }
        [JsonProperty("bits")]
        public ushort Bits { get; set; }
        [JsonProperty("encoding")]
        public string Encoding { get; set; }
        [JsonProperty("material")]
        public string Material { get; set; }
    }

    public class KeyManifest
    {
        [JsonRequired]
        [JsonProperty("manifest")]
        public ManifestMeta Meta { get; set; }
        [JsonRequired]
        [JsonProperty("keys")]
        public Dictionary<string, Key> Keys { get; set; }
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        [JsonProperty("type")]
        public string Type { get; set; }
        [JsonProperty("key")]
        public string Key { get; set; }
        [JsonProperty("provider-id")]
        public string ProviderId { get; set; }
        [JsonProperty("encryption-algorithm")]
        public string EncryptionAlgorithm { get; set; }
        [JsonProperty("padding-algorithm")]
        public string PaddingAlgorithm { get; set; }
        [JsonProperty("padding-hash")]
        public string PaddingHash { get; set; }
        [JsonProperty("default-mrk-region")]
        public string DefaultMrkRegion { get; set; }
        [JsonProperty("aws-kms-discovery-filter")]
        public DiscoveryFilter AwsKmsDiscoveryFilter { get; set; }
    }

    public class DiscoveryFilter
    {
        [JsonProperty("partition")]
        public string Partition { get; set; }
        [JsonProperty("account-ids")]
        public IList<string> AccountIds { get; set; }
    }

    public class DecryptVector {
        [JsonProperty("description")]
        public string Description { get; set; }
        [JsonRequired]
        [JsonProperty("ciphertext")]
        public string Ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }
        [JsonProperty("result")]
        public DecryptResult Result { get; set; }
        [JsonProperty("decryption-method")]
        public string DecryptionMethod { get; set; }
    }

    public class DecryptResult
    {
        [JsonProperty("output")]
        public DecryptOutput Output { get; set; }
        [JsonProperty("error")]
        public DecryptError Error { get; set; }
    }

    public class DecryptOutput
    {
        [JsonProperty("plaintext")]
        public string Plaintext { get; set; }
    }
    public class DecryptError
    {
        [JsonProperty("error-description")]
        public string ErrorMessage { get; set; }
    }

    public class DecryptManifest {
        [JsonRequired]
        [JsonProperty("manifest")]
        public ManifestMeta Meta { get; set; }
        [JsonRequired]
        [JsonProperty("client")]
        public Client Client { get; set; }
        [JsonRequired]
        [JsonProperty("keys")]
        public string KeysUri { get; set; }
        [JsonRequired]
        [JsonProperty("tests")]
        public Dictionary<string, DecryptVector> VectorMap { get; set; }
    }

    public class EncryptScenario
    {
        [JsonRequired]
        [JsonProperty("plaintext")]
        public string PlaintextName { get; set; }
        /// <summary>
        /// Hex string of algorithm suite ID
        /// </summary>
        [JsonRequired]
        [JsonProperty("algorithm")]
        public string Algorithm { get; set; }
        [JsonRequired]
        [JsonProperty("frame-size")]
        public uint FrameSize { get; set; }
        [JsonRequired]
        [JsonProperty("encryption-context")]
        public Dictionary<string, string> EncryptionContext { get; set; }
        [JsonRequired]
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }
    }

    public class EncryptVector
    {
        [JsonRequired]
        [JsonProperty("encryption-scenario")]
        public EncryptScenario Scenario { get; set; }

        // TODO create tampered messages
        // [JsonProperty("tampering")]
        // public string Tampering { get; set; }
    }

    public class EncryptManifest
    {
        [JsonRequired]
        [JsonProperty("manifest")]
        public ManifestMeta Meta { get; set; }
        [JsonRequired]
        [JsonProperty("keys")]
        public string KeysUri { get; set; }
        [JsonRequired]
        [JsonProperty("plaintexts")]
        public Dictionary<string, uint> PlaintextSizes { get; set; }
        [JsonRequired]
        [JsonProperty("tests")]
        public Dictionary<string, EncryptVector> VectorMap { get; set; }
    }

    public class ManifestMeta
    {
        [JsonRequired]
        [JsonProperty("type")]
        public string Type { get; set; }
        [JsonRequired]
        [JsonProperty("version")]
        public int Version { get; set; }
    }

    public class Client
    {
        [JsonRequired]
        [JsonProperty("name")]
        public string Name { get; set; }
        [JsonRequired]
        [JsonProperty("version")]
        public string Version { get; set; }
    }
}
