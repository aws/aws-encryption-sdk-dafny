// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections.Generic;
using Newtonsoft.Json;

namespace TestVectors
{
    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        public bool Decrypt { get; set; }
        public bool Encrypt { get; set; }
        public string Type { get; set; }
        [JsonProperty("key-id")]
        public string Id { get; set; }
        public string Algorithm { get; set; }
        public ushort Bits { get; set; }
        public string Encoding { get; set; }
        public string Material { get; set; }
    }

    public class KeyManifest
    {
        public Dictionary<string, Key> Keys { get; set; }
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        public string Type { get; set; }
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
    }

    public class DecryptVector {
        public string Description { get; set; }
        public string Ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }

        public DecryptResult Result { get; set; }
    }

    public class DecryptResult
    {
        public DecryptOutput Output { get; set; }
        public DecryptError Error { get; set; }
    }

    public class DecryptOutput
    {
        public string Plaintext { get; set; }
    }
    public class DecryptError
    {
        [JsonProperty("error-description")]
        public string ErrorMessage { get; set; }
    }

    public class DecryptManifest {
        [JsonProperty("tests")]
        public Dictionary<string, DecryptVector> VectorMap { get; set; }
        [JsonProperty("keys")]
        public string KeysUri { get; set; }
    }

    public class EncryptScenario
    {
        [JsonProperty("plaintext")]
        public string PlaintextName { get; set; }
        /// <summary>
        /// Hex string of algorithm suite ID
        /// </summary>
        [JsonProperty("algorithm")]
        public string Algorithm { get; set; }
        [JsonProperty("frame-size")]
        public uint FrameSize { get; set; }
        [JsonProperty("encryption-context")]
        public Dictionary<string, string> EncryptionContext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }
    }

    public class EncryptVector
    {
        [JsonProperty("encryption-scenario")]
        public EncryptScenario Scenario { get; set; }

        // TODO create tampered messages
        // [JsonProperty("tampering")]
        // public string Tampering { get; set; }
    }

    public class EncryptManifest
    {
        [JsonProperty("tests")]
        public Dictionary<string, EncryptVector> VectorMap { get; set; }
        [JsonProperty("plaintexts")]
        public Dictionary<string, uint> PlaintextSizes { get; set; }
        [JsonProperty("keys")]
        public string KeysUri { get; set; }
    }
}
