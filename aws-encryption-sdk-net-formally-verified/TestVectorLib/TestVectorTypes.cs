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

    public class TestVector {
        public string Description { get; set; }
        public string Ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> MasterKeys { get; set; }

        public TestVectorResult Result { get; set; }
    }

    public class TestVectorResult
    {
        public TestVectorOutput Output { get; set; }
        public TestVectorError Error { get; set; }
    }

    public class TestVectorOutput
    {
        public string Plaintext { get; set; }
    }
    public class TestVectorError
    {
        [JsonProperty("error-description")]
        public string ErrorMessage { get; set; }
    }

    public class DecryptManifest {
        public Dictionary<string, TestVector> VectorMap { get; set; }
        public string Keys { get; set; }

        public DecryptManifest(Dictionary<string, TestVector> vectorMap, string keys) {
            this.VectorMap = vectorMap;
            this.Keys = keys;
        }
    }

}
