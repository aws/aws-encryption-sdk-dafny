using System;
using System.Text;
using Newtonsoft.Json.Linq;
using System.Linq;
using System.Collections.Generic;

using byteseq = Dafny.Sequence<byte>;
using vectorseq = Dafny.Sequence<TestVectorExterns.TestCase>;

namespace TestVectorExterns {
    public partial class __default {
        public static STL.Result<byteseq> ReadFile(Dafny.Sequence<char> path) {
            byte[] contents;
            try {
                contents = System.IO.File.ReadAllBytes(new string(path.Elements));
            } catch(Exception e) {
                return new STL.Result_Failure<byteseq>(Dafny.Sequence<char>.FromString("Error reading file: " + e.ToString()));
            }

            return new STL.Result_Success<byteseq>(byteseq.FromArray(contents));
        }

        public static STL.Result<Dafny.Sequence<TestVectorExterns.Key>> ParseKeys(Dafny.Sequence<char> contents) {
            JObject keyManifest = JObject.Parse(new string (contents.Elements));
            IList<JToken> keys = keyManifest["keys"].Children().ToList();
            IList<TestVectorExterns.Key> parsedKeys = new List<TestVectorExterns.Key>();
            foreach (JToken key in keys) {
                bool encrypt = key.First()["encrypt"].ToObject<bool>();

                bool decrypt = key.First()["decrypt"].ToObject<bool>();
                Dafny.Sequence<char> keyType = Dafny.Sequence<char>.FromString(key.First()["type"].ToString());

                Dafny.Sequence<char> keyID = Dafny.Sequence<char>.FromString(key.First()["key-id"].ToString());
                
                Dafny.Sequence<char> keyIndex = Dafny.Sequence<char>.FromString(key.Value<JProperty>().Name);

                STL.Option<Dafny.Sequence<char>> algorithm = new STL.Option_None<Dafny.Sequence<char>>();
                if (key.First()["algorithm"] != null) {
                    algorithm = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key.First()["algorithm"].ToString()));
                }

                STL.Option<ushort> bits = new STL.Option_None<ushort>();
                if (key.First()["bits"] != null) {
                    bits = new STL.Option_Some<ushort>(key.First()["bits"].ToObject<ushort>());
                }

                STL.Option<Dafny.Sequence<char>> encoding = new STL.Option_None<Dafny.Sequence<char>>();
                if (key.First()["encoding"] != null) {
                    encoding = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key.First()["encoding"].ToString()));
                }

                STL.Option<Dafny.Sequence<char>> material = new STL.Option_None<Dafny.Sequence<char>>();
                if (key.First()["material"] != null) {
                    material = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key.First()["material"].ToString()));
                }

                TestVectorExterns.Key parsedKey = new TestVectorExterns.Key(encrypt, decrypt, keyType, keyID, algorithm, bits, encoding, material, keyIndex);
                parsedKeys.Add(parsedKey);
            }
            TestVectorExterns.Key[] keyArray = parsedKeys.Cast<TestVectorExterns.Key>().ToArray();

            return new STL.Result_Success<Dafny.Sequence<TestVectorExterns.Key>>(Dafny.Sequence<TestVectorExterns.Key>.FromArray(keyArray));
        }

        public static STL.Result<vectorseq> ParseManifest(Dafny.Sequence<char> contents, Dafny.Map<Dafny.Sequence<char>, TestVectorExterns.Key> keyList) {
            JObject manifest = JObject.Parse(new string (contents.Elements));
            IList<JToken> tests = manifest["tests"].Children().ToList();
            IList<TestVectorExterns.TestCase> testVectors = new List<TestVectorExterns.TestCase>();
            foreach (JToken test in tests)
            {
                IList<JToken> keys = test.First()["master-keys"].Children().ToList();
                IList<TestVectorExterns.MasterKey> parsedKeys = new List<TestVectorExterns.MasterKey>();
                foreach (JToken key in keys) {
                    Dafny.Sequence<char> masterKeyType = Dafny.Sequence<char>.FromString(key["type"].ToString());
                    Dafny.Sequence<char> materialID = Dafny.Sequence<char>.FromString(key["key"].ToString());
                    if (!keyList.Contains(materialID)) {
                        return new STL.Result_Failure<vectorseq>(Dafny.Sequence<char>.FromString("Missing key from keylist: " + materialID));
                    }

                    TestVectorExterns.Key material = keyList.Select(materialID);

                    STL.Option<Dafny.Sequence<char>> providerID = new STL.Option_None<Dafny.Sequence<char>>();
                    if (key["provider-id"] != null) {
                        providerID = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key["provider-id"].ToString()));
                    }

                    STL.Option<Dafny.Sequence<char>> encryptionAlgorithm = new STL.Option_None<Dafny.Sequence<char>>();
                    if (key["encryption-algorithm"] != null) {
                        encryptionAlgorithm = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key["encryption-algorithm"].ToString()));
                    }

                    STL.Option<Dafny.Sequence<char>> paddingAlgorithm = new STL.Option_None<Dafny.Sequence<char>>();
                    if (key["padding-algorithm"] != null) {
                        paddingAlgorithm = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key["padding-algorithm"].ToString()));
                    }

                    STL.Option<Dafny.Sequence<char>> paddingHash = new STL.Option_None<Dafny.Sequence<char>>();
                    if (key["padding-hash"] != null) {
                        paddingHash = new STL.Option_Some<Dafny.Sequence<char>>(Dafny.Sequence<char>.FromString(key["padding-hash"].ToString()));
                    }

                    TestVectorExterns.MasterKey parsedKey = new TestVectorExterns.MasterKey(masterKeyType, material, providerID, encryptionAlgorithm, paddingAlgorithm, paddingHash);
                    parsedKeys.Add(parsedKey);
                }
                Dafny.Sequence<char> testID = Dafny.Sequence<char>.FromString(test.Value<JProperty>().Name);
                Dafny.Sequence<char> plaintext = Dafny.Sequence<char>.FromString(test.First()["plaintext"].ToString());
                Dafny.Sequence<char> ciphertext = Dafny.Sequence<char>.FromString(test.First()["ciphertext"].ToString());
                TestVectorExterns.TestCase testVector = new TestVectorExterns.TestCase(testID, plaintext, ciphertext, Dafny.Sequence<TestVectorExterns.MasterKey>.FromArray(parsedKeys.Cast<TestVectorExterns.MasterKey>().ToArray()));
                testVectors.Add(testVector);
            }
            TestVectorExterns.TestCase[] vectorArray = testVectors.Cast<TestVectorExterns.TestCase>().ToArray();

            return new STL.Result_Success<vectorseq>(vectorseq.FromArray(vectorArray));
        }
    }
}
