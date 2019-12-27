using CommandLine;
using System;
using System.Text;
using Newtonsoft.Json.Linq;
using System.Linq;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using AWSEncryptionSDK;
using KeyringDefs;
using KMSUtils;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using Newtonsoft.Json;

namespace TestVectors {

    // TODO Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class Key {
        [JsonProperty("decrypt")]
        public bool decrypt { get; set; }
        [JsonProperty("encrypt")]
        public bool encrypt { get; set; }
        [JsonProperty("type")]
        public string type { get; set; }
        [JsonProperty("key-id")]
        public string ID { get; set; }
        [JsonProperty("algorithm")]
        public string algorithm { get; set; }
        [JsonProperty("bits")]
        public ushort bits { get; set; }
        [JsonProperty("encoding")]
        public string encoding { get; set; }
        [JsonProperty("material")]
        public string material { get; set; }  
    }

    // TODO Rename? Need to use some enums for various fields, possibly subtypes to represent RSA vs AES having different params?
    public class MasterKey {
        [JsonProperty("type")]
        public string type { get; set; }
        [JsonProperty("key")]
        public string key { get; set; } // TODO or load Key directly?
        [JsonProperty("provider-id")]
        public string providerID { get; set; }
        [JsonProperty("encryption-algorithm")]
        public string encryptionAlgorithm { get; set; }
        [JsonProperty("padding-algorithm")]
        public string paddingAlgorithm { get; set; }
        [JsonProperty("padding-hash")]
        public string paddingHash { get; set; }
    }

    public class TestVector {
        [JsonProperty("plaintext")]
        public string plaintext { get; set; }
        [JsonProperty("ciphertext")]
        public string ciphertext { get; set; }
        [JsonProperty("master-keys")]
        public IList<MasterKey> masterKeys { get; set; }
    }

    public partial class __default {

        public static Dictionary<string, Key> ParseKeys(string path) {
            string contents = System.IO.File.ReadAllText(path);
            JObject keyManifest = JObject.Parse(contents);
            return keyManifest["keys"].ToObject<Dictionary<string, Key>>();
        }

        public static Dictionary<string, TestVector> ParseVectorsFromManifest(string path) {
            string contents = System.IO.File.ReadAllText(path);
            JObject manifest = JObject.Parse(contents);
            return manifest["tests"].ToObject<Dictionary<string, TestVector>>();
        }

        public static string TestURIToPath(string uri) {
            // TODO clean up. currently assumes starts with file://
            return uri.Substring(7);
        }
        private static MultiKeyring CreateEncryptKeyring(TestVector vector, Dictionary<string, Key> keys)
        {
            Keyring generator = CreateKeyring(vector.masterKeys[0], keys[vector.masterKeys[0].key]);
            IList<Keyring> children = vector.masterKeys.Skip(1).Select<MasterKey, Keyring>(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.key])).ToList();
            return Keyrings.MakeMultiKeyring(generator, children.ToArray());
        }
        private static MultiKeyring CreateDecryptKeyring(TestVector vector, Dictionary<string, Key> keys)
        {
            IList<Keyring> children = vector.masterKeys.Select<MasterKey, Keyring>(keyInfo => CreateKeyring(keyInfo, keys[keyInfo.key])).ToList();
            return Keyrings.MakeMultiKeyring(null, children.ToArray());
        }
        private static Keyring CreateKeyring(MasterKey keyInfo, Key key)
        {
            if (keyInfo.type == "aws-kms" && key.type == "aws-kms")
            {
                ClientSupplier clientSupplier = new DefaultClientSupplier();
                return Keyrings.MakeKMSKeyring(clientSupplier, Enumerable.Empty<String>(), key.ID, Enumerable.Empty<String>());
            }
            else if (keyInfo.type == "raw" && keyInfo.encryptionAlgorithm == "aes" && key.type == "symmetric")
            {
                EncryptionSuites.EncryptionSuite wrappingAlgorithm = BitsToAESWrappingSuite(key.bits);
                if (key.encoding != "base64")
                {
                    throw new Exception("Unsupported AES material encoding.");
                }
                return Keyrings.MakeRawAESKeyring(
                        Encoding.UTF8.GetBytes(keyInfo.providerID),
                        Encoding.UTF8.GetBytes(key.ID),
                        Encoding.UTF8.GetBytes(key.material),
                        BitsToAESWrappingSuite(key.bits)
                        );
            }
            else if (keyInfo.type == "raw" && keyInfo.encryptionAlgorithm == "rsa" && (key.type == "public" || key.type == "private"))
            {
                //Do we need to do anything with the key.bits field?
                return Keyrings.MakeRawRSAKeyring(
                        Encoding.UTF8.GetBytes(keyInfo.providerID),
                        Encoding.UTF8.GetBytes(key.ID),
                        RSAPAddingFromStrings(keyInfo.paddingAlgorithm, keyInfo.paddingHash),
                        key.type == "public" ? Encoding.UTF8.GetBytes(key.material) : null,
                        key.type == "private" ? Encoding.UTF8.GetBytes(key.material) : null
                        );
            }
            else
            {
                throw new Exception("Unsupported keyring type!");
            }
        }
        private static DafnyFFI.RSAPaddingModes RSAPAddingFromStrings(string strAlg, string strHash)
        {
            return (strAlg, strHash) switch
            {
                ("pkcs1", _) => DafnyFFI.RSAPaddingModes.PKCS1,
                    ("oaep-mgf1", "sha1") => DafnyFFI.RSAPaddingModes.OAEP_SHA1,
                    ("oaep-mgf1", "sha256") => DafnyFFI.RSAPaddingModes.OAEP_SHA256,
                    ("oaep-mgf1", "sha384") => throw new NotYetSupportedException("sha382"), //Dafny.RSAPaddingModes.OAEP_SHA384,
                    ("oaep-mgf1", "sha512") => throw new NotYetSupportedException("sha512"), //Dafny.RSAPaddingModes.OAEP_SHA512,
                    _ => throw new Exception("Unspoorted RSA Padding " + strAlg + strHash)
            };
        }
        private static EncryptionSuites.EncryptionSuite BitsToAESWrappingSuite(ushort bits)
        {
            switch(bits) {
                case 128: return DafnyFFI.EncryptionSuiteProvider.AES_GCM_128;
                case 192: return DafnyFFI.EncryptionSuiteProvider.AES_GCM_192;
                case 256: return DafnyFFI.EncryptionSuiteProvider.AES_GCM_256;
                default: throw new Exception("Unsupported AES Wrapping algorithm");
            }
        }

        // CLI Options
        [Verb("encrypt", HelpText = "Test encrypt against test vectors")]
        class EncryptOptions {
            [Option('d', "vectorDir", Required = true, HelpText = "a path to aws-crypto-tools-test-vector-framework unzipped directory")]
            public string vectorDir {get; set;}

            [Option('o', "decryptOracle", Required = true, HelpText = "a url to the decrypt oracle")]
            public string decryptOracle {get; set;}

            [Option('f', "tolerateFailures", Required = false, HelpText = "Maximum acceptable number of failures")]
            public int tolerateFailures {get; set;}
        }

        [Verb("decrypt", HelpText = "Test decrypt against test vectors")]
        class DecryptOptions {
            [Option('d', "vectorDir", Required = true, HelpText = "a path to aws-crypto-tools-test-vector-framework unzipped directory")]
            public string vectorDir {get; set;}

            [Option('f', "tolerateFailures", Required = false, HelpText = "Maximum acceptable number of failures")]
            public int tolerateFailures {get; set;}
        }

        private static Tuple<int, int, int> IntegrationEncryptTestVectors(EncryptOptions options)
        {
            string vectorDir = options.vectorDir;
            string decryptOracle = options.decryptOracle;
            int tolerateFailures = options.tolerateFailures;

            Dictionary<string, Key> keyMap = ParseKeys(Path.Combine(vectorDir, "keys.json")); //TODO should get this from manifest
            Dictionary<string, TestVector> vectorMap = ParseVectorsFromManifest(Path.Combine(vectorDir, "manifest.json"));

            Uri uri = new Uri(decryptOracle);
            HttpClient client = new HttpClient();
            client.DefaultRequestHeaders.Add("Accept", "application/octet-stream");

            int passCount = 0;
            int skipCount = 0;
            int failCount = 0;

            //TODO Parallelize this
            foreach(var vectorEntry in vectorMap) {
                TestVector vector = vectorEntry.Value;

                byte[] plaintext = System.IO.File.ReadAllBytes(TestURIToPath(vector.plaintext)); //TODO Randomly generate this?
                Keyring keyring;
                try {
                    keyring = CreateEncryptKeyring(vector, keyMap);
                } catch(NotYetSupportedException e) {
                    skipCount++;
                    continue;
                }

                CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
                MemoryStream plaintextStream = new MemoryStream(plaintext);

                try{
                    MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>());

                    var content = new StreamContent(ciphertext);
                    content.Headers.Add("Content-Type", "application/octet-stream");

                    var response = client.PostAsync(uri, content).Result;
                    if (response.StatusCode != HttpStatusCode.OK) {
                        failCount++;
                    } else if (!response.Content.ReadAsByteArrayAsync().Result.SequenceEqual(plaintext)) {
                        failCount++;
                    } else {
                        passCount++;
                    }
                } catch (DafnyException e) {
                    // TODO Log this error?
                    failCount++;
                }
                if (tolerateFailures != 0 && failCount >= tolerateFailures) {
                    break;
                }
            }
            return Tuple.Create(passCount, skipCount, failCount);
        }

        private static Tuple<int, int, int> IntegrationDecryptTestVectors(DecryptOptions options)
        {
            string vectorDir = options.vectorDir;
            int tolerateFailures = options.tolerateFailures;

            Dictionary<string, Key> keyMap = ParseKeys(Path.Combine(vectorDir, "keys.json")); //TODO should get this from manifest
            Dictionary<string, TestVector> vectorMap = ParseVectorsFromManifest(Path.Combine(vectorDir, "manifest.json"));

            int passCount = 0;
            int skipCount = 0;
            int failCount = 0;

            foreach(var vectorEntry in vectorMap) {
                TestVector vector = vectorEntry.Value;

                byte[] plaintext = System.IO.File.ReadAllBytes(TestURIToPath(vector.plaintext));
                byte[] ciphertext = System.IO.File.ReadAllBytes(TestURIToPath(vector.ciphertext));

                Keyring keyring;
                try {
                    keyring = CreateDecryptKeyring(vector, keyMap);
                } catch(NotYetSupportedException e) {
                    // TODO Should we log this error?
                    skipCount++;
                    continue;
                }

                CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
				MemoryStream ciphertextStream = new MemoryStream(ciphertext);

                try {
                    MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertextStream, cmm);
                    byte[] result = decodedStream.ToArray();
                    if (result.SequenceEqual(plaintext)) {
                        passCount++;
                    } else {
                        failCount++;
                    }
                } catch (DafnyException e) {
                    // TODO Log this error?
                    failCount++;
                }
                if (tolerateFailures != 0 && failCount >= tolerateFailures) {
                    break;
                }
            }
            return Tuple.Create(passCount, skipCount, failCount);
        }

        // TODO sane error handling
        public static int Main(string[] args) {
            int returnCode = 0;
            Parser.Default.ParseArguments<EncryptOptions, DecryptOptions>(args)
                .WithParsed<EncryptOptions>(encOpt => {
                        Tuple<int, int, int> result = IntegrationEncryptTestVectors(encOpt);
                        Console.WriteLine(String.Format("pass: {0}, skip: {1}, fail: {2}", result.Item1, result.Item2, result.Item3));
                        if (encOpt.tolerateFailures > 0 && result.Item3 >= encOpt.tolerateFailures) {
                            returnCode = 1;
                        }
                        })
                .WithParsed<DecryptOptions>(decOpt => {
                        Tuple<int, int, int> result = IntegrationDecryptTestVectors(decOpt);
                        Console.WriteLine(String.Format("pass: {0}, skip: {1}, fail: {2}", result.Item1, result.Item2, result.Item3));
                        if (decOpt.tolerateFailures > 0 && result.Item3 >= decOpt.tolerateFailures) {
                            returnCode = 1;
                        }
                        });
            return returnCode;
        }
    }
}
