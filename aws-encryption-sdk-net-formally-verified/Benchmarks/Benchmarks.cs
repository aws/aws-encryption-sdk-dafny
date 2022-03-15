using System.Collections.Generic;
using System.IO;
using System.Security.Cryptography;
using Aws.Crypto;
using Aws.Esdk;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Running;
using Org.BouncyCastle.Utilities.Encoders;

namespace Benchmarks
{
    public class EncryptDecryptBenchmark
    {
        [Params(0, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000)]
        public int PlaintextLengthBytes { get; set; }

        private static readonly string AES_256_KEY_MATERIAL_B64 = "AAECAwQFBgcICRAREhMUFRYXGBkgISIjJCUmJygpMDE=";

        private IAwsEncryptionSdk _encryptionSdk;
        private IKeyring _keyring;
        private MemoryStream _plaintext;
        private MemoryStream _ciphertext;
        private Dictionary<string, string> _encryptionContext;

        // Runs once for each combination of params
        [GlobalSetup]
        public void GlobalSetup()
        {
            _encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

            var providers = AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
            _keyring = providers.CreateRawAesKeyring(new CreateRawAesKeyringInput
            {
                KeyNamespace = "aes_namespace",
                KeyName = "aes_name",
                WrappingAlg = AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16,
                WrappingKey = new MemoryStream(Base64.Decode(AES_256_KEY_MATERIAL_B64))
            });

            _plaintext = new MemoryStream(PlaintextLengthBytes);
            _plaintext.SetLength(PlaintextLengthBytes);  // need to set this because buffer is 0-length by default
            RandomNumberGenerator.Fill(_plaintext.GetBuffer());

            _encryptionContext = new Dictionary<string, string>
            {
                { "key1", "value1" },
                { "key2", "value2" },
                { "key3", "value3" }
            };

            _ciphertext = Encrypt().Ciphertext;
        }

        [Benchmark]
        public EncryptOutput Encrypt() =>
            _encryptionSdk.Encrypt(new EncryptInput
            {
                Keyring = _keyring,
                Plaintext = _plaintext,
                EncryptionContext = _encryptionContext,
                AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
            });

        [Benchmark]
        public DecryptOutput Decrypt() =>
            _encryptionSdk.Decrypt(new DecryptInput
            {
                Keyring = _keyring,
                Ciphertext = _ciphertext
            });
    }

    public class Program
    {
        public static void Main(string[] args) => BenchmarkSwitcher.FromAssembly(typeof(Program).Assembly).Run(args);
    }
}
