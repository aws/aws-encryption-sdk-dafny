using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Running;
using Org.BouncyCastle.Utilities.Encoders;
using RSA = RSAEncryption.RSA;

namespace Benchmarks
{
    public abstract class BaseEncryptDecryptBenchmark
    {
        [ParamsSource(nameof(ValuesForPlaintextLengthBytes))]
        public int PlaintextLengthBytes { get; set; }

        [ParamsSource(nameof(ValuesForFrameLengthBytes))]
        public int FrameLengthBytes { get; set; }

        private IAwsEncryptionSdk _encryptionSdk;
        private IKeyring _keyring;
        private MemoryStream _plaintext;
        private MemoryStream _ciphertext;
        private Dictionary<string, string> _encryptionContext;

        /**
         * Concrete benchmark classes should implement this method.
         */
        protected abstract IKeyring CreateKeyring();

        // Runs once for each combination of params
        [GlobalSetup]
        public void GlobalSetup()
        {
            _encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

            _keyring = CreateKeyring();

            _plaintext = new MemoryStream(PlaintextLengthBytes);
            _plaintext.SetLength(PlaintextLengthBytes);  // need to set this because buffer is 0-length by default
            RandomNumberGenerator.Create().GetBytes(_plaintext.GetBuffer());

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
                FrameLength = FrameLengthBytes
            });

        [Benchmark]
        public DecryptOutput Decrypt() =>
            _encryptionSdk.Decrypt(new DecryptInput
            {
                Keyring = _keyring,
                Ciphertext = _ciphertext
            });

        private static readonly int[] DefaultValuesForPlaintextLengthBytes =
        {
            1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000
        };

        public static IEnumerable<int> ValuesForPlaintextLengthBytes() =>
            ParseIntsFromEnvVar("BENCHMARK_PLAINTEXT_LENGTH_BYTES", DefaultValuesForPlaintextLengthBytes);

        private static readonly int[] DefaultValuesForFrameLengthBytes = { 1024, 4096, 65536 };

        public static IEnumerable<int> ValuesForFrameLengthBytes() =>
            ParseIntsFromEnvVar("BENCHMARK_FRAME_LENGTH_BYTES", DefaultValuesForFrameLengthBytes);

        /// <summary>
        /// Parses the named environment variable as comma-separated integers and returns them,
        /// or returns the given default values if the environment variable is empty.
        /// </summary>
        /// <exception cref="ApplicationException">if the environment variable is incorrectly formatted</exception>
        private static IEnumerable<int> ParseIntsFromEnvVar(string name, IEnumerable<int> defaults)
        {
            var envValue = Environment.GetEnvironmentVariable(name);
            if (string.IsNullOrWhiteSpace(envValue))
            {
                return defaults;
            }

            try
            {
                return envValue
                    .Split(',')
                    .Select(part => int.Parse(part.Trim()))
                    // Evaluate this query immediately so that we catch parse exceptions right away,
                    // and not when the caller tries to use the results
                    .ToList();
            }
            catch (FormatException exception)
            {
                throw new ApplicationException(
                    $"Environment variable {name} could not be parsed as comma-separated ints",
                    exception);
            }
        }
    }

    public class RawAesKeyringBenchmark : BaseEncryptDecryptBenchmark
    {
        private static readonly string AES_256_KEY_MATERIAL_B64 = "AAECAwQFBgcICRAREhMUFRYXGBkgISIjJCUmJygpMDE=";

        protected override IKeyring CreateKeyring()
        {
            var providers = AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
            return providers.CreateRawAesKeyring(new CreateRawAesKeyringInput
            {
                KeyNamespace = "aes_namespace",
                KeyName = "aes_name",
                WrappingAlg = AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16,
                WrappingKey = new MemoryStream(Base64.Decode(AES_256_KEY_MATERIAL_B64))
            });
        }
    }

    public class RawRsaKeyringBenchmark : BaseEncryptDecryptBenchmark
    {
        protected override IKeyring CreateKeyring()
        {
            RSA.GenerateKeyPairBytes(2048, out var publicKeyBytes, out var privateKeyBytes);

            var providers = AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
            return providers.CreateRawRsaKeyring(new CreateRawRsaKeyringInput
            {
                KeyNamespace = "rsa_namespace",
                KeyName = "rsa_name",
                PaddingScheme = PaddingScheme.OAEP_SHA512_MGF1,
                PublicKey = new MemoryStream(publicKeyBytes),
                PrivateKey = new MemoryStream(privateKeyBytes)
            });
        }
    }

    public class Program
    {
        public static void Main(string[] args) => BenchmarkSwitcher.FromAssembly(typeof(Program).Assembly).Run(args);
    }
}
