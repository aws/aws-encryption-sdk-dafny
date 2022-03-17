// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using AWSEncryptionSDK;
// using KeyringDefs;
using Org.BouncyCastle.Security;
using Xunit;

using Wrappers_Compile;

namespace AWSEncryptionSDKTests
{
    // public class ClientTests
    // {
    //     private static string SUCCESS = "SUCCESS";
    //     private static string KEYRING_NAMESPACE = "namespace";
    //     private static string KEYRING_NAME = "myKeyring";
    //     private static string CURRENT_REGION = "us-west-2";
    //
    //     // This is a testing only client supplier that returns whatever client it was given in all cases, regardless of region
    //     // For example, this is useful for testing cases where we always want a bad client
    //     private partial class TestingOnlyClientSupplier : AWSEncryptionSDK.AWSKMSClientSupplier {
    //         readonly private Amazon.KeyManagementService.IAmazonKeyManagementService client;
    //
    //         public TestingOnlyClientSupplier(Amazon.KeyManagementService.IAmazonKeyManagementService client) {
    //             this.client = client;
    //         }
    //
    //         public Amazon.KeyManagementService.IAmazonKeyManagementService GetClient(string region) {
    //             // Ignore the region, just return the same client in all cases
    //             return client;
    //         }
    //     }
    //
    //     // MakeKMSKeyring is a helper method that creates a KMS Keyring for unit testing with a specific client supplier
    //     private Keyring MakeKMSKeyringWithClientSupplier(AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier)
    //     {
    //         String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
    //         return AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //             clientSupplier, Enumerable.Empty<String>(), keyArn, Enumerable.Empty<String>());
    //     }
    //
    //     // MakeKMSKeyring is a helper method that creates a KMS Keyring for unit testing
    //     private Keyring MakeKMSKeyring()
    //     {
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier();
    //         return MakeKMSKeyringWithClientSupplier(clientSupplier);
    //     }
    //
    //     // MakeDefaultCMMWithKMSKeyring is a helper method that creates a default CMM using a KMS Keyring for unit testing
    //     // with a specific client supplier
    //     private CMMDefs.CMM MakeDefaultCMMWithKMSKeyringWithClientSupplier(AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier)
    //     {
    //         Keyring keyring = MakeKMSKeyringWithClientSupplier(clientSupplier);
    //         return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //     }
    //
    //     // MakeDefaultCMMWithKMSKeyring is a helper method that creates a default CMM using a KMS Keyring for unit testing
    //     private CMMDefs.CMM MakeDefaultCMMWithKMSKeyring()
    //     {
    //         Keyring keyring = MakeKMSKeyring();
    //         return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //     }
    //
    //     // MakeCachingCMMWithKMSKeyring is a helper method that creates a caching CMM around a default CMM that
    //     // uses a KMS Keyring for unit testing
    //     private CMMDefs.CMM MakeCachingCMMWithKMSKeyring()
    //     {
    //         Keyring keyring = MakeKMSKeyring();
    //         CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //         cmm = AWSEncryptionSDK.CMMs.MakeCachingCMM(cmm, 1,
    //                                                    CachingCMMDef.__default.DEFAULT__BYTE__USE__LIMIT__PER__CACHED__KEY,
    //                                                    CachingCMMDef.__default.DEFAULT__MESSAGE__USE__LIMIT__PER__CACHED__KEY);
    //         return cmm;
    //     }
    //
    //     // MakeRSAKeyring is a helper method that creates a RSA Keyring for unit testing
    //     private Keyring MakeRSAKeyring(Keyrings.RSAPaddingModes paddingMode, String nameSpace, String name)
    //     {
    //         byte[] publicKey;
    //         byte[] privateKey;
    //         RSAEncryption.RSA.GenerateKeyPairBytes(2048, out publicKey, out privateKey);
    //         // If namespace or name is null, just pass null into the constructor to properly test this behavior
    //         return AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
    //             nameSpace == null ? null : Encoding.UTF8.GetBytes(nameSpace),
    //             name == null ? null : Encoding.UTF8.GetBytes(name),
    //             paddingMode,
    //             publicKey,
    //             privateKey);
    //     }
    //
    //     // MakeDefaultCMMWithRSAKeyring is a helper method that creates a default CMM using a RSA Keyring for unit testing
    //     private CMMDefs.CMM MakeDefaultCMMWithRSAKeyring(Keyrings.RSAPaddingModes paddingMode)
    //     {
    //         Keyring keyring = MakeRSAKeyring(paddingMode, KEYRING_NAMESPACE, KEYRING_NAME);
    //         return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //     }
    //
    //     // MakeAESKeyring is a helper method that creates an AES Keyring for unit testing
    //     private static string AESWrappingAlgorithmToGeneratorUtilitiesAlgorithm(Keyrings.AESWrappingAlgorithm wrappingAlgorithm)
    //     {
    //         switch (wrappingAlgorithm) {
    //             case Keyrings.AESWrappingAlgorithm.AES_GCM_128:
    //                 return "AES128";
    //             case Keyrings.AESWrappingAlgorithm.AES_GCM_192:
    //                 return "AES192";
    //             case Keyrings.AESWrappingAlgorithm.AES_GCM_256:
    //                 return "AES256";
    //             default:
    //                 throw new ArgumentException("Unsupported AES Wrapping Algorithm");
    //         };
    //     }
    //
    //     private Keyring MakeAESKeyring(Keyrings.AESWrappingAlgorithm wrappingAlgorithm, String nameSpace, String name)
    //     {
    //         var algorithm = AESWrappingAlgorithmToGeneratorUtilitiesAlgorithm(wrappingAlgorithm);
    //         var keygen = GeneratorUtilities.GetKeyGenerator(algorithm);
    //         var wrappingKey = keygen.GenerateKey();
    //         // If namespace or name is null, just pass null into the constructor to properly test this behavior
    //         return AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
    //             nameSpace == null ? null : Encoding.UTF8.GetBytes(nameSpace),
    //             name == null ? null : Encoding.UTF8.GetBytes(name),
    //             wrappingKey,
    //             wrappingAlgorithm);
    //     }
    //
    //     // MakeDefaultCMMWithAESKeyring is a helper method that creates a default CMM using an AES Keyring for unit testing
    //     private CMMDefs.CMM MakeDefaultCMMWithAESKeyring(Keyrings.AESWrappingAlgorithm wrappingAlgorithm)
    //     {
    //         Keyring keyring = MakeAESKeyring(wrappingAlgorithm, KEYRING_NAMESPACE, KEYRING_NAME);
    //         return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //     }
    //
    //     // MakeDefaultCMMWithMultiKeyring is a helper method that creates a default CMM using a Multi-Keyring for unit testing
    //     private CMMDefs.CMM MakeDefaultCMMWithMultiKeyring()
    //     {
    //         Keyring generator = MakeKMSKeyring();
    //         Keyring[] children = new Keyring[] {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.PKCS1, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA1, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA256, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA384, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA512, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_128, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_192, KEYRING_NAMESPACE, KEYRING_NAME),
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_256, KEYRING_NAMESPACE, KEYRING_NAME),
    //         };
    //
    //         Keyring keyring = AWSEncryptionSDK.Keyrings.MakeMultiKeyring(generator, children);
    //         return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
    //     }
    //
    //     // EncryptDecrypt is a helper method that performs an encrypt and then a decrypt on a plaintext that is
    //     // formatted using a given id. withParams dictates whether Encrypt should use any additional encryption parameters
    //     private string EncryptDecrypt(CMMDefs.CMM cmm, int id, bool withParams)
    //     {
    //         var plaintext = String.Format("Hello from id {0}", id);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         if (withParams) {
    //             encryptRequest.algorithmSuiteID = 0x0346;
    //             encryptRequest.frameLength = 2048;
    //         }
    //         MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(
    //                 new AWSEncryptionSDK.Client.DecryptRequest{message = ciphertext, cmm = cmm}
    //                 );
    //         StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
    //         String decoded = reader.ReadToEnd();
    //         return (plaintext == decoded) ? SUCCESS : String.Format("Id: {0} failed, decoded: {1}", id, decoded);
    //     }
    //
    //     // EncryptDecryptThreaded is a helper method that calls EncryptDecrypt in a threaded manner using either 1 thread
    //     // if multithreading is disabled or 4 * the number of processors on the machine if it is enabled
    //     private void EncryptDecryptThreaded(CMMDefs.CMM cmm, bool isMultithreaded, bool withParams)
    //     {
    //         var concurrentBag = new ConcurrentBag<String>();
    //         var totalIds = isMultithreaded ? Environment.ProcessorCount * 4 : 1;
    //         // Sanity check that the total number of ids is valid
    //         Assert.True(isMultithreaded ? totalIds >= 4 : totalIds == 1);
    //
    //         Parallel.For(
    //             0, totalIds, new ParallelOptions { MaxDegreeOfParallelism = totalIds },
    //             id => { concurrentBag.Add(EncryptDecrypt(cmm, id, withParams)); }
    //         );
    //
    //         var totalDecoded = 0;
    //         foreach (string decoded in concurrentBag) {
    //             Assert.Equal(SUCCESS, decoded);
    //             totalDecoded += 1;
    //         }
    //         Assert.Equal(totalIds, totalDecoded);
    //     }
    //
    //     // DefaultClientTestData represents simple client test data that does not require additional parameters outside of
    //     // whether the test should be multithreaded and whether it should use additional params for encrypt
    //     public static TheoryData<bool, bool> DefaultClientTestData
    //     {
    //         get
    //         {
    //             var data = new TheoryData<bool, bool>();
    //             var multithreadedList = new bool[] { true, false };
    //             var withParamsList = new bool[] { true, false };
    //             foreach (bool isMultithreaded in multithreadedList) {
    //                 foreach (bool withParams in withParamsList) {
    //                     data.Add(isMultithreaded, withParams);
    //                 }
    //             }
    //             return data;
    //         }
    //     }
    //
    //     // AWSKMSClientTestData represents client test data that can be used for simple KMS client tests that check
    //     // combinations of AWSKMSClientSupplier and DefaultClientTestData
    //     public static TheoryData<AWSEncryptionSDK.AWSKMSClientSupplier, bool, bool> AWSKMSClientTestData
    //     {
    //         get
    //         {
    //             var data = new TheoryData<AWSEncryptionSDK.AWSKMSClientSupplier, bool, bool>();
    //             var clientSuppliers = new List<AWSEncryptionSDK.AWSKMSClientSupplier>() {
    //                 // BaseClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSBaseClientSupplier(),
    //                 // DefaultClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                 // ExcludeRegionsClientSupplier with BaseClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSBaseClientSupplier(),
    //                     new List<string>() { "us-east-1", "another-region" }),
    //                 // ExcludeRegionsClientSupplier with DefaultClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                     new List<string>() { "us-east-1", "another-region" }),
    //                 // ExcludeRegionsClientSupplier with no excluded regions
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                     new List<string>() {}),
    //                 // LimitRegionsClientSupplier with DefaultClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                     new List<string>() { CURRENT_REGION, "another-region" }),
    //                 // LimitRegionsClientSupplier with BaseClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSBaseClientSupplier(),
    //                     new List<string>() { CURRENT_REGION, "another-region" }),
    //                 // LimitRegionsClientSupplier with ExcludeRegionsClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                         AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                         new List<string>() { "excluded-region" }),
    //                     new List<string>() { CURRENT_REGION, "another-region" }),
    //                 // ExcludeRegionsClientSupplier with LimitRegionsClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                         AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                         new List<string>() { CURRENT_REGION, "another-region" }),
    //                     new List<string>() { "excluded-region" }),
    //                 // CachingClientSupplier with BaseClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSCachingClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier()),
    //                 // CachingClientSupplier with ExcludeRegionsClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSCachingClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                         AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSBaseClientSupplier(),
    //                         new List<string>() { "us-east-1", "another-region" })),
    //                 // CachingClientSupplier with LimitRegionsClientSupplier
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSCachingClientSupplier(
    //                     AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                         AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSBaseClientSupplier(),
    //                         new List<string>() { CURRENT_REGION, "another-region" }))
    //             };
    //             foreach (AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier in clientSuppliers) {
    //                 foreach (var item in DefaultClientTestData) {
    //                     // Since this is just being used for unit tests, and we know DefaultClientTestData is
    //                     // TheoryData<bool, bool>, cast object to bool directly
    //                     data.Add(clientSupplier, (bool) item[0], (bool) item[1]);
    //                 }
    //             }
    //             return data;
    //         }
    //     }
    //
    //     [Theory]
    //     [MemberData(nameof(AWSKMSClientTestData))]
    //     public void RoundTripHappyPath_KMS(AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier, bool isMultithreaded, bool withParams)
    //     {
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(clientSupplier);
    //         EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
    //     }
    //
    //     [Theory]
    //     [MemberData(nameof(DefaultClientTestData))]
    //     public void RoundTripHappyPath_KMS_CachingCMM(bool isMultithreaded, bool withParams)
    //     {
    //         CMMDefs.CMM cmm = MakeCachingCMMWithKMSKeyring();
    //         EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_KMS()
    //     {
    //         String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
    //         Assert.Throws<ArgumentNullException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 null, Enumerable.Empty<String>(), keyArn, Enumerable.Empty<String>());
    //         });
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_LimitRegions_BadRegion()
    //     {
    //         // LimitRegionsClientSupplier with a region we are not in
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { "some-other-region" });
    //
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(clientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} not in regions maintained by LimitRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_Caching_Composable_BadRegion()
    //     {
    //         // LimitRegionsClientSupplier with a region we are not in
    //         AWSEncryptionSDK.AWSKMSClientSupplier limitRegionsClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { "some-other-region" });
    //
    //         // CachingClientSupplier using the LimitRegionsClientSupplier
    //         AWSEncryptionSDK.AWSKMSClientSupplier cachingClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSCachingClientSupplier(
    //             limitRegionsClientSupplier);
    //
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(cachingClientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} not in regions maintained by LimitRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //
    //         // ExcludeRegionsClientSupplier with a region we are in
    //         AWSEncryptionSDK.AWSKMSClientSupplier excludeRegionsClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { CURRENT_REGION });
    //
    //         // Update the CachingClientSupplier and make a new call
    //         cachingClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSCachingClientSupplier(excludeRegionsClientSupplier);
    //         cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(cachingClientSupplier);
    //         encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} is in regions maintained by ExcludeRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_Caching_BadClient()
    //     {
    //         // Custom testing client supplier that always returns a bad client (a client that instantly has a timeout)
    //         var timeoutConfig = new Amazon.KeyManagementService.AmazonKeyManagementServiceConfig { Timeout = TimeSpan.FromMilliseconds(1) };
    //         var timeoutClient = new Amazon.KeyManagementService.AmazonKeyManagementServiceClient(timeoutConfig);
    //         AWSEncryptionSDK.AWSKMSClientSupplier badClientSupplier = new TestingOnlyClientSupplier(timeoutClient);
    //
    //         // CachingClientSupplier using the TestingOnlyClientSupplier
    //         // Manually construct this using Dafny structs to allow us to check the cache
    //         KMSUtils.CachingClientSupplier cachingDafnyClientSupplier = new KMSUtils.CachingClientSupplier();
    //         cachingDafnyClientSupplier.__ctor(new KMSUtils.AWSKMSClientSupplierAsDafny(badClientSupplier));
    //         AWSEncryptionSDK.AWSKMSClientSupplier cachingClientSupplier = new KMSUtils.DafnyAWSKMSClientSupplierAsNative(cachingDafnyClientSupplier);
    //
    //         // Manually call get client
    //         Amazon.KeyManagementService.IAmazonKeyManagementService obtainedClient = cachingClientSupplier.GetClient(CURRENT_REGION);
    //         Assert.Equal(timeoutClient, (Amazon.KeyManagementService.AmazonKeyManagementServiceClient)obtainedClient);
    //
    //         // Check the client is not cached
    //         var lookupRegion = DafnyFFI.NullableToOption<Dafny.ISequence<char>>(DafnyFFI.DafnyStringFromString(CURRENT_REGION));
    //         Option<Amazon.KeyManagementService.IAmazonKeyManagementService> potentialClient = cachingDafnyClientSupplier._clientCache.LookupClient(lookupRegion);
    //         Assert.NotNull(potentialClient);
    //         Assert.True(potentialClient.is_None);
    //         Assert.Equal(0, cachingDafnyClientSupplier._clientCache.ClientCache.Count);
    //
    //         // Try to call Encrypt (expect an exception since a timeout will occur)
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(cachingClientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //
    //         // Check that the client is still not cached
    //         potentialClient = cachingDafnyClientSupplier._clientCache.LookupClient(lookupRegion);
    //         Assert.NotNull(potentialClient);
    //         Assert.True(potentialClient.is_None);
    //         Assert.Equal(0, cachingDafnyClientSupplier._clientCache.ClientCache.Count);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_ExcludeRegions_BadRegion()
    //     {
    //         // ExcludeRegionsClientSupplier with a region we are in
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { CURRENT_REGION });
    //
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(clientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} is in regions maintained by ExcludeRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_LimitRegions_ExcludeRegions_BadRegion()
    //     {
    //         // LimitRegionsClientSupplier with ExcludeRegionsClientSupplier with a region we are in
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                 new List<string>() { CURRENT_REGION }),
    //             new List<string>() { CURRENT_REGION });
    //
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(clientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} is in regions maintained by ExcludeRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_ClientSupplier_ExcludeRegions_LimitRegions_BadRegion()
    //     {
    //         // ExcludeRegionsClientSupplier with LimitRegionsClientSupplier with a region we are not in
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //                 AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(),
    //                 new List<string>() { "another-region" }),
    //             new List<string>() { "excluded-region" });
    //
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyringWithClientSupplier(clientSupplier);
    //         MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("something"));
    //         var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
    //         DafnyException ex = Assert.Throws<DafnyException>(() => {
    //             AWSEncryptionSDK.Client.Encrypt(encryptRequest);
    //         });
    //         Assert.Equal(String.Format("Given region {0} not in regions maintained by LimitRegionsClientSupplier", CURRENT_REGION), ex.Message);
    //     }
    //
    //     [Fact]
    //     public void ClientSupplier_NoRegion_GetClient_Failures()
    //     {
    //         // ExcludeRegionsClientSupplier GetClient being called with no region
    //         AWSEncryptionSDK.AWSKMSClientSupplier excludeRegionsClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSExcludeRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { });
    //         AWSEncryptionSDK.AWSKMSClientSupplierException ex = Assert.Throws<AWSEncryptionSDK.AWSKMSClientSupplierException>(() => {
    //             excludeRegionsClientSupplier.GetClient(null);
    //         });
    //         Assert.Equal("ExcludeRegionsClientSupplier GetClient requires a region", ex.Message);
    //
    //         // LimitRegionsClientSupplier GetClient being called with no region
    //         AWSEncryptionSDK.AWSKMSClientSupplier limitRegionsClientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSLimitRegionsClientSupplier(
    //             AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier(), new List<string>() { });
    //         ex = Assert.Throws<AWSEncryptionSDK.AWSKMSClientSupplierException>(() => {
    //             limitRegionsClientSupplier.GetClient(null);
    //         });
    //         Assert.Equal("LimitRegionsClientSupplier GetClient requires a region", ex.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_KeyIds_KMS()
    //     {
    //         String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier();
    //         // Try when keyIds is null
    //         ArgumentNullException nullKeyIdsException = Assert.Throws<ArgumentNullException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 clientSupplier, null, keyArn, Enumerable.Empty<String>());
    //         });
    //         Assert.Equal("KMS Keyring keyIDs", nullKeyIdsException.ParamName);
    //
    //         // Try when keyIds contains null elements
    //         List<String> keyIds = new List<String>() { "keyId1", null, "keyId2" };
    //         ArgumentException nullKeyIdsElementException = Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 clientSupplier, keyIds, keyArn, Enumerable.Empty<String>());
    //         });
    //         Assert.Equal("KMS Keyring keyIDs given null element", nullKeyIdsElementException.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_GrantTokens_KMS()
    //     {
    //         String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
    //         AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier = AWSEncryptionSDK.AWSKMSClientSuppliers.NewKMSDefaultClientSupplier();
    //         // Try when grantTokens is null
    //         ArgumentNullException nullGrantTokensException = Assert.Throws<ArgumentNullException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 clientSupplier, Enumerable.Empty<String>(), keyArn, null);
    //         });
    //         Assert.Equal("KMS Keyring grantTokens", nullGrantTokensException.ParamName);
    //
    //         // Try when grantTokens contains null elements
    //         List<String> grantTokensWithNull = new List<String>() { "grantToken1", null, "grantToken2" };
    //         ArgumentException nullGrantTokensElementException = Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 clientSupplier, Enumerable.Empty<String>(), keyArn, grantTokensWithNull);
    //         });
    //         Assert.Equal("KMS Keyring grantTokens given null element", nullGrantTokensElementException.Message);
    //
    //         // Try when grantTokens has too many elements
    //         List<String> grantTokensTooLong = new List<String>();
    //         for (int i = 0; i < 11; i++) {
    //             grantTokensTooLong.Add(String.Format("grantToken{0}", i));
    //         }
    //         Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
    //                 clientSupplier, Enumerable.Empty<String>(), keyArn, grantTokensTooLong);
    //         });
    //     }
    //
    //     // RSAClientTestData represents client test data that can be used for simple RSA client tests that check all
    //     // combinations of RSAPaddingModes and DefaultClientTestData
    //     public static TheoryData<Keyrings.RSAPaddingModes, bool, bool> RSAClientTestData
    //     {
    //         get
    //         {
    //             var data = new TheoryData<Keyrings.RSAPaddingModes, bool, bool>();
    //             foreach (Keyrings.RSAPaddingModes paddingMode in Enum.GetValues(typeof(Keyrings.RSAPaddingModes))) {
    //                 foreach (var item in DefaultClientTestData) {
    //                     // Since this is just being used for unit tests, and we know DefaultClientTestData is
    //                     // TheoryData<bool, bool>, cast object to bool directly
    //                     data.Add(paddingMode, (bool) item[0], (bool) item[1]);
    //                 }
    //             }
    //             return data;
    //         }
    //     }
    //
    //     [Theory]
    //     [MemberData(nameof(RSAClientTestData))]
    //     public void RoundTripHappyPath_RSA(Keyrings.RSAPaddingModes paddingMode, bool isMultithreaded, bool withParams)
    //     {
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
    //         EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_NoKeys_RSA()
    //     {
    //         Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
    //             Encoding.UTF8.GetBytes(KEYRING_NAMESPACE),
    //             Encoding.UTF8.GetBytes(KEYRING_NAME),
    //             Keyrings.RSAPaddingModes.OAEP_SHA512,
    //             null,
    //             null);
    //         });
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_Namespace_RSA()
    //     {
    //         // Try when namespace is null
    //         ArgumentNullException nullNamespaceException = Assert.Throws<ArgumentNullException>(() => {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA512, null, KEYRING_NAME);
    //         });
    //         Assert.Equal("RSA Keyring nameSpace", nullNamespaceException.ParamName);
    //
    //         // Try when namespace is empty
    //         ArgumentException emptyNamespaceException = Assert.Throws<ArgumentException>(() => {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA512, "", KEYRING_NAME);
    //         });
    //         Assert.Equal("RSA Keyring nameSpace is empty", emptyNamespaceException.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_Name_RSA()
    //     {
    //         // Try when name is null
    //         ArgumentNullException nullNameException = Assert.Throws<ArgumentNullException>(() => {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA512, KEYRING_NAMESPACE, null);
    //         });
    //         Assert.Equal("RSA Keyring name", nullNameException.ParamName);
    //
    //         // Try when name is empty
    //         ArgumentException emptyNameException = Assert.Throws<ArgumentException>(() => {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA512, KEYRING_NAMESPACE, "");
    //         });
    //         Assert.Equal("RSA Keyring name is empty", emptyNameException.Message);
    //     }
    //
    //     // AESClientTestData represents client test data that can be used for simple AES client tests that check all
    //     // combinations of AESWrappingAlgorithm and DefaultClientTestData
    //     public static TheoryData<Keyrings.AESWrappingAlgorithm, bool, bool> AESClientTestData
    //     {
    //         get
    //         {
    //             var data = new TheoryData<Keyrings.AESWrappingAlgorithm, bool, bool>();
    //             foreach (Keyrings.AESWrappingAlgorithm wrappingAlgorithm in Enum.GetValues(typeof(Keyrings.AESWrappingAlgorithm))) {
    //                 foreach (var item in DefaultClientTestData) {
    //                     // Since this is just being used for unit tests, and we know DefaultClientTestData is
    //                     // TheoryData<bool, bool>, cast object to bool directly
    //                     data.Add(wrappingAlgorithm, (bool) item[0], (bool) item[1]);
    //                 }
    //             }
    //             return data;
    //         }
    //     }
    //
    //     [Theory]
    //     [MemberData(nameof(AESClientTestData))]
    //     public void RoundTripHappyPath_AES(Keyrings.AESWrappingAlgorithm wrappingAlgorithm, bool isMultithreaded, bool withParams)
    //     {
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
    //         EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_MismatchedWrappingAlgorithm_AES()
    //     {
    //         // Make the keygen use a different wrapping algorithm than the one that is passed into the AES Keyring
    //         var keygen = GeneratorUtilities.GetKeyGenerator("AES128");
    //         var wrappingKey = keygen.GenerateKey();
    //         Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
    //                 Encoding.UTF8.GetBytes(KEYRING_NAMESPACE),
    //                 Encoding.UTF8.GetBytes(KEYRING_NAME),
    //                 wrappingKey,
    //                 Keyrings.AESWrappingAlgorithm.AES_GCM_192);
    //         });
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_Namespace_AES()
    //     {
    //         // Try when namespace is null
    //         ArgumentNullException nullNamespaceException = Assert.Throws<ArgumentNullException>(() => {
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_128, null, KEYRING_NAME);
    //         });
    //         Assert.Equal("AES Keyring nameSpace", nullNamespaceException.ParamName);
    //
    //         // Try when namespace is empty
    //         ArgumentException emptyNamespaceException = Assert.Throws<ArgumentException>(() => {
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_128, "", KEYRING_NAME);
    //         });
    //         Assert.Equal("AES Keyring nameSpace is empty", emptyNamespaceException.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_Name_AES()
    //     {
    //         // Try when name is null
    //         ArgumentNullException nullNameException = Assert.Throws<ArgumentNullException>(() => {
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_128, KEYRING_NAMESPACE, null);
    //         });
    //         Assert.Equal("AES Keyring name", nullNameException.ParamName);
    //
    //         // Try when name is empty
    //         ArgumentException emptyNameException = Assert.Throws<ArgumentException>(() => {
    //             MakeAESKeyring(Keyrings.AESWrappingAlgorithm.AES_GCM_128, KEYRING_NAMESPACE, "");
    //         });
    //         Assert.Equal("AES Keyring name is empty", emptyNameException.Message);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_WrappingKey_AES()
    //     {
    //         // Try when the wrapping key is null
    //         Assert.Throws<ArgumentNullException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
    //                 Encoding.UTF8.GetBytes(KEYRING_NAMESPACE),
    //                 Encoding.UTF8.GetBytes(KEYRING_NAME),
    //                 null,
    //                 Keyrings.AESWrappingAlgorithm.AES_GCM_128);
    //         });
    //
    //         // Try when the wrapping key is empty
    //         Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
    //                 Encoding.UTF8.GetBytes(KEYRING_NAMESPACE),
    //                 Encoding.UTF8.GetBytes(KEYRING_NAME),
    //                 Encoding.UTF8.GetBytes(""),
    //                 Keyrings.AESWrappingAlgorithm.AES_GCM_128);
    //         });
    //     }
    //
    //     [Theory]
    //     [MemberData(nameof(DefaultClientTestData))]
    //     public void RoundTripHappyPath_MultiKeyring(bool isMultithreaded, bool withParams)
    //     {
    //         CMMDefs.CMM cmm = MakeDefaultCMMWithMultiKeyring();
    //         EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
    //     }
    //
    //     [Fact]
    //     public void BadConstructor_Children_MultiKeyring()
    //     {
    //         Keyring generator = MakeKMSKeyring();
    //         // Try when children is null
    //         ArgumentNullException nullChildrenException = Assert.Throws<ArgumentNullException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeMultiKeyring(generator, null);
    //         });
    //         Assert.Equal("Multikeyring children", nullChildrenException.ParamName);
    //
    //         // Try when children contains null elements
    //         Keyring[] children = new Keyring[] {
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.PKCS1, KEYRING_NAMESPACE, KEYRING_NAME),
    //             null,
    //             MakeRSAKeyring(Keyrings.RSAPaddingModes.OAEP_SHA256, KEYRING_NAMESPACE, KEYRING_NAME)
    //         };
    //         ArgumentException nullChildrenElementException = Assert.Throws<ArgumentException>(() => {
    //             AWSEncryptionSDK.Keyrings.MakeMultiKeyring(generator, children);
    //         });
    //         Assert.Equal("Multikeyring children given null element", nullChildrenElementException.Message);
    //     }
    //
    //     [Fact]
    //     public void EncryptNullPlaintext()
    //     {
    //         var cmm = MakeDefaultCMMWithKMSKeyring();
    //         var nullRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = null, cmm = cmm};
    //
    //         Assert.Throws<ArgumentNullException>(() =>
    //         AWSEncryptionSDK.Client.Encrypt(nullRequest));
    //     }
    //
    //     [Fact]
    //     public void EncryptNullCMMKeyring()
    //     {
    //         var nullRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream()};
    //
    //         var ex = Assert.Throws<DafnyException>(() =>
    //         AWSEncryptionSDK.Client.Encrypt(nullRequest));
    //
    //         Assert.Equal("EncryptRequest.cmm and EncryptRequest.keyring cannot both be null.", ex.Message);
    //     }
    //
    //     [Fact]
    //     public void EncryptNullEncryptionContext()
    //     {
    //         var nullCtx = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream(), keyring = MakeKMSKeyring(), encryptionContext = null};
    //
    //         Assert.Throws<ArgumentNullException>(() =>
    //         AWSEncryptionSDK.Client.Encrypt(nullCtx));
    //     }
    //
    //     [Fact]
    //     public void DecryptNullMessage()
    //     {
    //         var badRequest = new AWSEncryptionSDK.Client.DecryptRequest{message = null};
    //
    //         Assert.Throws<ArgumentNullException>(() =>
    //         AWSEncryptionSDK.Client.Decrypt(badRequest));
    //     }
    //
    //     [Fact]
    //     public void DecryptNullCMMKeyring()
    //     {
    //         var nullRequest = new AWSEncryptionSDK.Client.DecryptRequest{message = new MemoryStream()};
    //
    //         var ex = Assert.Throws<DafnyException>(() =>
    //         AWSEncryptionSDK.Client.Decrypt(nullRequest));
    //
    //         Assert.Equal("DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.", ex.Message);
    //     }
    //
    //     // TODO-RS: Test for nulls and other Dafny requirement violations
    // }
}
