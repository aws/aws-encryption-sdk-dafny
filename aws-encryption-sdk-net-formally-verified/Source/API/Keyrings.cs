// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.Linq;
// using KeyringDefs;
// using KMSKeyringDef;
// using MultiKeyringDef;
// using RawAESKeyring;
// using RawRSAKeyringDef;
using icharseq = Dafny.ISequence<char>;

namespace AWSEncryptionSDK
{
    // public class Keyrings
    // {
    //     public static Keyring MakeKMSKeyring(AWSKMSClientSupplier clientSupplier,
    //                                          IEnumerable<string> keyIDs,
    //                                          string generator,
    //                                          IEnumerable<string> grantTokens)
    //     {
    //         CheckEnumerableNotNullOrContainingNullElements(grantTokens, "KMS Keyring grantTokens");
    //         var convertedTokens = grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray();
    //         if (convertedTokens.Length > KMSUtils.__default.MAX__GRANT__TOKENS) {
    //             throw new ArgumentException("KMS Keyring grantTokens given more than 10 grant tokens");
    //         }
    //         CheckEnumerableNotNullOrContainingNullElements(keyIDs, "KMS Keyring keyIDs");
    //         if (clientSupplier == null) {
    //             throw new ArgumentNullException("clientSupplier");
    //         }
    //         KMSKeyring result = new KMSKeyring();
    //         result.__ctor(
    //             new KMSUtils.AWSKMSClientSupplierAsDafny(clientSupplier),
    //             Dafny.Sequence<icharseq>.FromElements(),
    //             DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
    //             Dafny.Sequence<icharseq>.FromElements(convertedTokens));
    //         return result;
    //     }
    //     // TODO: Eventually the MultiKeyring will take a sequence instead of an array.
    //     public static MultiKeyring MakeMultiKeyring(Keyring generator, IList<Keyring> children)
    //     {
    //         CheckEnumerableNotNullOrContainingNullElements(children, "Multikeyring children");
    //         MultiKeyring result = new MultiKeyring();
    //         result.__ctor(generator, Dafny.Sequence<Keyring>.FromArray(children.ToArray()));
    //         return result;
    //     }
    //
    //     public enum AESWrappingAlgorithm {
    //         AES_GCM_128, AES_GCM_192, AES_GCM_256
    //     }
    //
    //     private static EncryptionSuites.EncryptionSuite AESWrappingAlgorithmToDafnyWrappingAlgorithm(AESWrappingAlgorithm wrappingAlgorithm)
    //     {
    //         switch (wrappingAlgorithm) {
    //             case AESWrappingAlgorithm.AES_GCM_128:
    //                 return EncryptionSuites.__default.AES__GCM__128;
    //             case AESWrappingAlgorithm.AES_GCM_192:
    //                 return EncryptionSuites.__default.AES__GCM__192;
    //             case AESWrappingAlgorithm.AES_GCM_256:
    //                 return EncryptionSuites.__default.AES__GCM__256;
    //             default:
    //                 throw new ArgumentException("Unsupported AES Wrapping Algorithm");
    //         };
    //     }
    //
    //     public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, AESWrappingAlgorithm wrappingAlgorithm)
    //     {
    //         CheckArrayNotNullOrEmpty(nameSpace, "AES Keyring nameSpace");
    //         CheckArrayNotNullOrEmpty(name, "AES Keyring name");
    //         RawAESKeyring result = new RawAESKeyring();
    //         EncryptionSuites.EncryptionSuite wrappingAlgDafny = AESWrappingAlgorithmToDafnyWrappingAlgorithm(wrappingAlgorithm);
    //         if (wrappingKey == null) {
    //             throw new ArgumentNullException("AES Keyring wrappingKey");
    //         }
    //         if (wrappingKey.Length != wrappingAlgDafny.keyLen) {
    //             throw new ArgumentException("AES Keyring wrappingKey has incorrect length given wrapping algorithm");
    //         }
    //         result.__ctor(
    //                 DafnyFFI.SequenceFromByteArray(nameSpace),
    //                 DafnyFFI.SequenceFromByteArray(name),
    //                 DafnyFFI.SequenceFromByteArray(wrappingKey),
    //                 wrappingAlgDafny
    //                 );
    //         return result;
    //     }
    //
    //     public enum RSAPaddingModes {
    //         PKCS1, OAEP_SHA1, OAEP_SHA256, OAEP_SHA384, OAEP_SHA512
    //     }
    //
    //     private static RSAEncryption.PaddingMode RSAPaddingModesToDafnyPaddingMode(RSAPaddingModes paddingModes)
    //     {
    //         switch (paddingModes) {
    //             case RSAPaddingModes.PKCS1:
    //                 return RSAEncryption.PaddingMode.create_PKCS1();
    //             case RSAPaddingModes.OAEP_SHA1:
    //                 return RSAEncryption.PaddingMode.create_OAEP__SHA1();
    //             case RSAPaddingModes.OAEP_SHA256:
    //                 return RSAEncryption.PaddingMode.create_OAEP__SHA256();
    //             case RSAPaddingModes.OAEP_SHA384:
    //                 return RSAEncryption.PaddingMode.create_OAEP__SHA384();
    //             case RSAPaddingModes.OAEP_SHA512:
    //                 return RSAEncryption.PaddingMode.create_OAEP__SHA512();
    //             default:
    //                 throw new ArgumentException("Unsupported RSA Padding Mode");
    //         };
    //     }
    //
    //     public static RawRSAKeyring MakeRawRSAKeyring(byte[] nameSpace, byte[] name, RSAPaddingModes paddingMode, byte[] publicKey, byte[] privateKey)
    //     {
    //         CheckArrayNotNullOrEmpty(nameSpace, "RSA Keyring nameSpace");
    //         CheckArrayNotNullOrEmpty(name, "RSA Keyring name");
    //         RawRSAKeyring result = new RawRSAKeyring();
    //         RSAEncryption.PaddingMode paddingModeDafny = RSAPaddingModesToDafnyPaddingMode(paddingMode);
    //         RSAEncryption.PublicKey publicKeyWrapper = null;
    //         RSAEncryption.PrivateKey privateKeyWrapper = null;
    //         if (publicKey != null) {
    //             publicKeyWrapper = new RSAEncryption.PublicKey();
    //             publicKeyWrapper.__ctor(DafnyFFI.SequenceFromByteArray(publicKey));
    //         }
    //         if (privateKey != null) {
    //             privateKeyWrapper = new RSAEncryption.PrivateKey();
    //             privateKeyWrapper.__ctor(DafnyFFI.SequenceFromByteArray(privateKey));
    //         }
    //         if (publicKeyWrapper == null && privateKeyWrapper == null) {
    //             throw new ArgumentException("RSA Keyring requires at least one of: public key or private key");
    //         }
    //         result.__ctor(
    //                 DafnyFFI.SequenceFromByteArray(nameSpace),
    //                 DafnyFFI.SequenceFromByteArray(name),
    //                 paddingModeDafny,
    //                 DafnyFFI.NullableToOption(publicKeyWrapper),
    //                 DafnyFFI.NullableToOption(privateKeyWrapper)
    //                 );
    //         return result;
    //     }
    //
    //     private static void CheckArrayNotNullOrEmpty<T>(T[] array, string name)
    //     {
    //         if (array == null) {
    //             throw new ArgumentNullException(name);
    //         }
    //         if (array.Length == 0) {
    //             throw new ArgumentException(String.Format("{0} is empty", name));
    //         }
    //     }
    //
    //     private static void CheckEnumerableNotNullOrContainingNullElements<T>(IEnumerable<T> enumerable, string name) where T : class
    //     {
    //         if (enumerable == null) {
    //             throw new ArgumentNullException(name);
    //         }
    //         if (enumerable.Contains(null)) {
    //             throw new ArgumentException(String.Format("{0} given null element", name));
    //         }
    //     }
    // }
}
