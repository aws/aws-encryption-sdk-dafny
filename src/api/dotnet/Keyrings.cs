using System;
using System.Collections.Generic;
using System.Linq;
using KeyringDefs;
using KMSKeyringDef;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using icharseq = Dafny.ISequence<char>;

namespace AWSEncryptionSDK
{
    public class Keyrings
    {
        public static Keyring MakeKMSKeyring(AWSKMSClientSupplier clientSupplier,
                                             IEnumerable<string> keyIDs,
                                             string generator,
                                             IEnumerable<string> grantTokens)
        {
            CheckEnumerableNotNullOrContainingNullElements(grantTokens, "KMS Keyring grantTokens");
            var convertedTokens = grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray();
            if (convertedTokens.Length > KMSUtils.__default.MAX__GRANT__TOKENS) {
                throw new ArgumentException("KMS Keyring grantTokens given more than 10 grant tokens");
            }
            CheckEnumerableNotNullOrContainingNullElements(keyIDs, "KMS Keyring keyIDs");
            if (clientSupplier == null) {
                throw new ArgumentNullException("clientSupplier");
            }
            KMSKeyring result = new KMSKeyring();
            result.__ctor(
                new KMSUtils.AWSKMSClientSupplierAsDafny(clientSupplier),
                Dafny.Sequence<icharseq>.FromElements(),
                DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
                Dafny.Sequence<icharseq>.FromElements(convertedTokens));
            return result;
        }
        // TODO: Eventually the MultiKeyring will take a sequence instead of an array.
        public static MultiKeyring MakeMultiKeyring(Keyring generator, IList<Keyring> children)
        {
            CheckEnumerableNotNullOrContainingNullElements(children, "Multikeyring children");
            MultiKeyring result = new MultiKeyring();
            result.__ctor(generator, Dafny.Sequence<Keyring>.FromArray(children.ToArray()));
            return result;
        }
        public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            CheckArrayNotNullOrEmpty(nameSpace, "AES Keyring nameSpace");
            CheckArrayNotNullOrEmpty(name, "AES Keyring name");
            RawAESKeyring result = new RawAESKeyring();
            EncryptionSuites.EncryptionSuite wrappingAlgDafny = DafnyFFI.AESWrappingAlgorithmToDafnyWrappingAlgorithm(wrappingAlgorithm);
            if (wrappingKey == null) {
                throw new ArgumentNullException("AES Keyring wrappingKey");
            }
            if (wrappingKey.Length != wrappingAlgDafny.keyLen) {
                throw new ArgumentException("AES Keyring wrappingKey has incorrect length given wrapping algorithm");
            }
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    DafnyFFI.SequenceFromByteArray(wrappingKey),
                    wrappingAlgDafny
                    );
            return result;
        }
        public static RawRSAKeyring MakeRawRSAKeyring(byte[] nameSpace, byte[] name, DafnyFFI.RSAPaddingModes paddingMode, byte[] publicKey, byte[] privateKey)
        {
            CheckArrayNotNullOrEmpty(nameSpace, "RSA Keyring nameSpace");
            CheckArrayNotNullOrEmpty(name, "RSA Keyring name");
            RawRSAKeyring result = new RawRSAKeyring();
            RSAEncryption.PaddingMode paddingModeDafny = DafnyFFI.RSAPaddingModesToDafnyPaddingMode(paddingMode);
            RSAEncryption.PublicKey publicKeyWrapper = null;
            RSAEncryption.PrivateKey privateKeyWrapper = null;
            if (publicKey != null) {
                publicKeyWrapper = new RSAEncryption.PublicKey();
                publicKeyWrapper.__ctor(DafnyFFI.SequenceFromByteArray(publicKey));
            }
            if (privateKey != null) {
                privateKeyWrapper = new RSAEncryption.PrivateKey();
                privateKeyWrapper.__ctor(DafnyFFI.SequenceFromByteArray(privateKey));
            }
            if (publicKeyWrapper == null && privateKeyWrapper == null) {
                throw new ArgumentException("RSA Keyring requires at least one of: public key or private key");
            }
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    paddingModeDafny,
                    DafnyFFI.NullableToOption(publicKeyWrapper),
                    DafnyFFI.NullableToOption(privateKeyWrapper)
                    );
            return result;
        }

        private static void CheckArrayNotNullOrEmpty<T>(T[] array, string name)
        {
            if (array == null) {
                throw new ArgumentNullException(name);
            }
            if (array.Length == 0) {
                throw new ArgumentException(String.Format("{0} is empty", name));
            }
        }

        private static void CheckEnumerableNotNullOrContainingNullElements<T>(IEnumerable<T> enumerable, string name) where T : class
        {
            if (enumerable == null) {
                throw new ArgumentNullException(name);
            }
            if (enumerable.Contains(null)) {
                throw new ArgumentException(String.Format("{0} given null element", name));
            }
        }
    }
}
