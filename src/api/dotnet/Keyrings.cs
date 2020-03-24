using System;
using System.Collections.Generic;
using System.Linq;
using KeyringDefs;
using KMSKeyringDef;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using KMSUtils;
using icharseq = Dafny.ISequence<char>;

namespace AWSEncryptionSDK
{
    public class Keyrings
    {
        private static int KMS_GRANT_TOKEN_LIMIT = 10;

        public static Keyring MakeKMSKeyring(ClientSupplier clientSupplier,
                                             IEnumerable<string> keyIDs,
                                             string generator,
                                             IEnumerable<string> grantTokens)
        {
            var convertedTokens = grantTokens == null ? null : grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray();
            if (convertedTokens == null || convertedTokens.Length > KMS_GRANT_TOKEN_LIMIT) {
                throw new ArgumentException("KMS Keyring grant tokens required, must be between 0 and 10 elements");
            }
            if (keyIDs == null) {
                throw new ArgumentException("KMS Keyring key ids required, though can be empty");
            }
            if (clientSupplier == null) {
                throw new ArgumentException("KMS Keyring client supplier required");
            }
            KMSKeyring result = new KMSKeyring();
            result.__ctor(
                clientSupplier, 
                Dafny.Sequence<icharseq>.FromElements(keyIDs.Select(DafnyFFI.DafnyStringFromString).ToArray()),
                DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
                Dafny.Sequence<icharseq>.FromElements(convertedTokens));
            return result;
        }
        // TODO: Eventually the MultiKeyring will take a sequence instead of an array.
        public static MultiKeyring MakeMultiKeyring(Keyring generator, IList<Keyring> children)
        {
            foreach (Keyring child in children) {
                if (child == null) {
                    throw new ArgumentException("Multikeyring given null child keyring");
                }
            }
            MultiKeyring result = new MultiKeyring();
            result.__ctor(generator, Dafny.Sequence<Keyring>.FromArray(children.ToArray()));
            return result;
        }
        public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            if (nameSpace == null || nameSpace.Length == 0) {
                throw new ArgumentException("AES Keyring Key Namespace Required");
            }
            if (name == null || name.Length == 0) {
                throw new ArgumentException("AES Keyring Key Name Required");
            }
            RawAESKeyring result = new RawAESKeyring();
            EncryptionSuites.EncryptionSuite wrappingAlgDafny = DafnyFFI.AESWrappingAlgorithmToDafnyWrappingAlgorithm(wrappingAlgorithm);
            if (wrappingKey == null || wrappingKey.Length != wrappingAlgDafny.keyLen) {
                throw new ArgumentException("AES wrapping key has incorrect length given wrapping algorithm");
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
            if (nameSpace == null || nameSpace.Length == 0) {
                throw new ArgumentException("RSA Keyring Key Namespace Required");
            }
            if (name == null || name.Length == 0) {
                throw new ArgumentException("RSA Keyring Key Name Required");
            }
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
    }
}
