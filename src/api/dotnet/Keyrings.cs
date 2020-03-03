using System;
using System.Collections.Generic;
using System.Linq;
using KeyringDefs;
using KMSKeyringDef;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using KMSUtils;
using STL;
using charseq = Dafny.Sequence<char>;

namespace AWSEncryptionSDK
{
    public class Keyrings
    {
        public static Keyring MakeKMSKeyring(ClientSupplier clientSupplier,
                                             IEnumerable<string> keyIDs,
                                             string generator,
                                             IEnumerable<string> grantTokens)
        {
            KMSKeyring result = new KMSKeyring();
            // TODO: The Dafny constructor shouldn't be directly callable from C# code!
            // This isn't checking for nulls or any other requirements.
            result.__ctor(
                clientSupplier, 
                Dafny.Sequence<charseq>.FromElements(keyIDs.Select(DafnyFFI.DafnyStringFromString).ToArray()),
                DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
                Dafny.Sequence<charseq>.FromElements(grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray()));
            return result;
        }
        // TODO: Eventually the MultiKeyring will take a sequence instead of an array.
        public static MultiKeyring MakeMultiKeyring(Keyring generator, Keyring[] children)
        {
            // TODO: Check for null value etc.
            MultiKeyring result = new MultiKeyring();
            result.__ctor(generator, children);
            return result;
        }
        public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            // TODO: Check for null values
            RawAESKeyring result = new RawAESKeyring();
            EncryptionSuites.EncryptionSuite wrappingAlgDafny;
            switch(wrappingAlgorithm) {
                case DafnyFFI.AESWrappingAlgorithm.AES_GCM_128:
                    wrappingAlgDafny = EncryptionSuites.__default.AES__GCM__128;
                    break;
                case DafnyFFI.AESWrappingAlgorithm.AES_GCM_192:
                    wrappingAlgDafny = EncryptionSuites.__default.AES__GCM__192;
                    break;
                case DafnyFFI.AESWrappingAlgorithm.AES_GCM_256:
                    wrappingAlgDafny = EncryptionSuites.__default.AES__GCM__256;
                    break;
                default:
                    throw new ArgumentException("Unsupported AES Wrapping Algorithm");
            };
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
            // TODO: check for null values, ensure at least one key is non-null.
            RawRSAKeyring result = new RawRSAKeyring();
            RSAEncryption.PaddingMode paddingModeDafny;
            switch(paddingMode) {
                case DafnyFFI.RSAPaddingModes.PKCS1:
                    paddingModeDafny = RSAEncryption.PaddingMode.create_PKCS1();
                    break;
                case DafnyFFI.RSAPaddingModes.OAEP_SHA1:
                    paddingModeDafny = RSAEncryption.PaddingMode.create_OAEP__SHA1();
                    break;
                case DafnyFFI.RSAPaddingModes.OAEP_SHA256:
                    paddingModeDafny = RSAEncryption.PaddingMode.create_OAEP__SHA256();
                    break;
                case DafnyFFI.RSAPaddingModes.OAEP_SHA384:
                    paddingModeDafny = RSAEncryption.PaddingMode.create_OAEP__SHA384();
                    break;
                case DafnyFFI.RSAPaddingModes.OAEP_SHA512:
                    paddingModeDafny = RSAEncryption.PaddingMode.create_OAEP__SHA512();
                    break;
                default:
                    throw new ArgumentException("Unsupported RSA Padding Mode");
            };
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
