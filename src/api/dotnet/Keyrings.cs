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
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace AWSEncryptionSDK
{
    public class Keyrings
    {
        public static Keyring AsInternalKeyring(ExternalKeyring keyring) {
            // TODO-RS: This feels correct because we want to catch incoming nulls
            // from external client code, but I'm not 100% confident because
            // we also want to accept nullable Keyring? values too (e.g. a MultiKeyring's generator)
            if (keyring == null) {
                throw new NullReferenceException();
            }
            if (keyring is AsExternalKeyring k2) {
                return k2.wrapped;
            } else {
                AsKeyring result = new AsKeyring();
                result.__ctor(keyring);
                return result;
            }
        }
        
        public static ExternalKeyring AsExternalKeyring(Keyring keyring) {
            // TODO-RS: This is intended to support mapping a "Keyring?" value,
            // but I'm not confident that always makes sense.
            if (keyring == null) {
                return null;
            }
            if (keyring is AsKeyring k2) {
                return k2.wrapped;
            } else {
                AsExternalKeyring result = new AsExternalKeyring();
                result.__ctor(keyring);
                return result;
            }
        }
        
        public static ExternalKeyring MakeKMSKeyring(ClientSupplier clientSupplier,
                                             IEnumerable<string> keyIDs,
                                             string generator,
                                             IEnumerable<string> grantTokens)
        {
            KMSKeyring result = new KMSKeyring();
            // TODO: The Dafny constructor shouldn't be directly callable from C# code!
            // This isn't checking for nulls or any other requirements.
            result.__ctor(
                clientSupplier, 
                Dafny.Sequence<icharseq>.FromElements(keyIDs.Select(DafnyFFI.DafnyStringFromString).ToArray()),
                DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
                Dafny.Sequence<icharseq>.FromElements(grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray()));
            return AsExternalKeyring(result);
        }
        public static ExternalKeyring MakeMultiKeyring(ExternalKeyring generator, IList<ExternalKeyring> children)
        {
            // TODO: Check for null value etc.
            MultiKeyring result = new MultiKeyring();
            result.__ctor(AsInternalKeyring(generator), Dafny.Sequence<Keyring>.FromElements(children.Select(AsInternalKeyring).ToArray()));
            return AsExternalKeyring(result);
        }

        public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            // TODO: Check for null values
            RawAESKeyring result = new RawAESKeyring();
            EncryptionSuites.EncryptionSuite wrappingAlgDafny = wrappingAlgorithm switch {
                DafnyFFI.AESWrappingAlgorithm.AES_GCM_128 => EncryptionSuites.__default.AES__GCM__128,
                DafnyFFI.AESWrappingAlgorithm.AES_GCM_192 => EncryptionSuites.__default.AES__GCM__192,
                DafnyFFI.AESWrappingAlgorithm.AES_GCM_256 => EncryptionSuites.__default.AES__GCM__256,
                _ => throw new ArgumentException("Unsupported AES Wrapping Algorithm")
            };
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    DafnyFFI.SequenceFromByteArray(wrappingKey),
                    wrappingAlgDafny
                    );
            return result;
        }

        public static ExternalKeyring MakeRawRSAKeyring(byte[] nameSpace, byte[] name, DafnyFFI.RSAPaddingModes paddingMode, byte[] publicKey, byte[] privateKey)
        {
            // TODO: check for null values, ensure at least one key is non-null.
            RawRSAKeyring result = new RawRSAKeyring();
            RSAEncryption.PaddingMode paddingModeDafny = paddingMode switch {
                DafnyFFI.RSAPaddingModes.PKCS1 => RSAEncryption.PaddingMode.create_PKCS1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA1 => RSAEncryption.PaddingMode.create_OAEP__SHA1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA256 => RSAEncryption.PaddingMode.create_OAEP__SHA256(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA384 => RSAEncryption.PaddingMode.create_OAEP__SHA384(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA512 => RSAEncryption.PaddingMode.create_OAEP__SHA512(),
                _ => throw new ArgumentException("Unsupported RSA Padding Mode")
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
            return AsExternalKeyring(result);
        }
    }
}
