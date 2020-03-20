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
        public static ExternalKeyring MakeKMSKeyring(ClientSupplier clientSupplier,
                                                     IEnumerable<string> keyIDs,
                                                     string generator,
                                                     IEnumerable<string> grantTokens)
        {
            // TODO-RS: Check for null strings
            var internalKeyring = DafnyFFI.ExtractResult(KMSKeyringDef.__default.MakeKMSKeyring(
                clientSupplier, 
                Dafny.Sequence<icharseq>.FromElements(keyIDs.Select(DafnyFFI.DafnyStringFromString).ToArray()),
                DafnyFFI.DafnyStringFromString(generator),
                Dafny.Sequence<icharseq>.FromElements(grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray())));
            return KeyringDefs.__default.ToExternalKeyring(internalKeyring);
        }
       
        public static ExternalKeyring MakeMultiKeyring(ExternalKeyring generator, IList<ExternalKeyring> children)
        {
            var childrenSequence = Dafny.Sequence<ExternalKeyring>.FromArray(children.ToArray());
            var internalKeyring = DafnyFFI.ExtractResult(MultiKeyringDef.__default.MakeMultiKeyring(generator, childrenSequence));
            return KeyringDefs.__default.ToExternalKeyring(internalKeyring);
        }
        public static ExternalKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            // TODO: Check for null values
            RawAESKeyring result = new RawAESKeyring();
            EncryptionSuites.EncryptionSuite wrappingAlgDafny;
            switch (wrappingAlgorithm) {
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
            // TODO-RS: Move into Dafny
            return KeyringDefs.__default.ToExternalKeyring(result);
        }
        public static ExternalKeyring MakeRawRSAKeyring(byte[] nameSpace, byte[] name, DafnyFFI.RSAPaddingModes paddingMode, byte[] publicKey, byte[] privateKey)
        {
            // TODO: check for null values, ensure at least one key is non-null.
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
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    paddingModeDafny,
                    DafnyFFI.NullableToOption(publicKeyWrapper),
                    DafnyFFI.NullableToOption(privateKeyWrapper)
                    );
            // TODO-RS: Move this into Dafny
            return KeyringDefs.__default.ToExternalKeyring(result);
        }
    }
}
