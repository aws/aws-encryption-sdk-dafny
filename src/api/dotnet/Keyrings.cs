using System.Collections.Generic;
using System.Linq;
using KeyringDefs;
using KMSKeyringDef;
using KMSUtils;
using MultiKeyringDef;
using RawAESKeyringDef;
using RawRSAKeyringDef;
using STL;
using byteseq = Dafny.Sequence<byte>;
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

        // TODO: Eventually the MultiKeyring will take a seqence instead of an array.
        public static MultiKeyring MakeMultiKeyring(Keyring generator, Keyring[] children)
        {
            // TODO: Check for null value etc.
            MultiKeyring result = new MultiKeyring();
            result.__ctor(generator, children);
            return result;
        }
        public static RawAESKeyring MakeRawAESKeyring(byte[] nameSpace, byte[] name, byte[] wrappingKey, EncryptionSuites.EncryptionSuite wrappingAlg)
        {
            // TODO: Check for null values, valid wrapping value, etc.
            RawAESKeyring result = new RawAESKeyring();
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    DafnyFFI.SequenceFromByteArray(wrappingKey),
                    wrappingAlg
                    );
            return result;
        }
        public static RawRSAKeyring MakeRawRSAKeyring(byte[] nameSpace, byte[] name, DafnyFFI.RSAPaddingModes paddingMode, byte[] publicKey, byte[] privateKey)
        {
            // TODO: check for null values, ensure at least one key is non-null.
            RawRSAKeyring result = new RawRSAKeyring();
            RSAEncryption.RSAPaddingMode paddingModeDafny = paddingMode switch {
                DafnyFFI.RSAPaddingModes.PKCS1 => RSAEncryption.RSAPaddingMode.create_PKCS1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA1 => RSAEncryption.RSAPaddingMode.create_OAEP__SHA1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA256 => RSAEncryption.RSAPaddingMode.create_OAEP__SHA256(),
                _ => throw new NotYetSupportedException("Unsupported RSA Padding Mode")
            };
            result.__ctor(
                    DafnyFFI.SequenceFromByteArray(nameSpace),
                    DafnyFFI.SequenceFromByteArray(name),
                    paddingModeDafny,
                    DafnyFFI.NullableToOption(publicKey != null ? DafnyFFI.SequenceFromByteArray(publicKey) : null),
                    DafnyFFI.NullableToOption(privateKey != null ? DafnyFFI.SequenceFromByteArray(privateKey) : null)
                    );
            return result;
        }
    }
}
