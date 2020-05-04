using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
using CMMDefs;
using KeyringDefs;
using Dafny;
using ibyteseq = Dafny.ISequence<byte>;
using encryptioncontext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;

namespace AWSEncryptionSDK
{
    // TODO: What to name this?
    public class Client {

        // TODO: Proper documentation
        public static MemoryStream Encrypt(EncryptRequest request) {
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<ibyteseq> result = ESDKClient.__default.Encrypt(request.GetDafnyRequest());
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }

        // TODO: Proper documentation
        public static MemoryStream Decrypt(DecryptRequest request) {
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<ibyteseq> result = ESDKClient.__default.Decrypt(request.GetDafnyRequest());

            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }

        private static encryptioncontext ToDafnyEncryptionContext(Dictionary<string, string> encryptionContext)
        {
            IEnumerable<Pair<ibyteseq, ibyteseq>> e = encryptionContext.Select(entry
                => new Pair<ibyteseq, ibyteseq>(DafnyFFI.DafnyUTF8BytesFromString(entry.Key), DafnyFFI.DafnyUTF8BytesFromString(entry.Value)));
            return encryptioncontext.FromElements(e.ToArray());
        }

        public class EncryptRequest {
            public MemoryStream plaintext { get; set;}
            public CMM cmm { get; set;}
            public Keyring keyring { get; set;}
            public Dictionary<string, string> encryptionContext{ get; set;} = new Dictionary<string, string>() ;
            public ushort? algorithmSuiteID { get; set;}
            public uint? frameLength { get; set;}

            internal ESDKClient.EncryptRequest GetDafnyRequest() {
                if (this.plaintext == null) {
                    throw new ArgumentNullException("EncryptRequest.plaintext must not be null.");
                } else if (this.encryptionContext == null) {
                    throw new ArgumentNullException("EncryptRequest.encryptionContext must not be null.");
                }

                var dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(this.plaintext);
                var optionalAlgID = this.algorithmSuiteID != null ? STL.Option<ushort>.create_Some((ushort)this.algorithmSuiteID) : STL.Option<ushort>.create_None();

                return ESDKClient.EncryptRequest.create(
                    plaintext: dafnyPlaintext,
                    cmm: this.cmm,
                    keyring: this.keyring,
                    plaintextLength: new BigInteger(dafnyPlaintext.Count),
                    encryptionContext: ToDafnyEncryptionContext(this.encryptionContext),
                    algorithmSuiteID: optionalAlgID,
                    frameLength: this.frameLength != null ? STL.Option<uint>.create_Some((uint)this.frameLength) : STL.Option<uint>.create_None()
                );
            }
        }

        public class DecryptRequest {
            public MemoryStream message { get; set;}
            public CMM cmm { get; set;}
            public Keyring keyring { get; set;}

            internal ESDKClient.DecryptRequest GetDafnyRequest() {
                if (this.message == null) {
                    throw new ArgumentNullException("DecryptRequest.message must not be null.");
                }

                var dafnyMessage = DafnyFFI.SequenceFromMemoryStream(this.message);

                return ESDKClient.DecryptRequest.create(
                    message: dafnyMessage,
                    cmm: this.cmm,
                    keyring: this.keyring
                );
            }
        }
    }
}
