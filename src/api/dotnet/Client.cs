using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
using CMMDefs;
using KeyringDefs;
using Dafny;
using ibyteseq = Dafny.ISequence<byte>;
using icharseq = Dafny.ISequence<char>;
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
            //public int? plaintextLength { get; set;}
            public Dictionary<string, string> encryptionContext{ get; set;} = new Dictionary<string, string>() ;
            public ushort? algorithmSuiteID { get; set;}
            public uint? frameLength { get; set;}

            internal ESDKClient.EncryptRequest GetDafnyRequest() {
                if (this.plaintext == null) {
                    throw new ArgumentNullException("EncryptRequest.plaintext must not be null.");
                } else if (this.cmm == null && this.keyring == null) {
                    throw new ArgumentNullException("EncryptRequest.cmm and EncryptRequest.keyring cannot both be null.");
                } else if (this.cmm != null && this.keyring != null) {
                    throw new ArgumentException("EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both).");
                } else if (this.encryptionContext == null) {
                    throw new ArgumentNullException("EncryptRequest.encryptionContext must not be null.");
                } else if (this.algorithmSuiteID != null && !AlgorithmSuite.__default.VALID__IDS.Elements.Contains((ushort)this.algorithmSuiteID)) {
                    throw new ArgumentException("Invalid algorithm suite.");
                }

                if (this.cmm == null) {
                    this.cmm = CMMs.MakeDefaultCMM(this.keyring);
                }

                var dafnyPlaintext = ESDKClient.SequenceStreamUnion.create(DafnyFFI.SequenceFromMemoryStream(this.plaintext));
                var optionalAlgID = this.algorithmSuiteID != null ? STL.Option<ushort>.create_Some((ushort)this.algorithmSuiteID) : STL.Option<ushort>.create_None();

                return new ESDKClient.EncryptRequest{
                    plaintext = dafnyPlaintext,
                    cmm = this.cmm,
                    plaintextLength = new BigInteger(dafnyPlaintext.bytes.Count),
                    encryptionContext = ToDafnyEncryptionContext(this.encryptionContext),
                    algorithmSuiteID = optionalAlgID,
                    frameLength = this.frameLength != null ? STL.Option<uint>.create_Some((uint)this.frameLength) : STL.Option<uint>.create_None()
                };
            }
        }
        
        public class DecryptRequest {
            public MemoryStream message { get; set;}
            public CMM cmm { get; set;}
            public Keyring keyring { get; set;}

            internal ESDKClient.DecryptRequest GetDafnyRequest() {
                if (this.message == null) {
                    throw new ArgumentNullException("DecryptRequest.message must not be null.");
                } else if (this.cmm == null && this.keyring == null) {
                    throw new ArgumentNullException("DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");
                } else if (this.cmm != null && this.keyring != null) {
                    throw new ArgumentException("DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
                }

                if (this.cmm == null) {
                    this.cmm = CMMs.MakeDefaultCMM(this.keyring);
                }

                var dafnyMessage = ESDKClient.SequenceStreamUnion.create(DafnyFFI.SequenceFromMemoryStream(this.message));

                return new ESDKClient.DecryptRequest{
                    message = dafnyMessage,
                    cmm = this.cmm
                };
            }
        }
    }
}
