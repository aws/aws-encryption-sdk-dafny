
using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;
using CMMDefs;
using Dafny;
using ibyteseq = Dafny.ISequence<byte>;
using icharseq = Dafny.ISequence<char>;
using encryptioncontext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;
using Streams;
using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;
using ESDKClient;

namespace AWSEncryptionSDK
{
    // TODO: What to name this?
    public class Client {

        // TODO: Proper documentation
        // TODO: should return some custom stream that "reads" the encryption
        // ie it can't all be loaded into memory
        public static OutputStream Encrypt(Stream plaintext, CMM cmm, Dictionary<string, string> encryptionContext = null, ushort? algorithmSuiteID = null, uint? frameLength = null) {
            if (algorithmSuiteID != null && !AlgorithmSuite.__default.VALID__IDS.Elements.Contains((ushort)algorithmSuiteID)) {
                throw new ArgumentException("Invalid algorithmSuiteID: " + algorithmSuiteID.ToString());
            }
            // TODO need to convert Stream to Dafny InputStream
            InputStream dafnyStream = DafnyFFI.InputStreamFromStream(plaintext);
    
            // TODO: This isn't checking for nulls or any of the requirements on the Dafny method.
            // See https://github.com/dafny-lang/dafny/issues/461.
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            var optAlgorithmSuiteID = algorithmSuiteID != null ? STL.Option<ushort>.create_Some((ushort)algorithmSuiteID) : STL.Option<ushort>.create_None();
            var optFrameLength = frameLength != null ? STL.Option<uint>.create_Some((uint)frameLength) : STL.Option<uint>.create_None();
            var dafnyEncryptionContext = encryptionContext != null ? STL.Option<encryptioncontext>.create_Some(ToDafnyEncryptionContext(encryptionContext)) : STL.Option<encryptioncontext>.create_None();
            STL.Result<ESDKClient.EncryptorStream> result = ESDKClient.__default.StreamEncrypt(
                    dafnyStream,
                    cmm,
                    dafnyEncryptionContext,
                    optAlgorithmSuiteID,
                    optFrameLength
                    );
            return new OutputStream(DafnyFFI.ExtractResult(result));
        }
  
        // TODO: Proper documentation
        // TODO: should return some custom stream that "reads" the decryption
        // ie it can't all be loaded into memory
        public static MemoryStream Decrypt(Stream cyphertext, CMM cmm) {
            ibyteseq dafnyPlaintext = DafnyFFI.SequenceFromStream(cyphertext);
    
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<ibyteseq> result = ESDKClient.__default.Decrypt(dafnyPlaintext, cmm);
    
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }
  
        private static encryptioncontext ToDafnyEncryptionContext(Dictionary<string, string> encryptionContext)
        {
            IEnumerable<Pair<ibyteseq, ibyteseq>> e = encryptionContext.Select(entry
                => new Pair<ibyteseq, ibyteseq>(DafnyFFI.DafnyUTF8BytesFromString(entry.Key), DafnyFFI.DafnyUTF8BytesFromString(entry.Value)));
            return encryptioncontext.FromElements(e.ToArray());
        }
    }
}
