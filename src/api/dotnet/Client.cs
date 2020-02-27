
using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;
using _System;
using CMMDefs;
using Dafny;
using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;

namespace AWSEncryptionSDK
{
    // TODO: What to name this?
    public class Client {

        // TODO: Proper documentation
        public static MemoryStream Encrypt(MemoryStream plaintext, CMM cmm, ushort? algorithmSuiteID = null, uint? frameLength = null, Dictionary<string, string> encryptionContext = null) {
            if (algorithmSuiteID != null && !AlgorithmSuite.__default.VALID__IDS.Elements.Contains((ushort)algorithmSuiteID)) {
                throw new ArgumentException("Invalid algorithmSuiteID: " + algorithmSuiteID.ToString());
            }
            byteseq dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(plaintext);
    
            // TODO: This isn't checking for nulls or any of the requirements on the Dafny method.
            // See https://github.com/dafny-lang/dafny/issues/461.
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            var optAlgorithmSuiteID = algorithmSuiteID != null ? STL.Option<ushort>.create_Some((ushort)algorithmSuiteID) : STL.Option<ushort>.create_None();
            var optFrameLength = frameLength != null ? STL.Option<uint>.create_Some((uint)frameLength) : STL.Option<uint>.create_None();
            var dafnyEncryptionContext = encryptionContext != null ? STL.Option<Map<Sequence<byte>, Sequence<byte>>>.create_Some(ToDafnyEncryptionContext(encryptionContext)) : STL.Option<Map<Sequence<byte>, Sequence<byte>>>.create_None();
            STL.Result<byteseq> result = ESDKClient.__default.Encrypt(
                    dafnyPlaintext,
                    cmm,
                    optAlgorithmSuiteID,
                    optFrameLength,
                    dafnyEncryptionContext
                    );
    
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }
  
        // TODO: Proper documentation
        public static MemoryStream Decrypt(MemoryStream cyphertext, CMM cmm) {
            byteseq dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(cyphertext);
    
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<byteseq> result = ESDKClient.__default.Decrypt(dafnyPlaintext, cmm);
    
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }
  
        private static Map<Sequence<byte>, Sequence<byte>> 
            ToDafnyEncryptionContext(Dictionary<string, string> encryptionContext)
        {
            IEnumerable<Pair<byteseq, byteseq>> e = encryptionContext.Select(entry
                => new Pair<byteseq, byteseq>(DafnyFFI.DafnyUTF8BytesFromString(entry.Key), DafnyFFI.DafnyUTF8BytesFromString(entry.Value)));
            return Map<Sequence<byte>, Sequence<byte>>.FromElements(e.ToArray());
        }
    }
}
