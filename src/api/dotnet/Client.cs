
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
        public static MemoryStream Encrypt(MemoryStream plaintext, CMM cmm, Dictionary<string, string> encryptionContext) {
            byteseq dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(plaintext);
            Sequence<Tuple2<byteseq, byteseq>> dafnyEncryptionContext = 
                ToDafnyEncryptionContext(encryptionContext);
    
            // TODO: This isn't checking for nulls or any of the requirements on the Dafny method.
            // See https://github.com/dafny-lang/dafny/issues/461.
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<byteseq> result = ESDKClient.__default.Encrypt(dafnyPlaintext, cmm, dafnyEncryptionContext);
    
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }
  
        // TODO: Proper documentation
        public static MemoryStream Decrypt(MemoryStream cyphertext, CMM cmm) {
            byteseq dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(cyphertext);
    
            // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
            STL.Result<byteseq> result = ESDKClient.__default.Decrypt(dafnyPlaintext, cmm);
    
            return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.ExtractResult(result));
        }
  
        private static Sequence<Tuple2<byteseq, byteseq>> 
            ToDafnyEncryptionContext(Dictionary<string, string> encryptionContext)
        {
            IEnumerable<Tuple2<byteseq, byteseq>> e = encryptionContext.Select(entry
                => new Tuple2<byteseq, byteseq>(DafnyFFI.DafnyUTF8BytesFromString(entry.Key), DafnyFFI.DafnyUTF8BytesFromString(entry.Value)));
            return Sequence<Tuple2<byteseq, byteseq>>.FromElements(e.ToArray());
        }
    }
}
