
using System;
using System.IO;
using System.Collections.Generic;
using _75_CMMDefs_Compile;
using byteseq = Dafny.Sequence<byte>;

// Sample of a top-level AWS Encryption SDK client method.
public class Client {
  
  public MemoryStream Encrypt(MemoryStream plaintext, CMM cmm, Dictionary<string, string> encryptionContext) {
    byteseq dafnyPlaintext = DafnyFFI.SequenceFromMemoryStream(plaintext);
    Dafny.Sequence<_System.Tuple2<byteseq, byteseq>> dafnyEC = 
        DafnyFFI.SeqOfPairsFromDictionary(encryptionContext);
    
    // TODO: Might need a lock here if ANYTHING in the Dafny runtime isn't threadsafe!
    STL.Result<byteseq> result = ESDKClient.__default.Encrypt(dafnyPlaintext, cmm, dafnyEC);
    
    return DafnyFFI.MemoryStreamFromSequence(DafnyFFI.GetResult<byteseq>(result));
  }
}