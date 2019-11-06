
using System;
using System.IO;
using System.Collections.Generic;

using byteseq = Dafny.Sequence<byte>;

public class Client {
  private ESDK.Client dafnyClient;
  
  MemoryStream Encrypt(MemoryStream plaintext, Dictionary<string, string> encryptionContext) {
    byteseq dafnyPlaintext = DafnySequenceFromMemoryStream(plaintext);
    Dafny.Sequence<_System.Tuple2<byteseq, byteseq>> dafnyEC = DafnySeqOfPairsFromDictionary(encryptionContext);
    STL.Result<ESDK.Encryption> result = dafnyClient.Encrypt(dafnyPlaintext, dafnyEC);
    return MemoryStreamFromDafnySequence(getResult<ESDK.Encryption>(result).ctxt);
  }

  private MemoryStream MemoryStreamFromDafnySequence(byteseq seq) {
    // TODO: Unsafe! Need to make a copy.
    return new MemoryStream(seq.Elements);
  }
  
  private byteseq DafnySequenceFromMemoryStream(MemoryStream bytes) {
    throw new NotImplementedException();
  }
  
  private Dafny.Sequence<_System.Tuple2<byteseq,byteseq>> DafnySeqOfPairsFromDictionary(Dictionary<string, string> bytes) {
    throw new NotImplementedException();
  }

  private T getResult<T>(STL.Result<T> result) {
    if (result is STL.Result_Success<T> s) {
      return s.value;
    } else if (result is STL.Result_Failure<T> f) {
      // TODO-RS: Need to refine the wrapped value in a Failure
      throw new DafnyException(StringFromDafnyString(f.error));
    } else {
      throw new ArgumentException(message: "Unrecognized STL.Result constructor", paramName: nameof(result));
    }
  }

  private string StringFromDafnyString(Dafny.Sequence<char> dafnyString) {
    return new string(dafnyString.Elements);
  }
}

public class DafnyException : Exception {
  public DafnyException(string message) : base(message) {
  }
}
