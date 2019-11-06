
using System;
using System.IO;
using System.Collections.Generic;

using byteseq = Dafny.Sequence<byte>;

public class Client {
  
  private ESDK.Client dafnyClient;
  
  MemoryStream Encrypt(MemoryStream plaintext, Dictionary<string, string> encryptionContext) {
    byteseq dafnyPlaintext = DafnySequenceFromMemoryStream(plaintext);
    Dafny.Sequence<_System.Tuple2<byteseq, byteseq>> dafnyEC = DafnySeqOfPairsFromDictionary(encryptionContext);
    
    // TODO: Might need a GIL here if ANYTHING in the Dafny runtime isn't threadsafe!
    STL.Result<ESDK.Encryption> result = dafnyClient.Encrypt(dafnyPlaintext, dafnyEC);
    
    return MemoryStreamFromDafnySequence(getResult<ESDK.Encryption>(result).ctxt);
  }

  private MemoryStream MemoryStreamFromDafnySequence(byteseq seq) {
    // TODO: Find a way to safely avoid copying 
    byte[] copy = new byte[seq.Elements.Length];
    Array.Copy(seq.Elements, 0, copy, 0, seq.Elements.Length);
    return new MemoryStream(copy);
  }
  
  private byteseq DafnySequenceFromMemoryStream(MemoryStream bytes) {
    // TODO: Find a way to safely avoid copying 
    return new Dafny.Sequence<byte>(bytes.ToArray());
  }
  
  private Dafny.Sequence<_System.Tuple2<byteseq,byteseq>> DafnySeqOfPairsFromDictionary(Dictionary<string, string> bytes) {
    // TODO: Similar implementation to the above methods. Can we find a more general way to map
    // to and from Dafny.Sequence and IEnumerable
    throw new NotImplementedException();
  }

  private T getResult<T>(STL.Result<T> result) {
    if (result is STL.Result_Success<T> s) {
      return s.value;
    } else if (result is STL.Result_Failure<T> f) {
      // TODO-RS: Need to refine the wrapped value in a Failure so we
      // can throw specific exception types.
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
