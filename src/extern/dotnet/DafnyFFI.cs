using System;
using System.Collections.Generic;
using System.IO;
using Dafny;

public class DafnyFFI {
  
    public static MemoryStream MemoryStreamFromSequence(Sequence<byte> seq) {
        // TODO: Find a way to safely avoid copying 
        byte[] copy = new byte[seq.Elements.Length];
        Array.Copy(seq.Elements, 0, copy, 0, seq.Elements.Length);
        return new MemoryStream(copy);
    }
  
    public static Sequence<byte> SequenceFromMemoryStream(MemoryStream bytes) {
        // TODO: Find a way to safely avoid copying 
        return Sequence<byte>.FromArray(bytes.ToArray());
    }
  
    public static Dafny.Sequence<_System.Tuple2<Sequence<byte>,Sequence<byte>>> 
        SeqOfPairsFromDictionary(Dictionary<string, string> bytes) {
        // TODO: Similar implementation to the above methods.
        // Can we find a more general way to map to and from Dafny.Sequence and IEnumerable?
        throw new NotImplementedException();
    }

    public static string StringFromDafnyString(Dafny.Sequence<char> dafnyString) {
        // This is safe under the assumption that nothing modifies the wrapped array
        return new string(dafnyString.Elements);
    }
  
    public static T GetResult<T>(STL.Result<T> result) {
        if (result is STL.Result_Success<T> s) {
            return s.value;
        } else if (result is STL.Result_Failure<T> f) {
            // TODO-RS: Need to refine the wrapped value in a Failure so we
            // can throw specific exception types.
            throw new DafnyException(StringFromDafnyString(f.error));
        } else {
            throw new ArgumentException(message: "Unrecognized STL.Result constructor");
        }
    }
}

public class DafnyException : Exception {
    public DafnyException(string message) : base(message) {
    }
}
