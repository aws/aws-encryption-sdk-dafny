using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using _System;
using Dafny;

using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;

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
  
    public static Dafny.Sequence<_System.Tuple2<byteseq, byteseq>> 
        SeqOfPairsFromDictionary(Dictionary<string, string> dictionary)
    {
        IEnumerable<Tuple2<byteseq, byteseq>> e = dictionary.Select(entry
            => new Tuple2<byteseq, byteseq>(DafnyUTF8BytesFromString(entry.Key), DafnyUTF8BytesFromString(entry.Value)));
        return Sequence<Tuple2<byteseq, byteseq>>.FromElements(e.ToArray());
    }

    public static string StringFromDafnyString(charseq dafnyString) {
        // This is safe under the assumption that nothing modifies the wrapped array
        return new string(dafnyString.Elements);
    }
    
    public static charseq DafnyStringFromString(string s) {
        return charseq.FromArray(s.ToCharArray());
    }
    
    public static byteseq DafnyUTF8BytesFromString(string s) {
        return byteseq.FromArray(Encoding.UTF8.GetBytes(s));
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
