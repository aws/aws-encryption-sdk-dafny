
using System;
using System.IO;
using Wrappers_Compile;
using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;

namespace TestUtils {
  public partial class __default {

    public static _IOutcome<icharseq> WriteFile(icharseq path, ibyteseq contents) {
      try {
        var pathString = DafnyFFI.StringFromDafnyString(path);
        var bytes = DafnyFFI.ByteArrayFromSequence(contents);
        File.WriteAllBytes(pathString, bytes);
        return Outcome<icharseq>.create_Pass();
      } catch (Exception e) {
        return DafnyFFI.CreateFail(e.Message);
      }
    }
    
    public static _IResult<ibyteseq, icharseq> ReadFile(icharseq path) {
      try {
        var pathString = DafnyFFI.StringFromDafnyString(path);
        var bytes = File.ReadAllBytes(pathString);
        var byteseq = DafnyFFI.SequenceFromByteArray(bytes);
        return Result<ibyteseq, icharseq>.create_Success(byteseq);
      } catch (Exception e) {
        return DafnyFFI.CreateFailure<ibyteseq>(e.Message);
      }
    }
  }
}