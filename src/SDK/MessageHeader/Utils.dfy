include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Utils {
  import AlgorithmSuite
  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  /*
   * Utils
   */
  method ReadFixedLengthFromStreamOrFail(is: Streams.StringReader, n: nat) returns (ret: Result<array<uint8>>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(bytes) =>
        && n == bytes.Length
        && fresh(bytes)
      case Failure(_) => true
  {
    var bytes := new uint8[n];
    var bytesRead :- is.Read(bytes, 0, n);
    if bytesRead != n {
      return Failure("IO Error: Not enough bytes left on stream.");
    } else {
      return Success(bytes);
    }
  }
  /*
  // This is like StringWriter.WriteSimple
  // TODO: this is broken somehow
  method WriteFixedLengthToStreamOrFail(os: Streams.StringWriter, bytes: array<uint8>) returns (ret: Result<nat>)
    requires os.Valid()
    requires bytes !in os.Repr
    modifies os.Repr
    ensures old(os.Repr) == os.Repr
    ensures bytes !in os.Repr
    ensures os.Valid()
    ensures match ret
      case Success(len_written) =>
        && len_written == bytes.Length
        && os.pos == old(os.pos) + len_written
        && old(os.pos + len_written <= os.data.Length)
        && os.data[..] == old(os.data[..os.pos]) + bytes[..] + old(os.data[os.pos + len_written..])
      case Failure(e) => true
  {
    ghost var oldPos := os.pos;
    ghost var oldData := os.data;
    var oldCap := os.capacity();
    var len :- os.Write(bytes, 0, bytes.Length);
    if 0 < bytes.Length <= oldCap {
      // assert len == bytes.Length;
      assert oldPos + len <= oldData.Length;

      assert os.data[..oldPos] == oldData[..oldPos];
      assert os.data[oldPos..oldPos+len] == bytes[..];
      assert os.data[oldPos+len..] == oldData[oldPos + len..];

      assert os.data[..] == oldData[..oldPos] + bytes[..] + oldData[oldPos + len..];
      assert os.pos == oldPos + len;
      return Success(len);
    } else {
      return Failure("Serialization Error: Reached end of stream.");
    }
  }
  */
  /*
  // This is like StringWriter.WriteSingleByteSimple
  method WriteSingleByteToStreamOrFail(os: Streams.StringWriter, byte: uint8) returns (ret: Result<nat>)
    requires os.Valid()
    modifies os.Repr
    ensures old(os.Repr) == os.Repr
    ensures os.Valid()
    ensures match ret
      case Success(len_written) =>
        && len_written == 1
        && old(os.pos + len_written <= os.data.Length)
        && os.data[..] == old(os.data[..os.pos]) + [byte] + old(os.data[os.pos + len_written..])
        && os.pos == old(os.pos) + len_written
      case Failure(e) => true
  {
    var len :- os.WriteSingleByte(byte);
    if len == 1 {
      return Success(len);
    } else {
      return Failure("Serialization Error: Reached end of stream.");
    }
  }
  */

  predicate SortedKVPairsUpTo(a: seq<(seq<uint8>, seq<uint8>)>, n: nat)
    requires n <= |a|
  {
    forall j :: 0 < j < n ==> LexCmpSeqs(a[j-1].0, a[j].0, UInt8Less)
  }

  predicate SortedKVPairs(a: seq<(seq<uint8>, seq<uint8>)>)
  {
    SortedKVPairsUpTo(a, |a|)
  }
}
