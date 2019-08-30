include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Utils {
    import AlgorithmSuite
    import opened Streams
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened UTF8
    /*
     * Utils
     */
    method readFixedLengthFromStreamOrFail(is: StringReader, n: nat) returns (ret: Either<array<uint8>, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(bytes) =>
                    && n == bytes.Length
                    && fresh(bytes)
                case Right(_)    => true
        ensures is.Valid()
    {
        var bytes := new uint8[n];
        var out: Either<nat, Error>;
        out := is.Read(bytes, 0, n);
        match out {
            case Left(bytesRead) =>
                if bytesRead != n {
                    return Right(IOError("Not enough bytes left on stream."));
                } else {
                    return Left(bytes);
                }
            case Right(e) => return Right(e);
        }
    }
    /*
    // This is like StringWriter.WriteSimple
    // TODO: this is broken somehow
    method WriteFixedLengthToStreamOrFail(os: StringWriter, bytes: array<uint8>) returns (ret: Result<nat>)
      requires os.Valid()
      requires bytes !in os.Repr
      modifies os.Repr
      ensures old(os.Repr) == os.Repr
      ensures bytes !in os.Repr
      ensures os.Valid()
      ensures
        match ret
          case Left(len_written) =>
            && len_written == bytes.Length
            && os.pos == old(os.pos) + len_written
            && old(os.pos + len_written <= os.data.Length)
            && os.data[..] == old(os.data[..os.pos]) + bytes[..] + old(os.data[os.pos + len_written..])
          case Right(e) => true
    {
        ghost var oldPos := os.pos;
        ghost var oldData := os.data;
        var oldCap := os.capacity();
        ret := os.Write(bytes, 0, bytes.Length);
        match ret {
            case Left(len) =>
                if oldCap >= bytes.Length > 0 {
                //if len == bytes.Length {
                   // assert len == bytes.Length;
                    assert oldPos + len <= oldData.Length;

                    assert os.data[..oldPos] == oldData[..oldPos];
                    assert os.data[oldPos..oldPos+len] == bytes[..];
                    assert os.data[oldPos+len..] == oldData[oldPos + len..];

                    assert os.data[..] == oldData[..oldPos] + bytes[..] + oldData[oldPos + len..];
                    assert os.pos == oldPos + len;
                    return Left(len);
                } else {
                    return Right(SerializationError("Reached end of stream."));
                }
            case Right(e)  => return ret;
        }
    }
    */
    /*
    // This is like StringWriter.WriteSingleByteSimple
    method WriteSingleByteToStreamOrFail(os: StringWriter, byte: uint8) returns (ret: Result<nat>)
      requires os.Valid()
      modifies os.Repr
      ensures old(os.Repr) == os.Repr
      ensures os.Valid()
      ensures
        match ret
          case Left(len_written) =>
            && len_written == 1
            && old(os.pos + len_written <= os.data.Length)
            && os.data[..] == old(os.data[..os.pos]) + [byte] + old(os.data[os.pos + len_written..])
            && os.pos == old(os.pos) + len_written
          case Right(e) => true
    {
        ret := os.WriteSingleByte(byte);
        match ret {
            case Left(len) =>
                if len == 1 {
                    return Left(len);
                } else {
                    return Right(SerializationError("Reached end of stream."));
                }
            case Right(e)  => return ret;
        }
    }
    */

    predicate SortedKVPairsUpTo(a: array<(array<uint8>, array<uint8>)>, n: nat)
        requires n <= a.Length
        reads a
        reads set i | 0 <= i < n :: a[i].0
    {
        forall j :: 0 < j < n ==> lexCmpArrays(a[j-1].0, a[j].0, ltByte)
    }

    predicate SortedKVPairs(a: array<(array<uint8>, array<uint8>)>)
        reads a
        reads set i | 0 <= i < a.Length :: a[i].0
    {
        SortedKVPairsUpTo(a, a.Length)
    }
}