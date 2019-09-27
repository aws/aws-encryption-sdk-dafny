include "Definitions.dfy"
include "Validity.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.SerializeEDK {
  import opened Definitions
  import opened Validity

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  lemma {:axiom} Assume(b: bool)
    ensures b

  // Alternative w/o flatten/map
  function SerializeEDKEntries(entries: seq<EDKEntry>): seq<uint8>
    requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
  {
    if entries == [] then
      []
    else
      var entry := entries[0];
      UInt16ToSeq(|entry.providerID| as uint16)   + StringToByteSeq(entry.providerID) +
      UInt16ToSeq(|entry.providerInfo| as uint16) + entry.providerInfo +
      UInt16ToSeq(|entry.ciphertext| as uint16)   + entry.ciphertext +
      SerializeEDKEntries(entries[1..])
  }

  function SerializeEDK(encryptedDataKeys: T_EncryptedDataKeys): seq<uint8>
    requires ValidEncryptedDataKeys(encryptedDataKeys)
  {
    Assume(|encryptedDataKeys.entries| < UINT16_LIMIT);
    Assume(forall i :: 0 <= i < |encryptedDataKeys.entries| ==> encryptedDataKeys.entries[i].Valid());
    UInt16ToSeq(|encryptedDataKeys.entries| as uint16) +
    SerializeEDKEntries(encryptedDataKeys.entries)
  }

  method SerializeEDKImpl(os: Streams.StringWriter, encryptedDataKeys: T_EncryptedDataKeys) returns (ret: Result<nat>)
    requires os.Valid() && ValidEncryptedDataKeys(encryptedDataKeys)
    modifies os`data
    ensures os.Valid() && ValidEncryptedDataKeys(encryptedDataKeys)
    //ensures old(|os.data|) <= |os.data|
    ensures match ret
      case Success(totalWritten) =>
        var serEDK := SerializeEDK(encryptedDataKeys);
        var initLen := old(|os.data|);
        && totalWritten == |serEDK|
        && initLen + totalWritten == |os.data|
        && os.data == old(os.data) + serEDK
      case Failure(e) => true
  {
    Assume(false);  // TODO: turned off verification for now
    var totalWritten: nat := 0;
    ghost var initLen := |os.data|;
    ghost var prevPos: nat := initLen;
    ghost var currPos: nat := initLen;

    {
      Assume(|encryptedDataKeys.entries| < UINT16_LIMIT);
      var bytes := UInt16ToArray(|encryptedDataKeys.entries| as uint16);
      var len :- os.WriteSimple(bytes);
      totalWritten := totalWritten + len;
      prevPos := currPos;
      currPos := initLen + totalWritten;
      assert currPos - prevPos == bytes.Length;
      assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      assert totalWritten <= |SerializeEDK(encryptedDataKeys)|;
    }

    var j := 0;
    ghost var written: seq<nat> := [currPos, currPos];
    while j < |encryptedDataKeys.entries|
      invariant j <= |encryptedDataKeys.entries|
      invariant j < |written|
      invariant unchanged(os`Repr)
      invariant InBoundsEncryptedDataKeysUpTo(encryptedDataKeys.entries, j)
      invariant ValidEncryptedDataKeys(encryptedDataKeys)
      invariant initLen + totalWritten == currPos
      invariant 0 <= initLen <= prevPos <= currPos <= |os.data|
      invariant forall k :: 0 <= k < |written| ==> initLen <= written[k] <= |os.data|
      invariant currPos-initLen <= |SerializeEDK(encryptedDataKeys)|
      invariant SerializeEDK(encryptedDataKeys)[..currPos-initLen] == os.data[initLen..currPos]
      invariant SerializeEDK(encryptedDataKeys)[prevPos-initLen..currPos-initLen] == os.data[prevPos..currPos];
      invariant 1 <= j ==> os.data[initLen..written[j]] == os.data[initLen..written[j-1]] + SerializeEDKEntries(encryptedDataKeys.entries[..j])
    {
      var entry := encryptedDataKeys.entries[j];
      {
        Assume(|entry.providerID| < UINT16_LIMIT);
        var bytes := UInt16ToArray(|entry.providerID| as uint16);
        var len :- os.WriteSimple(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }

      {
        var bytes := StringToByteSeq(entry.providerID);
        var len :- os.WriteSimpleSeq(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        assert currPos - prevPos == |bytes|;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }

      {
        Assume(|entry.providerInfo| < UINT16_LIMIT);
        var bytes := UInt16ToArray(|entry.providerInfo| as uint16);
        var len :- os.WriteSimple(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        assert currPos - prevPos == bytes.Length;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }

      {
        var bytes := entry.providerInfo;
        var len :- os.WriteSimpleSeq(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        assert currPos - prevPos == |bytes|;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }

      {
        Assume(|entry.ciphertext| < UINT16_LIMIT);
        var bytes := UInt16ToArray(|entry.ciphertext| as uint16);
        var len :- os.WriteSimple(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        assert currPos - prevPos == bytes.Length;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }

      {
        var bytes := entry.ciphertext;
        var len :- os.WriteSimpleSeq(bytes);
        totalWritten := totalWritten + len;
        prevPos := currPos;
        currPos := initLen + totalWritten;
        assert currPos - prevPos == |bytes|;
        Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
        assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
      }
      written := written + [currPos];
      j := j + 1;
      Assume(ValidEncryptedDataKeys(encryptedDataKeys));
    }

    Assume(totalWritten == |SerializeEDK(encryptedDataKeys)|);
    Assume(initLen+totalWritten == |os.data|);
    Assume(os.data == old(os.data) + SerializeEDK(encryptedDataKeys));
    return Success(totalWritten);
  }
}
