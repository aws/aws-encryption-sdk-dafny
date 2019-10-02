include "Definitions.dfy"
include "Validity.dfy"
include "../Materials.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.SerializeEDK {
  import Msg = Definitions
  import V = Validity
  import Materials

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // ----- Specification -----

  function SerializeEDKs(encryptedDataKeys: Msg.EncryptedDataKeys): seq<uint8>
    requires V.ValidEncryptedDataKeys(encryptedDataKeys)
  {
    reveal V.ValidEncryptedDataKeys();
    var n := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) +
    SerializeEDKEntries(encryptedDataKeys.entries, 0, n)
  }

  function SerializeEDKEntries(entries: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
  {
    if lo == hi then [] else SerializeEDKEntries(entries, lo, hi - 1) + SerializeEDKEntry(entries[hi - 1])
  }

  function SerializeEDKEntry(edk: Materials.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
  {
    UInt16ToSeq(|edk.providerID| as uint16)   + StringToByteSeq(edk.providerID) +
    UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo +
    UInt16ToSeq(|edk.ciphertext| as uint16)   + edk.ciphertext
  }

  // ----- Implementation -----

  method SerializeEDKsImpl(os: Streams.StringWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: Result<nat>)
    requires os.Valid() && V.ValidEncryptedDataKeys(encryptedDataKeys)
    modifies os`data
    ensures os.Valid() && V.ValidEncryptedDataKeys(encryptedDataKeys)
    ensures match ret
      case Success(totalWritten) =>
        var serEDK := SerializeEDKs(encryptedDataKeys);
        var initLen := old(|os.data|);
        && totalWritten == |serEDK|
        && initLen + totalWritten == |os.data|
        && os.data == old(os.data) + serEDK
      case Failure(e) => true
  {
    reveal V.ValidEncryptedDataKeys();

    var totalWritten := 0;

    var bytes := UInt16ToArray(|encryptedDataKeys.entries| as uint16);
    var len :- os.WriteSimple(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 2;

    var j := 0;
    ghost var n := |encryptedDataKeys.entries|;
    while j < |encryptedDataKeys.entries|
      invariant j <= n == |encryptedDataKeys.entries|
      invariant os.data ==
        old(os.data) +
        UInt16ToSeq(n as uint16) +
        SerializeEDKEntries(encryptedDataKeys.entries, 0, j);
      invariant totalWritten == 2 + |SerializeEDKEntries(encryptedDataKeys.entries, 0, j)|
    {
      var entry := encryptedDataKeys.entries[j];

      bytes := UInt16ToArray(|entry.providerID| as uint16);
      len :- os.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      var byteSeq := StringToByteSeq(entry.providerID);
      len :- os.WriteSimpleSeq(byteSeq);
      totalWritten := totalWritten + len;

      bytes := UInt16ToArray(|entry.providerInfo| as uint16);
      len :- os.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      len :- os.WriteSimpleSeq(entry.providerInfo);
      totalWritten := totalWritten + len;

      bytes := UInt16ToArray(|entry.ciphertext| as uint16);
      len :- os.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      len :- os.WriteSimpleSeq(entry.ciphertext);
      totalWritten := totalWritten + len;

      j := j + 1;
    }

    return Success(totalWritten);
  }
}
