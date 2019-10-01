include "Definitions.dfy"
include "SerializeAAD.dfy"
include "SerializeEDK.dfy"
include "Validity.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.Serialize {
  import opened Definitions
  import SerializeAAD
  import SerializeEDK
  import opened Validity

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  function {:opaque} Serialize(hb: HeaderBody): seq<uint8>
    requires ValidHeaderBody(hb)
  {
    reveal ValidHeaderBody();
    [hb.version as uint8] +
    [hb.typ as uint8] +
    UInt16ToSeq(hb.algorithmSuiteID as uint16) +
    hb.messageID +
    SerializeAAD.SerializeAAD(hb.aad) +
    SerializeEDK.SerializeEDKs(hb.encryptedDataKeys) +
    (match hb.contentType case NonFramed => [0x01] case Framed => [0x02]) +
    hb.reserved +
    [hb.ivLength] +
    UInt32ToSeq(hb.frameLength)
  }

  method SerializeHeaderBody(os: Streams.StringWriter, hb: HeaderBody) returns (ret: Result<nat>)
    requires os.Valid() && ValidHeaderBody(hb)
    modifies os`data
    ensures os.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHb := (reveal Serialize(); Serialize(hb));
        var initLen := old(|os.data|);
        && totalWritten == |serHb|
        && initLen + totalWritten == |os.data|
        && serHb == os.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var totalWritten := 0;

    var len :- os.WriteSingleByteSimple(hb.version as uint8);
    totalWritten := totalWritten + len;

    len :- os.WriteSingleByteSimple(hb.typ as uint8);
    totalWritten := totalWritten + len;

    var bytes := UInt16ToArray(hb.algorithmSuiteID as uint16);
    len :- os.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    len :- os.WriteSimpleSeq(hb.messageID);
    totalWritten := totalWritten + len;

    reveal ValidHeaderBody();
    len :- SerializeAAD.SerializeAADImpl(os, hb.aad);
    totalWritten := totalWritten + len;

    len :- SerializeEDK.SerializeEDKsImpl(os, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;

    var contentType: uint8;
    match hb.contentType {
      case NonFramed => contentType := 0x01;
      case Framed    => contentType := 0x02;
    }
    len :- os.WriteSingleByteSimple(contentType);
    totalWritten := totalWritten + len;

    len :- os.WriteSimpleSeq(hb.reserved);
    totalWritten := totalWritten + len;

    len :- os.WriteSingleByteSimple(hb.ivLength);
    totalWritten := totalWritten + len;

    bytes := UInt32ToArray(hb.frameLength);
    len :- os.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    reveal Serialize();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(os: Streams.StringWriter, ha: HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<nat>)
    requires os.Valid()
    requires ValidHeaderAuthentication(ha, algorithmSuiteID)
    modifies os`data
    ensures os.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHa := ha.iv + ha.authenticationTag;
        var initLen := old(|os.data|);
        && totalWritten == |serHa|
        && initLen + totalWritten == |os.data|
        && serHa == os.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var m :- os.WriteSimpleSeq(ha.iv);
    var n :- os.WriteSimpleSeq(ha.authenticationTag);
    return Success(m + n);
  }
}
