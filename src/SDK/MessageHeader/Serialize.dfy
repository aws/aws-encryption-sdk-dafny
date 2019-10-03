include "Definitions.dfy"
include "SerializeAAD.dfy"
include "SerializeEDK.dfy"
include "Validity.dfy"
include "../AlgorithmSuite.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.Serialize {
  import Msg = Definitions
  import SerializeAAD
  import SerializeEDK
  import V = Validity
  import AlgorithmSuite

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  function {:opaque} Serialize(hb: Msg.HeaderBody): seq<uint8>
    requires V.ValidHeaderBody(hb)
  {
    reveal V.ValidHeaderBody();
    [hb.version as uint8] +
    [hb.typ as uint8] +
    UInt16ToSeq(hb.algorithmSuiteID as uint16) +
    hb.messageID +
    SerializeAAD.SerializeAAD(hb.aad) +
    SerializeEDK.SerializeEDKs(hb.encryptedDataKeys) +
    [Msg.ContentTypeToUInt8(hb.contentType)] +
    hb.reserved +
    [hb.ivLength] +
    UInt32ToSeq(hb.frameLength)
  }

  method SerializeHeaderBody(wr: Streams.StringWriter, hb: Msg.HeaderBody) returns (ret: Result<nat>)
    requires wr.Valid() && V.ValidHeaderBody(hb)
    modifies wr`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHb := (reveal Serialize(); Serialize(hb));
        var initLen := old(|wr.data|);
        && totalWritten == |serHb|
        && initLen + totalWritten == |wr.data|
        && serHb == wr.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var totalWritten := 0;

    var len :- wr.WriteSingleByteSimple(hb.version as uint8);
    totalWritten := totalWritten + len;

    len :- wr.WriteSingleByteSimple(hb.typ as uint8);
    totalWritten := totalWritten + len;

    var bytes := UInt16ToArray(hb.algorithmSuiteID as uint16);
    len :- wr.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    len :- wr.WriteSimpleSeq(hb.messageID);
    totalWritten := totalWritten + len;

    reveal V.ValidHeaderBody();
    len :- SerializeAAD.SerializeAADImpl(wr, hb.aad);
    totalWritten := totalWritten + len;

    len :- SerializeEDK.SerializeEDKsImpl(wr, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;

    var contentType := Msg.ContentTypeToUInt8(hb.contentType);
    len :- wr.WriteSingleByteSimple(contentType);
    totalWritten := totalWritten + len;

    len :- wr.WriteSimpleSeq(hb.reserved);
    totalWritten := totalWritten + len;

    len :- wr.WriteSingleByteSimple(hb.ivLength);
    totalWritten := totalWritten + len;

    bytes := UInt32ToArray(hb.frameLength);
    len :- wr.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    reveal Serialize();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(wr: Streams.StringWriter, ha: Msg.HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<nat>)
    requires wr.Valid()
    requires V.ValidHeaderAuthentication(ha, algorithmSuiteID)
    modifies wr`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHa := ha.iv + ha.authenticationTag;
        var initLen := old(|wr.data|);
        && totalWritten == |serHa|
        && initLen + totalWritten == |wr.data|
        && serHa == wr.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var m :- wr.WriteSimpleSeq(ha.iv);
    var n :- wr.WriteSimpleSeq(ha.authenticationTag);
    return Success(m + n);
  }
}
