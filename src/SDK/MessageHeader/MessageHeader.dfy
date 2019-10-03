include "Definitions.dfy"
include "Deserialize.dfy"
include "Serialize.dfy"
include "Validity.dfy"

include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader {
  import AlgorithmSuite
  import opened StandardLibrary
  import Streams

  import D = Deserialize
  import S = Serialize

  method Deserialize(rd: Streams.StringReader) returns (res: Result<Definitions.Header>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match res
      case Success(header) => Validity.ValidHeader(header)
      case Failure(_) => true
  {
    var body :- D.DeserializeHeaderBody(rd);
    var auth :- D.DeserializeHeaderAuthentication(rd, body.algorithmSuiteID);
    return Success(Definitions.Header(body, auth));
  }

  method Serialize(wr: Streams.StringWriter, header: Definitions.Header) returns (ret: Result<nat>)
    requires wr.Valid() && Validity.ValidHeader(header)
    modifies wr.Repr
    ensures wr.Valid()
  {
    var m :- S.SerializeHeaderBody(wr, header.body);
    var n :- S.SerializeHeaderAuthentication(wr, header.auth, header.body.algorithmSuiteID);
    return Success(m + n);
  }
}
