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

  method Deserialize(is: Streams.StringReader) returns (res: Result<Definitions.Header>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match res
      case Success(header) => Validity.ValidHeader(header)
      case Failure(_) => true
  {
    var body :- D.DeserializeHeaderBody(is);
    var auth :- D.DeserializeHeaderAuthentication(is, body.algorithmSuiteID);
    return Success(Definitions.Header(body, auth));
  }

  method Serialize(os: Streams.StringWriter, header: Definitions.Header) returns (ret: Result<nat>)
    requires os.Valid() && Validity.ValidHeader(header)
    modifies os.Repr
    ensures os.Valid()
  {
    var m :- S.SerializeHeaderBody(os, header.body);
    var n :- S.SerializeHeaderAuthentication(os, header.auth, header.body.algorithmSuiteID);
    return Success(m + n);
  }
}
