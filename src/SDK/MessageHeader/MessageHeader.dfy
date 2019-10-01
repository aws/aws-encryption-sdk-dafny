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

  /*
   * Definition of the message header, i.e., the header body and the header authentication
   */
  class Header {
    var body: Option<Definitions.HeaderBody>
    var auth: Option<Definitions.HeaderAuthentication>

    constructor () {
      body, auth := None, None;
    }

    method Deserialize(is: Streams.StringReader)
      requires is.Valid()
      requires body.None? || auth.None?
      modifies is, `body, `auth
      ensures body.Some? && auth.Some? ==> Validity.ValidHeaderBody(body.get)
      ensures body.Some? && auth.Some? ==> Validity.ValidHeaderAuthentication(auth.get, body.get.algorithmSuiteID)
      // TODO: is this the right decision?
      ensures body.Some? <==> auth.Some?
      ensures body.None? <==> auth.None? // redundant
      ensures is.Valid()
    {
      var res := D.DeserializeHeaderBody(is);
      match res {
        case Success(body_) =>
          assert body_.algorithmSuiteID in AlgorithmSuite.Suite.Keys; // nfv
          var res := D.DeserializeHeaderAuthentication(is, body_.algorithmSuiteID);
          match res {
            case Success(auth_) =>
              body, auth := Some(body_), Some(auth_);
              assert Validity.ValidHeaderBody(body.get);
            case Failure(e) =>
              print "Could not deserialize message header: " + e + "\n";
              body, auth := None, None;
              return;
          }
        case Failure(e) =>
          print "Could not deserialize message header: " + e + "\n";
          body, auth := None, None;
          return;
      }
    }

    method Serialize(os: Streams.StringWriter) returns (ret: Result<nat>)
      requires os.Valid()
      requires body.Some?
      requires Validity.ValidHeaderBody(body.get)
      modifies os.Repr
      ensures os.Valid()
    {
      ret := S.SerializeHeaderBody(os, body.get);
    }
  }
}
