include "Definitions.dfy"
include "Deserialize.dfy"
include "Serialize.dfy"
include "Validity.dfy"

include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader {
    // only uses Result<T, Error> from StandardLibrary
    // TODO: refactor StandardLibrary into smaller modules
    import opened StandardLibrary
    import opened Streams
    /*
     * Definition of the message header, i.e., the header body and the header authentication
     */
    class Header {
        var body: Option<Definitions.HeaderBody>
        var auth: Option<Definitions.HeaderAuthentication>

        constructor () {
            body := None;
            auth := None;
        }
        method deserializeHeader(is: StringReader)
            requires is.Valid()
            modifies is, `body, `auth
            requires body.None? || auth.None?
            ensures body.Some? ==> Validity.ValidHeaderBody(body.get)
            ensures body.Some? && auth.Some? ==> Validity.ValidHeaderAuthentication(auth.get, body.get.algorithmSuiteID)
            // TODO: is this the right decision?
            ensures body.Some? <==> auth.Some?
            ensures body.None? <==> auth.None? // redundant
            ensures is.Valid()
        {
            assume false;
            {
                var res := Deserialize.headerBody(is);
                match res {
                    case Left(body_) => body := Some(body_);
                    case Right(e)    => {
                        print "Could not deserialize message header: " + e.msg + "\n";
                        body := None;
                        auth := None;
                        return;
                    }
                }
            }
            // TODO: We need to prove freshness or non-aliasing somehow?
            // Works when we add this assumption:
            //assume fresh(Validity.ReprAAD(body.get.aad))
            //       && fresh(Validity.ReprEncryptedDataKeys(body.get.encryptedDataKeys));

            {
                var res := Deserialize.headerAuthentication(is, body.get);
                match res {
                    case Left(auth_) => auth := Some(auth_);
                    case Right(e)    => {
                        print "Could not deserialize message header: " + e.msg + "\n";
                        body := None;
                        auth := None;
                        return;
                    }
                }
            }
            //assume fresh(Validity.ReprAAD(body.get.aad))
            //       && fresh(Validity.ReprEncryptedDataKeys(body.get.encryptedDataKeys));
        }

        method serializeHeader(os: StringWriter) returns (ret: Result<nat>)
            requires os.Valid()
            requires body.Some?
            requires os.Repr !! Validity.ReprAAD(body.get.aad)
            requires os.Repr !! Validity.ReprEncryptedDataKeys(body.get.encryptedDataKeys)
            requires Validity.ValidHeaderBody(body.get)
            modifies os.Repr
            ensures os.Valid()
        {
            ret := Serialize.headerBody(os, body.get);
        }
    }
}