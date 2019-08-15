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
            ensures body.Some? && auth.Some? ==> Validity.ValidHeaderBody(body.get)
            ensures body.Some? && auth.Some? ==> Validity.ValidHeaderAuthentication(auth.get, body.get.algorithmSuiteID)
            // TODO: is this the right decision?
            ensures body.Some? <==> auth.Some?
            ensures body.None? <==> auth.None? // redundant
            ensures is.Valid()
        {
            {
                var res := Deserialize.headerBody(is);
                match res {
                    case Left(body_) =>
                        // How does Dafny know the following assertion holds with Validity.ValidHeaderBody being opaque?
                        assert body_.algorithmSuiteID in AlgorithmSuite.Suite.Keys; // nfv
                        var res := Deserialize.headerAuthentication(is, body_);
                        match res {
                            case Left(auth_) =>
                                body := Some(body_);
                                auth := Some(auth_);
                                reveal Validity.ReprAAD();
                                assert Validity.ValidHeaderBody(body.get);
                            case Right(e)    => {
                                print "Could not deserialize message header: " + e.msg + "\n";
                                body := None;
                                auth := None;
                                return;
                            }
                        }
                    case Right(e)    => {
                        print "Could not deserialize message header: " + e.msg + "\n";
                        body := None;
                        auth := None;
                        return;
                    }
                }
            }
        }

        method serializeHeader(os: StringWriter) returns (ret: Either<nat, Error>)
            requires os.Valid()
            requires body.Some?
            requires os.Repr !! Validity.ReprAAD(body.get.aad)
            requires os.Repr !! Validity.ReprEncryptedDataKeys(body.get.encryptedDataKeys)
            requires Validity.ReprAAD(body.get.aad) !! Validity.ReprEncryptedDataKeys(body.get.encryptedDataKeys)
            requires Validity.ValidHeaderBody(body.get)
            modifies os.Repr
            ensures os.Valid()
        {
            ret := Serialize.headerBody(os, body.get);
        }
    }
}