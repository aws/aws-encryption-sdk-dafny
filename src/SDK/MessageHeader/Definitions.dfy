include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"

module MessageHeader.Definitions {
  import AlgorithmSuite
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials

  /*
   * Definition of the message header, i.e., the header body and the header authentication
   */
  datatype Header = Header(body: HeaderBody, auth: HeaderAuthentication)

  /*
   * Header body type definition
   */
  type Version               = x | x == 0x01 /*Version 1.0*/ witness 0x01
  type Type                  = x | x == 0x80 /*Customer Authenticated Encrypted Data*/ witness 0x80
  const MESSAGE_ID_LEN       := 16
  type MessageID             = x: seq<uint8> | |x| == MESSAGE_ID_LEN witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  type Reserved              = x: seq<uint8> | x == [0,0,0,0] witness [0,0,0,0]
  datatype ContentType       = NonFramed | Framed

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Materials.EncryptedDataKey>)

  datatype HeaderBody        = HeaderBody(
                                 version: Version,
                                 typ: Type,
                                 algorithmSuiteID: AlgorithmSuite.ID,
                                 messageID: MessageID,
                                 aad: Materials.EncryptionContext,
                                 encryptedDataKeys: EncryptedDataKeys,
                                 contentType: ContentType,
                                 reserved: Reserved,
                                 ivLength: uint8,
                                 frameLength: uint32)

  /*
   * Header authentication type definition
   */
  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)
}
