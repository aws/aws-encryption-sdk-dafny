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
  const VERSION_1: uint8     := 0x01
  type Version               = x | x == VERSION_1 witness VERSION_1

  const TYPE_CUSTOMER_AED: uint8 := 0x80
  type Type                  = x | x == TYPE_CUSTOMER_AED witness TYPE_CUSTOMER_AED

  const MESSAGE_ID_LEN       := 16
  type MessageID             = x: seq<uint8> | |x| == MESSAGE_ID_LEN witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

  type Reserved              = x: seq<uint8> | x == [0,0,0,0] witness [0,0,0,0]

  datatype ContentType       = NonFramed | Framed

  function method ContentTypeToUInt8(contentType: ContentType): uint8 {
    match contentType
    case NonFramed => 0x01
    case Framed => 0x02
  }

  function method UInt8ToContentType(x: uint8): Option<ContentType> {
    if x == 0x01 then
      Some(NonFramed)
    else if x == 0x02 then
      Some(Framed)
    else
      None
  }

  lemma ContentTypeConversionsCorrect(contentType: ContentType, x: uint8)
    ensures UInt8ToContentType(ContentTypeToUInt8(contentType)) == Some(contentType)
    ensures var opt := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.get) == x
  {
  }

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
