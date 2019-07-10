include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.Definitions {
    import AlgorithmSuite
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    type T_NonZero_uint16  = x: uint16 | x != 0 witness 1
    /*
    * Header body type definition
    */
    type T_Version         = x | x == 0x01 /*Version 1.0*/ witness 0x01
    type T_Type            = x | x == 0x80 /*Customer Authenticated Encrypted Data*/ witness 0x80
    type T_MessageID       = x: seq<uint8> | |x| == 16 witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    type T_Reserved        = x: seq<uint8> | x == [0,0,0,0] witness [0,0,0,0]
    datatype T_ContentType = NonFramed | Framed
    type EncCtx            = array<(array<uint8>, array<uint8>)>
    datatype T_AAD         = AAD(length: T_NonZero_uint16, kvPairs: EncCtx) | EmptyAAD

    datatype EDKEntry      = EDKEntry(keyProviderId: array<uint8>, keyProviderInfo: array<uint8>, encDataKey: array<uint8>)
    datatype T_EncryptedDataKeys
                           = EncryptedDataKeys(count: T_NonZero_uint16, entries: array<EDKEntry>)

    datatype HeaderBody    = HeaderBody(
                                version: T_Version,
                                typ: T_Type,
                                algorithmSuiteID: AlgorithmSuite.ID,
                                messageID: T_MessageID,
                                aad: T_AAD,
                                encryptedDataKeys: T_EncryptedDataKeys,
                                contentType: T_ContentType,
                                reserved: T_Reserved,
                                ivLength: uint8,
                                frameLength: uint32)

    /*
    * Header authentication type definition
    */
    
    datatype HeaderAuthentication = HeaderAuthentication(iv: array<uint8>, authenticationTag: array<uint8>)
}