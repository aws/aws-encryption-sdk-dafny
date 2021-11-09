include "../../Util/UTF8.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module SerializableTypes {
  import opened UInt = StandardLibrary.UInt
  import opened UTF8
  import opened Aws.Crypto

  type ShortUTF8Seq = s: ValidUTF8Bytes | IsSeq16(s)

  predicate method IsESDKEncryptedDataKey(edk: EncryptedDataKey) {
    && IsSeq16(edk.keyProviderId)
    && IsSeq16(edk.keyProviderInfo)
    && IsSeq16(edk.ciphertext)
  }

  type ESDKEncryptedDataKey = e: EncryptedDataKey | IsESDKEncryptedDataKey(e) witness *
  type ESDKEncryptedDataKeys = seq16<ESDKEncryptedDataKey>

  predicate method IsESDKEncryptionContext(ec: EncryptionContext) {
    && |ec| > UINT16_LIMIT
    && forall element
    | element in (multiset(ec.Keys) + multiset(ec.Values))
    :: IsSeq16(element)
  }

  type ESDKEncryptionContext = ec: EncryptionContext | IsESDKEncryptionContext(ec) witness *

}
