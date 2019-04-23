include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "ByteBuf.dfy"

module EDK {
  import opened StandardLibrary
  import opened Aws
  import opened ByteBuffer

  /*
  * This public interface to the encrypted data key (EDK) objects is provided for
  * developers of CMMs and keyrings only. If you are a user of the AWS Encryption
  * SDK and you are not developing your own CMMs and/or keyrings, you do not
  * need to use it and you should not do so.
  */

  class EncryptedDataKey {
    var provider_id: ByteBuf
    var provider_info: ByteBuf
    var ciphertext: ByteBuf


    constructor New(provider_id: ByteBuf, provider_info: ByteBuf, ciphertext: ByteBuf)
    {
      this.provider_id := provider_id;
      this.provider_info := provider_info; 
      this.ciphertext := ciphertext;
    }
    
    /**
     * Setting all bytes of an EDK to zero when you declare it will make this safe to call even if some buffers are unused.
     */
    method EdkClear()
    requires GoodByteBuf(this.provider_id) && GoodByteBuf(this.provider_info) && GoodByteBuf(this.ciphertext)
    modifies this.provider_id.a, this.provider_info.a, this.ciphertext.a
    {
      ByteBufClear(this.provider_id);
      ByteBufClear(this.provider_info);
      ByteBufClear(this.ciphertext);
    }
  }

  predicate GoodEDKList(edk_list: seq<EncryptedDataKey>)
  reads edk_list
  {
    var num_keys := |edk_list|;
    forall k :: 0 <= k < num_keys ==> GoodByteBuf(edk_list[k].provider_id) && GoodByteBuf(edk_list[k].provider_info) && 
    GoodByteBuf(edk_list[k].ciphertext)
  }
  /**
   * Clears all the EDKs in the list.
   */
  method EdkListClear(edk_list: seq<EncryptedDataKey>)
  requires GoodEDKList(edk_list)
  modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_id.a
  modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_info.a
  modifies set i | 0 <= i < |edk_list| :: edk_list[i].ciphertext.a
  {
    var num_keys := |edk_list|;
    var key_idx := 0;
    while key_idx < num_keys
          invariant 0 <= key_idx
          decreases num_keys - key_idx
          
    {
      edk_list[key_idx].EdkClear();
      key_idx := key_idx + 1; 
    }
}

  /**
   * Copies the EDK data in src to dest.
   */
   method EdkClone(dest: EncryptedDataKey, src: EncryptedDataKey)
   requires GoodByteBuf(dest.provider_id) && GoodByteBuf(dest.provider_info) && GoodByteBuf(dest.ciphertext)
   requires GoodByteBuf(src.provider_id) && GoodByteBuf(src.provider_info) && GoodByteBuf(src.ciphertext)
   requires dest.provider_id.len <= src.provider_id.len
   requires dest.provider_info.len <= src.provider_info.len
   requires dest.ciphertext.len <= src.ciphertext.len
   modifies dest.provider_id.a, dest.provider_info.a, dest.ciphertext.a 
   {
     ByteBufCopyFromByteBuf(dest.provider_id, src.provider_id);
     ByteBufCopyFromByteBuf(dest.provider_info, src.provider_info);
     ByteBufCopyFromByteBuf(dest.ciphertext, src.ciphertext);
   }

  // Upon successful parsing, "edk" as non-null and "cur'" has been advanced.
  // Otherwise, returns "edk" as null and "cur' == cur".
  method Parse(cur: ByteCursor) returns (edk: EncryptedDataKey?, cur': ByteCursor)
    requires GoodByteCursor(cur)
    ensures edk != null ==> ByteCursorAdvances(cur, cur')
    ensures edk == null ==> cur == cur'
}
