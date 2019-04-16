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
     * Deallocates all memory associated with an EDK. Setting all bytes of an EDK to
     * zero when you declare it will make this safe to call even if some buffers are unused.
     */
    method EdkCleanUp(edk: EncryptedDataKey) {}
  }
  /**
   * Allocates an empty list of EDKs.
   */
  method NewEdkList() returns (edk_list: seq<array>) {}

  /**
   * Deallocates all memory associated with all EDKs in the list and then deallocates the list.
   */
  method EdkListCleanUp(edk_list: seq<array>) returns (r: Outcome) {}

  /**
   * Deallocates all memory associated with all EDKs in the list and then clears the list.
   * The array list itself remains allocated but empty.
   */
  method EdkListClear(edk_list: seq<array>) returns (r: Outcome) {}

  /**
   * Copies the EDK data in src to dest.
   */
   method EdkClone(dst: EncryptedDataKey, src: EncryptedDataKey) returns (r: Outcome) modifies dst {}

  /**
  * Returns true if the contents of all EDK byte buffers are identical, false otherwise.
  */
  method EdkEq(edk1: EncryptedDataKey, edk2: EncryptedDataKey) returns (result: bool) {}

}
