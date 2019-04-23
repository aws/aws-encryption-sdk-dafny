include "StandardLibrary.dfy"
include "KeyringTrace.dfy"
include "ByteBuf.dfy"
include "EDK.dfy"
include "Cipher.dfy"

module Materials {
  import opened StandardLibrary
  import opened Aws
  import opened KeyringTraceModule
  import opened EDK
  import opened Cipher
  import opened ByteBuffer

  trait {:termination false} CMM {
    var refcount: nat
    method Destroy()
    // Generate is needed only for encryption
    method Generate(request: EncryptionRequest) returns (result: Outcome, materials: EncryptionMaterials)
      modifies request
      ensures fresh(materials)
      ensures fresh(materials.unencrypted_data_key) && materials.unencrypted_data_key.Length <= 32
    // Decrypt is needed only for decryption
    method Decrypt(request: DecryptionRequest) returns (result: Outcome, materials: DecryptionMaterials)
      ensures fresh(materials)

    // To be called by classes that implement a CMM
    static method BaseInit(cmm: CMM)
      modifies cmm
    {
      cmm.refcount := 1;
    }
    method Release()
      modifies this
      ensures refcount == old(refcount) == 0 || refcount == old(refcount) - 1
    {
      if refcount != 0 {
        refcount := refcount - 1;
        if refcount == 0 {
          // TODO: destroy
        }
      }
    }
    method Retain()
      modifies this
      ensures refcount == old(refcount) + 1
    {
      refcount := refcount + 1;
    }
  }

  trait {:termination false} Keyring {
    var refcount: nat
    method Destroy()
    method OnEncrypt(uedk: ByteBuf, keyring_trace: seq<KeyringTrace>, edk_list: seq<EncryptedDataKey>, enc_context: EncryptionContext,
     alg_id: AlgorithmID) returns (result: Outcome, uedk': ByteBuf, keyring_trace': seq<KeyringTrace>)
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_id.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_info.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].ciphertext.a
    method OnDecrypt(uedk: ByteBuf, keyring_trace: seq<KeyringTrace>, edk_list: seq<EncryptedDataKey>,enc_context: EncryptionContext,
     alg_id: AlgorithmID) returns (result: Outcome, uedk': ByteBuf, keyring_trace': seq<KeyringTrace>)

    // To be called by classes that implement a Keyring
    static method BaseInit(kr: Keyring)
      modifies kr
    {
      kr.refcount := 1;
    }
    method Release()
      modifies this
    {
      if refcount != 0 {
        refcount := refcount - 1;
        if refcount == 0 {
          // TODO: destroy
        }
      }
    }
    method Retain()
      modifies this
    {
      refcount := refcount + 1;
    }
  }

  class EncryptionRequest {
    var enc_context: EncryptionContext
    var requested_alg: AlgorithmID
    // upper bound on the plaintext size to be encrypted
    var plaintext_size: nat

    constructor (ctx: EncryptionContext, size: nat) {
      this.enc_context := ctx;
      this.plaintext_size := size;
    }
  }

  /**
  * Materials returned from a CMM generate_encryption_materials operation
  */
  class EncryptionMaterials {
    var unencrypted_data_key: array<byte>
    // Contains a trace of which wrapping keys took which actions in this request
    var keyring_trace: seq<KeyringTrace>  // in C version: struct aws_array_list
    var encrypted_data_keys: seq<EncryptedDataKey>
    // Trailing signature context, or NULL if no trailing signature is needed for this algorithm
    var signctx: SignCtx?
    var alg: AlgorithmID

    constructor (alg: AlgorithmID) {
      this.alg := alg;
    }
    method Destroy() {}
  }

  /**
  * Decryption request passed from session to CMM
  */
  class DecryptionRequest {
    const enc_context: EncryptionContext
    var encrypted_data_keys: seq<EncryptedDataKey>
    var requested_alg: AlgorithmID
  }

  /**
  * Decryption materials returned from CMM to session
  */
  class DecryptionMaterials {
    var unencrypted_data_key: array<byte>
    // Contains a trace of which wrapping keys took which actions in this request
    var keyring_trace: seq<KeyringTrace>  // in C version: struct aws_array_list
    // Trailing signature context, or NULL if no trailing signature is needed for this algorithm
    var signctx: SignCtx?
    var alg: AlgorithmID

    constructor (alg: AlgorithmID) {
      this.alg := alg;
    }
    method Destroy() {}
  }
}
