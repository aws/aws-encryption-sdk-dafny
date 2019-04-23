include "StandardLibrary.dfy"
include "KeyringTrace.dfy"
include "ByteBuf.dfy"
include "EDK.dfy"
include "Materials.dfy"
include "Cipher.dfy"

module RawRsaKeyring {
  import opened StandardLibrary
  import opened Aws
  import opened KeyringTraceModule
  import opened EDK
  import opened Materials
  import opened Cipher
  import opened ByteBuffer

 class RawRsaKeyring extends Keyring
 {
    var key_name: string 
    var key_namespace: string
    var rsa_private_key_pem: string 
    var rsa_public_key_pem: string 
    var rsa_padding_mode: RsaPaddingMode

    constructor New(key_name: string, key_namespace: string, rsa_private_key_pem: string, rsa_public_key_pem:string,
    rsa_padding_mode: RsaPaddingMode)
    requires |key_name| > 0
    requires |key_namespace| > 0 
    {
      this.key_name := key_name;
      this.key_namespace := key_namespace; 
      if (|rsa_private_key_pem| > 0) 
      {
          this.rsa_private_key_pem := rsa_private_key_pem;
      }
      else
      {
          this.rsa_public_key_pem := rsa_public_key_pem;
      }
      this.rsa_padding_mode := rsa_padding_mode;
    }

    method OnEncrypt(uedk: ByteBuf, keyring_trace: seq<KeyringTrace>, edk_list: seq<EncryptedDataKey>, 
    enc_context: EncryptionContext, alg_id: AlgorithmID) returns (result: Outcome, uedk': ByteBuf, 
    keyring_trace': seq<KeyringTrace>)
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_id.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_info.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].ciphertext.a
    {
       assert (|this.rsa_private_key_pem| > 0);
        var flags: bv32;
        var data_key_len: nat;
        var alg_props: AlgorithmProperties?;
        
        if (uedk.a.Length <= 0) {
          alg_props := AlgProperties(alg_id);
          if (alg_props != null) {
            data_key_len := alg_props.data_key_len;
          }
          else {
            result := AWS_OP_ERR;
          }
          //uedk'.a := new byte[data_key_len]; //Fix: Error: LHS of assignment must denote a mutable field
          result := GenRandom(uedk'.a);
          if (result == AWS_OP_ERR) {
            return AWS_OP_ERR, uedk', keyring_trace;
          }
          flags := AWS_CRYPTOSDK_WRAPPING_KEY_GENERATED_DATA_KEY;
        }
        else {
          uedk' := uedk;
        }
        
        result := RsaKeyringEncryptDataKey(uedk', edk_list);
        if (result == AWS_OP_ERR && flags == 0) 
        {
            ByteBufCleanUp(uedk');
        }
        if (result == AWS_OP_SUCCESS)
        {
            flags := AWS_CRYPTOSDK_WRAPPING_KEY_ENCRYPTED_DATA_KEY;
            result, keyring_trace' := keyring_trace_add_record(keyring_trace, this.key_namespace, this.key_name, flags);
        }
        return result, uedk', keyring_trace';
    }

    method OnDecrypt(uedk: ByteBuf, keyring_trace: seq<KeyringTrace>, edk_list: seq<EncryptedDataKey>,
    enc_context: EncryptionContext, alg_id: AlgorithmID) returns (result: Outcome, uedk': ByteBuf, keyring_trace': seq<KeyringTrace>)
    {
      assert(|this.rsa_public_key_pem| > 0);
      var num_edks := |edk_list|;
      var edk_idx := 0;
      var res: bool;
      while edk_idx < num_edks
        invariant 0 <= edk_idx
        decreases num_edks - edk_idx
        {
          var edk := edk_list[edk_idx];
          assert(edk.provider_id.len <= 0 || edk.provider_info.len <= 0 || edk.ciphertext.len <= 0);

          res := CompareStringtoBytebuf(this.key_namespace, edk.provider_id);
          if (res == false)
          {
            return AWS_OP_ERR, uedk, keyring_trace;
          }
          res := false;
          res := CompareStringtoBytebuf(this.key_name, edk.provider_info);
          if (res == false)
          {
            return AWS_OP_ERR, uedk, keyring_trace;
          }
          
          result, uedk' := RsaDecrypt(ByteCursorFromBuf(edk.ciphertext), rsa_private_key_pem, 
          this.rsa_padding_mode);
          if (result == AWS_OP_SUCCESS){
            /* We are here either because of a ciphertext mismatch
             * or because of an OpenSSL error. In either case, nothing
             * better to do than just moving on to next EDK, so clear the error code.
             */
          }
          else {
            result, keyring_trace' := keyring_trace_add_record(keyring_trace, this.key_namespace, this.key_name, 
            AWS_CRYPTOSDK_WRAPPING_KEY_DECRYPTED_DATA_KEY);
            return result, uedk', keyring_trace';
          }
          edk_idx := edk_idx + 1;
        }
         return result, uedk', keyring_trace';
    }

    method Destroy() {} //TODO

    method RsaKeyringEncryptDataKey(uedk: ByteBuf, edk_list: seq<EncryptedDataKey>) returns (result: Outcome) //TODO
    requires |this.rsa_private_key_pem| > 0; 
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_id.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].provider_info.a
    modifies set i | 0 <= i < |edk_list| :: edk_list[i].ciphertext.a
    {
    }

    static method CompareStringtoBytebuf(s: string, bb: ByteBuf) returns (result: bool) //TODO
    {
    }
 
 }

}