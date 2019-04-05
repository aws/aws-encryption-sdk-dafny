include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "Materials.dfy"
include "Cipher.dfy"

module Session {
  import opened StandardLibrary
  import opened Aws
  import opened Materials
  import opened Cipher

  // Encryption SDK mode
  datatype ProcessingMode = EncryptMode /* 0x9000 */ | DecryptMode /* 0x9001 */

  // Encryption SDK session
  datatype SessionState =
    /*** Common states ***/
    | Config          // Initial configuration. No data has been supplied
    | Error(Outcome)  // De/encryption failure. No data will be processed until reset
    | Done
    /*** Decrypt path ***/
    | ReadHeader
    | UnwrapKey
    | DecryptBody
    | CheckTrailer
    /*** Encrypt path ***/
    | GenKey
    | WriteHeader
    | EncryptBody
    | WriterTrailer

  class content_key { }  // TODO


  class Session {
    const mode: ProcessingMode
    ghost var input_consumed: nat
    ghost var message_size: Option<nat>

    var state: SessionState
    const cmm: CryptoMaterialsManager

    /* Encrypt mode configuration */
    var precise_size: Option<nat> /* Exact size of message */
    var size_bound: nat   /* Maximum message size */
    var data_so_far: nat  /* Bytes processed thus far */

    /* The actual header, if parsed */
    var head_copy: array?<byte>
    var header_size: nat
    var header: Header
    const frame_size := 256 * 1024 /* Frame size, zero for unframed */

    /* List of (struct aws_cryptosdk_keyring_trace_record)s */
    var keyring_trace: seq<keyring_trace_record>

    /* Estimate for the amount of input data needed to make progress. */
    var input_size_estimate: nat

    /* Estimate for the amount of output buffer needed to make progress. */
    var output_size_estimate: nat

    var frame_seqno: nat

    var alg_props: aws_cryptosdk_alg_properties?

    /* Decrypted, derived (if applicable) content key */
    var content_key: content_key?

    /* In-progress trailing signature context (if applicable) */
    var signctx: aws_cryptosdk_signctx?

    /* Set to true after successful call to CMM to indicate availability
     * of keyring trace and--in the case of decryption--the encryption context.
     */
    var cmm_success: bool

    predicate Valid()
      reads this
    {
      (mode == EncryptMode || message_size == None) &&
      (state == Config ==>
        true) &&
      (state.Error? ==> state != Error(SUCCESS))
    }

    constructor FromCMM(mode: ProcessingMode, cmm: CryptoMaterialsManager)
      ensures Valid()
      ensures this.mode == mode && this.input_consumed == 0 && this.message_size == None
    {
      this.mode := mode;
      this.cmm := cmm;
      this.header := new Header();
      new;
      Reset();
      this.state := Config;
      cmm.Retain();
    }

    method Reset()
      modifies this
      ensures state == Config
      ensures Valid()
      ensures input_consumed == 0 && message_size == None
    {
      this.input_consumed, this.message_size := 0, None;
      this.state := Config;
      this.precise_size := None;
      this.size_bound := UINT64_MAX;
      this.data_so_far := 0;
      this.cmm_success := false;
      this.head_copy := null;
      this.header_size := 0;
      this.header := new Header();
      this.keyring_trace := [];
      this.input_size_estimate := 1;
      this.output_size_estimate := 1;
      this.frame_seqno := 0;
      this.alg_props := null;
      this.signctx := null;
    }

    method SetMessageSize(message_size: nat) returns (r: Outcome)
      requires Valid() && mode == EncryptMode && this.message_size == None
      requires message_size <= size_bound
      modifies this
      ensures Valid() && input_consumed == old(input_consumed)
      ensures r == SUCCESS ==> this.message_size == Some(message_size)
    {
      this.message_size := Some(message_size);
      if this.state == EncryptBody {
        priv_encrypt_compute_body_estimate();
      }
      return SUCCESS;
    }

    method Process(outp: array<byte>, outlen: nat, inp: array<byte>, inlen: nat) returns (result: Outcome, out_bytes_written: nat, in_bytes_read: nat)
      requires Valid()
      requires outp != inp && inlen <= inp.Length && outlen <= outp.Length
      modifies this, outp
      ensures Valid() && message_size == old(message_size)
      ensures in_bytes_read <= inlen && out_bytes_written <= outlen
      ensures result != SUCCESS ==>
                input_consumed == old(input_consumed) &&
                forall i :: 0 <= i < outlen ==> outp[i] == 0
      ensures result == SUCCESS ==>
                input_consumed == old(input_consumed) + in_bytes_read &&
                in_bytes_read == inlen
      ensures result == SUCCESS && mode == EncryptMode ==>
                outp[..out_bytes_written] == Math.Encrypt(inp[..in_bytes_read])
      ensures result == SUCCESS && mode == DecryptMode ==>
                outp[..out_bytes_written] == Math.Decrypt(inp[..in_bytes_read])
    {
      var output := byte_buf(0, outp, 0, outlen);
      var input := byte_cursor(inlen, inp, 0);

      while true
        invariant Valid()
        invariant output.len <= outlen && input.ptr <= inlen
        invariant output.len <= output.capacity
        decreases outlen - output.len, inlen - input.ptr, if state == Config then 1 else 0
      {
        var prior_state, old_inp := state, input.ptr;

        var remaining_space := byte_buf_from_empty_array(output.enclosing_buffer, output.buffer_start_offset + output.len, output.capacity - output.len);

        match state {
          case Config =>
            state := if mode == EncryptMode then GenKey else ReadHeader;
            result := SUCCESS;
          case Done =>
            result := SUCCESS;
          case Error(err) =>
            result := err;
          /*** Decrypt path ***/
          case ReadHeader =>  // TODO
          case UnwrapKey =>  // TODO
          case DecryptBody =>  // TODO
          case CheckTrailer =>  // TODO
          /*** Encrypt path ***/
          case GenKey =>
            result := priv_try_gen_key();
          case WriteHeader =>
            result := priv_try_write_header(remaining_space);
          case EncryptBody =>
            result := priv_try_encrypt_body(remaining_space, input);
          case WriterTrailer =>
            result := priv_write_trailer(remaining_space);
        }
        var made_progress := remaining_space.len != 0 || input.ptr != old_inp || prior_state != state;

        output := output.(len := output.len + remaining_space.len);
        if result != SUCCESS || !made_progress {
          break;
        }
      }

      out_bytes_written, in_bytes_read := output.len, input.ptr;

      if result != SUCCESS {
        state := Error(result);
        forall i | 0 <= i < outlen {
          outp[i] := 0;
        }
        out_bytes_written := 0;
      }
    }

    predicate method IsDone()
      requires Valid()
      reads this
      ensures mode == EncryptMode && Some(input_consumed) == message_size ==> IsDone()
      ensures mode == DecryptMode ==> IsDone()
    {
      true
    }

    method Destroy()
      requires Valid()
      modifies this
    {
      cmm.Release();
    }

    method priv_try_gen_key() returns (result: Outcome)
      modifies `alg_props, `signctx, `cmm_success
    {
      result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;

      label tryit: {
        // The default CMM will fill this in.
        var request := new aws_cryptosdk_encryption_request(header.enc_context, precise_size);

        var r, materials := cmm.generate_encryption_materials(request);
        if r != 0 {
          result := AWS_OP_ERR;
          break tryit;
        }

        // Perform basic validation of the materials generated
        alg_props := aws_cryptosdk_alg_props(materials.alg);

        // assert session->alg_props != null;
        // assert materials->unencrypted_data_key.len == session->alg_props->data_key_len;
        // assert aws_array_list_length(&materials->encrypted_data_keys) != 0;
        // We should have a signature context iff this is a signed alg suite
        // assert session->alg_props->signature_len == 0 <==> materials->signctx == null;

        // Move ownership of the signature context before we go any further.
        signctx, materials.signctx := materials.signctx, null;

/*****
        // TODO - eliminate the data_key type
      //struct data_key data_key;
///        memcpy(&data_key, materials->unencrypted_data_key.buffer, materials->unencrypted_data_key.len);

///        aws_cryptosdk_transfer_list(&session->keyring_trace, &materials->keyring_trace);
        cmm_success := true;

        // Generate message ID and derive the content key from the data key.
        if (aws_cryptosdk_genrandom(session->header.message_id, sizeof(session->header.message_id))) {
          result := AWS_OP_ERR;
          break tryit;
        }

        if (aws_cryptosdk_derive_key(session->alg_props, &session->content_key, &data_key, session->header.message_id)) {
          result := AWS_OP_ERR;
          break tryit;
        }

        if (build_header(session, materials)) {
          result := AWS_OP_ERR;
          break tryit;
        }

        if (sign_header(session)) {
          result := AWS_OP_ERR;
          break tryit;
        }
*****/

        result := AWS_ERROR_SUCCESS;
      }

      if materials != null {
///          aws_byte_buf_secure_zero(&materials->unencrypted_data_key);
          aws_cryptosdk_encryption_materials_destroy(materials);
      }

///      aws_secure_zero(&data_key, sizeof(data_key));

      return result;
    }
    method priv_encrypt_compute_body_estimate() {
      // TODO
    }
    method priv_try_write_header(remaining_space: byte_buf) returns (result: Outcome) {
      // TODO
    }
    method priv_try_encrypt_body(remaining_space: byte_buf, input: byte_cursor) returns (result: Outcome) {
      // TODO
    }
    method priv_write_trailer(remaining_space: byte_buf) returns (result: Outcome) {
      // TODO
    }
  }

  class Header {
    constructor ()  // aws_cryptosdk_hdr_init
  }
}
