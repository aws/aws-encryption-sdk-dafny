include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "Materials.dfy"
include "Cipher.dfy"
include "ByteBuf.dfy"
include "Frame.dfy"

module Session {
  import opened StandardLibrary
  import opened Aws
  import opened Materials
  import EDK
  import Cipher
  import opened ByteBuffer
  import opened KeyringTraceModule
  import opened FrameFormat

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
    | WriteTrailer


  class Session {
    const mode: ProcessingMode
    ghost var input_consumed: nat
    ghost var message_size: Option<nat>

    var state: SessionState
    const cmm: CMM

    /* Encrypt mode configuration */
    var precise_size: Option<nat> /* Exact size of message */
    var size_bound: nat   /* Maximum message size */
    var data_so_far: nat  /* Bytes processed thus far */

    /* The actual header, if parsed */
    var header_copy: array?<byte>
    var header_size: nat
    var header: Header
    const frame_size := 256 * 1024 /* Frame size, zero for unframed */

    /* List of (struct aws_cryptosdk_keyring_trace_record)s */
    var keyring_trace: seq<KeyringTrace>

    /* Estimate for the amount of input data needed to make progress. */
    var input_size_estimate: nat

    /* Estimate for the amount of output buffer needed to make progress. */
    var output_size_estimate: nat

    var frame_seqno: nat

    var alg_props: Cipher.AlgorithmProperties?

    /* Decrypted, derived (if applicable) content key */
    var content_key: Cipher.content_key?

    /* In-progress trailing signature context (if applicable) */
    var signctx: Cipher.SignCtx?

    /* Set to true after successful call to CMM to indicate availability
     * of keyring trace and--in the case of decryption--the encryption context.
     */
    var cmm_success: bool

    predicate Valid()
      reads this
    {
      (mode == EncryptMode || message_size == None) &&
      match state
      case Config =>
        data_so_far == 0
      case Error(r) => r != AWS_OP_SUCCESS
      case Done => true
      case ReadHeader => true
      case UnwrapKey => true
      case DecryptBody => true
      case CheckTrailer => true
      case GenKey => true
      case WriteHeader => true
      case EncryptBody => true
      case WriteTrailer => true
    }

    constructor FromCMM(mode: ProcessingMode, cmm: CMM)
      modifies cmm
      ensures Valid()
      ensures this.mode == mode && this.input_consumed == 0 && this.message_size == None
      ensures cmm.refcount == old(cmm.refcount) + 1
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
      this.header_copy := null;
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
      ensures r == AWS_OP_SUCCESS ==> this.message_size == Some(message_size)
    {
      this.message_size := Some(message_size);
      if this.state == EncryptBody {
        priv_encrypt_compute_body_estimate();
      }
      return AWS_OP_SUCCESS;
    }

    // Note: ProcessEncrypt is a specialization of the Process method, for the purpose of testing the specifications of some of
    // the worker methods it calls. It only calls a worker routine once, rather than repeatedly calling them, as would be needed
    // in general. When the specification testing is completed, ProcessEncrypt will be deleted from the sources and replaced by the
    // more general Process method.
    method ProcessEncrypt(outp: array<byte>, outlen: nat, inp: array<byte>, inlen: nat) returns (result: Outcome, out_bytes_written: nat, in_bytes_read: nat)
      requires Valid() && mode == EncryptMode
      requires state == Config
      requires outp != inp && inlen <= inp.Length && outlen <= outp.Length
      modifies this, header, outp
      modifies header, header.iv.a, header.auth_tag.a, header.message_id
      /**
      ensures Valid() && message_size == old(message_size)
      ensures in_bytes_read <= inlen && out_bytes_written <= outlen
      ensures result != AWS_OP_SUCCESS ==>
                input_consumed == old(input_consumed) &&
                forall i :: 0 <= i < outlen ==> outp[i] == 0
      ensures result == AWS_OP_SUCCESS ==> state == Done
      ensures result == AWS_OP_SUCCESS ==>
                input_consumed == old(input_consumed) + in_bytes_read &&
                in_bytes_read == inlen
      ensures result == AWS_OP_SUCCESS && mode == EncryptMode ==>
                outp[..out_bytes_written] == Math.Encrypt(inp[..in_bytes_read])
      ensures result == AWS_OP_SUCCESS && mode == DecryptMode ==>
                outp[..out_bytes_written] == Math.Decrypt(inp[..in_bytes_read])
      **/
    {
      var output := ByteBufFromArray(outp, outlen);
      var input := ByteCursorFromArray(inp, inlen);

      label tryit: {
        // ----- Config
        assert state == Config;
        var remaining_space := ByteBufFromRemaining(output);
        state := GenKey;

        // ----- GenKey
        assert state == GenKey;
        result := priv_try_gen_key();
        if result != AWS_OP_SUCCESS { break tryit; }

        // ----- WriteHeader
        assert state == WriteHeader;
        output := priv_try_write_header(output);
        if state != EncryptBody { result := AWS_OP_ERR; break tryit; }

        // ----- EncryptBody
        assert state == EncryptBody;
        assert header == old(header);
        result, output, input := priv_try_encrypt_body(output, input);
        if result != AWS_OP_SUCCESS { break tryit; }
        if state != WriteTrailer { result := AWS_OP_ERR; break tryit; }

        // ----- WriteTrailer
        assert state == WriteTrailer;
        assert output.a == outp;  // DEBUG
        result, output := priv_write_trailer(output);
        if result != AWS_OP_SUCCESS { break tryit; }
        if state != Done { result := AWS_OP_ERR; break tryit; }

        // ----- Done
        assert state == Done;
      }
      assert result == AWS_OP_SUCCESS ==> state == Done;

      out_bytes_written, in_bytes_read := output.len, input.len;

      if result != AWS_OP_SUCCESS {
        state := Error(result);
        forall i | 0 <= i < outlen {
          outp[i] := 0;
        }
        out_bytes_written := 0;
      }
    }

    /*****
    method Process(outp: array<byte>, outlen: nat, inp: array<byte>, inlen: nat) returns (result: Outcome, out_bytes_written: nat, in_bytes_read: nat)
      requires Valid()
      requires outp != inp && inlen <= inp.Length && outlen <= outp.Length
      modifies this, outp
      ensures Valid() && message_size == old(message_size)
      ensures in_bytes_read <= inlen && out_bytes_written <= outlen
      ensures result != AWS_OP_SUCCESS ==>
                input_consumed == old(input_consumed) &&
                forall i :: 0 <= i < outlen ==> outp[i] == 0
      ensures result == AWS_OP_SUCCESS ==>
                input_consumed == old(input_consumed) + in_bytes_read &&
                in_bytes_read == inlen
      ensures result == AWS_OP_SUCCESS && mode == EncryptMode ==>
                outp[..out_bytes_written] == Math.Encrypt(inp[..in_bytes_read])
      ensures result == AWS_OP_SUCCESS && mode == DecryptMode ==>
                outp[..out_bytes_written] == Math.Decrypt(inp[..in_bytes_read])
    {
      var output := ByteBuf(0, outp, 0, outlen);
      var input := ByteCursor(inlen, inp, 0);

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
            result := AWS_OP_SUCCESS;
          case Done =>
            result := AWS_OP_SUCCESS;
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
            remaining_space := priv_try_write_header(remaining_space);
            result := AWS_OP_SUCCESS;
          case EncryptBody =>
            result := priv_try_encrypt_body(remaining_space, input);
          case WriterTrailer =>
            result := priv_write_trailer(remaining_space);
        }
        var made_progress := remaining_space.len != 0 || input.ptr != old_inp || prior_state != state;

        output := output.(len := output.len + remaining_space.len);
        if result != AWS_OP_SUCCESS || !made_progress {
          break;
        }
      }

      out_bytes_written, in_bytes_read := output.len, input.ptr;

      if result != AWS_OP_SUCCESS {
        state := Error(result);
        forall i | 0 <= i < outlen {
          outp[i] := 0;
        }
        out_bytes_written := 0;
      }
    }
    *****/

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
      modifies this, cmm
    {
      cmm.Release();
    }

    method priv_try_gen_key() returns (result: Outcome)
      requires Valid() && state == GenKey
      modifies this
      modifies header.iv.a, header.auth_tag.a
      modifies header, header.message_id
      ensures Valid()
      ensures unchanged(`data_so_far, `header)
      ensures result == AWS_OP_SUCCESS ==> state == WriteHeader
      ensures result == AWS_OP_SUCCESS ==>
        alg_props != null && content_key != null &&
        (alg_props.signature_len != 0 ==> signctx != null) &&
        header_copy != null && header_size <= header_copy.Length
    {
      var materials, data_key := null, null;
      label tryit: {
        // The default CMM will fill this in.
        var request := new EncryptionRequest(header.enc_context, if precise_size == None then UINT64_MAX else precise_size.get);

        result, materials := cmm.Generate(request);
        if result != AWS_OP_SUCCESS {
          result := AWS_OP_ERR;
          break tryit;
        }

        // Perform basic validation of the materials generated
        alg_props := Cipher.AlgProperties(materials.alg);
        if alg_props == null {
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
          break tryit;
        }
        if materials.unencrypted_data_key.Length != alg_props.data_key_len {
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
          break tryit;
        }
        if |materials.encrypted_data_keys| == 0 {
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
          break tryit;
        }
        // We should have a signature context iff this is a signed alg suite
        if !(alg_props.signature_len == 0 <==> materials.signctx == null) {
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
          break tryit;
        }

        // Move ownership of the signature context before we go any further.
        signctx, materials.signctx := materials.signctx, null;

        data_key := new byte[32];
        forall i | 0 <= i < materials.unencrypted_data_key.Length {
          data_key[i] := materials.unencrypted_data_key[i];
        }

        keyring_trace := materials.keyring_trace;
        cmm_success := true;

        // Generate message ID and derive the content key from the data key.
        result := Cipher.GenRandom(header.message_id);
        if result != AWS_OP_SUCCESS {
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
          break tryit;
        }

        result, content_key := Cipher.DeriveKey(alg_props, data_key, header.message_id);
        if result != AWS_OP_SUCCESS {
          result := AWS_OP_ERR;
          break tryit;
        }

        result := build_header(materials);
        if result != AWS_OP_SUCCESS {
          result := AWS_OP_ERR;
          break tryit;
        }

        result := sign_header();
        if result != AWS_OP_SUCCESS {
          result := AWS_OP_ERR;
          break tryit;
        }

        result := AWS_OP_SUCCESS;
      }

      // Clean up
      if materials != null {
        forall i | 0 <= i < materials.unencrypted_data_key.Length {
          materials.unencrypted_data_key[i] := 0;
        }
        materials.Destroy();
      }
      if data_key != null {
        forall i | 0 <= i < data_key.Length {
          data_key[i] := 0;
        }
      }

      return result;
    }

    method build_header(materials: EncryptionMaterials) returns (r: Outcome)
      requires alg_props != null
      modifies header, materials
      ensures materials.unencrypted_data_key == old(materials.unencrypted_data_key)
      ensures GoodByteBuf(header.iv) && GoodByteBuf(header.auth_tag)
      ensures fresh(header.iv.a) && fresh(header.auth_tag.a)
      ensures header.iv.len == alg_props.iv_len && header.auth_tag.len == alg_props.tag_len
    {
      header.alg_id := alg_props.alg_id;
      if UINT32_MAX < frame_size {
        return AWS_CRYPTOSDK_ERR_LIMIT_EXCEEDED;
      }
      header.frame_len := frame_size;

      // Swap the materials' EDK list for the header's.
      // When we clean up the materials structure we'll destroy the old EDK list.

      header.edk_list, materials.encrypted_data_keys := materials.encrypted_data_keys, header.edk_list;

      // The header should have been cleared earlier, so the materials structure should have
      // zero EDKs (otherwise we'd need to destroy the old EDKs as well).
      // TODO: check the property mentioned above, but not exactly like this:  assert |materials.encrypted_data_keys| == 0;

      header.iv := ByteBufInit_Full_AllZero(alg_props.iv_len);
      header.auth_tag := ByteBufInit_Full(alg_props.tag_len);

      return AWS_OP_SUCCESS;
    }

    method sign_header() returns (r: Outcome)
      requires alg_props != null && content_key != null
      requires GoodByteBuf(header.iv) && GoodByteBuf(header.auth_tag)
      requires header.iv.len == alg_props.iv_len && header.auth_tag.len == alg_props.tag_len
      modifies `header_size, `header_copy, `frame_seqno, `state
      modifies header.iv.a, header.auth_tag.a
      ensures state == if r == AWS_OP_SUCCESS then WriteHeader else old(state)
      ensures header_copy != null && header_copy.Length == header_size
    {
      header_size := header.size();
      header_copy := new byte[header_size];
      
      // Debug memsets - if something goes wrong below this makes it easier to
      // see what happened. It also makes sure that the header is fully initialized,
      // again just in case some bug doesn't overwrite them properly.
      ByteBufFill(header.iv, 0x42);
      ByteBufFill(header.auth_tag, 0xDE);

      assert header_copy.Length == header_size;
      var actual_size;
      r, actual_size := header.write(header_copy);
      if r != AWS_OP_SUCCESS {
        return AWS_OP_ERR;
      } else if actual_size != header_size {
        return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
      }

      var authtag_len := alg_props.iv_len + alg_props.tag_len;
      var to_sign := ByteBufFromArray(header_copy, header_size - authtag_len);
      var authtag := ByteBuf(header_copy, header_size - authtag_len, header_size, authtag_len);

      r := alg_props.SignHeader(content_key, authtag, to_sign);
      if r != AWS_OP_SUCCESS {
        return AWS_OP_ERR;
      }

      ByteBufCopyFromByteBuf(header.iv, authtag);
      ByteBufCopyFromByteBufOffset(header.auth_tag, authtag, header.iv.len);

      // Re-serialize the header now that we know the auth tag
      assert header_copy.Length == header_size;
      r, actual_size := header.write(header_copy);
      if r != AWS_OP_SUCCESS {
        return AWS_OP_ERR;
      } else if actual_size != header_size {
        return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
      }

      if signctx != null {
        r := signctx.SigUpdate(ByteCursorFromArray(header_copy, header_size));
        if r != AWS_OP_SUCCESS {
          return AWS_OP_ERR;
        }
      }

      frame_seqno, state := 1, WriteHeader;
      return AWS_OP_SUCCESS;
    }

    method priv_encrypt_compute_body_estimate() {
      // TODO
    }

    method priv_try_write_header(output: ByteBuf) returns (output': ByteBuf)
      requires GoodByteBuf(output)
      requires header_copy != null && header_size <= header_copy.Length
      modifies `output_size_estimate, `state, output.a
      ensures GoodByteBuf(output') && output'.a == output.a
      ensures state == old(state) || state == EncryptBody
    {
      output_size_estimate := header_size;

      // We'll only write the header if we have enough of an output buffer to
      // write the whole thing.

      var success;
      success, output' := ByteBufWrite(output, header_copy, header_size);
      if success {
        state := EncryptBody;
      }
    }

    method priv_try_encrypt_body(output: ByteBuf, input: ByteCursor) returns (result: Outcome, output': ByteBuf, input': ByteCursor)
      requires GoodByteBuf(output) && GoodByteCursor(input)
      requires precise_size.Some? ==> data_so_far <= precise_size.get
      requires alg_props != null && content_key != null
      modifies `output_size_estimate, `input_size_estimate, header`message_id, `data_so_far, `frame_seqno, `state, output.a
      ensures result != AWS_OP_SUCCESS ==> state == old(state) && output' == output && input' == input
      ensures state == old(state) || state == WriteTrailer
      ensures GoodByteBuf(output') && GoodByteCursor(input') && output'.a == output.a && input'.a == input.a
    {
      /* First, figure out how much plaintext we need. */
      var plaintext_size, frame_type;
      if frame_size != 0 {
        /* This is a framed message; is it the last frame? */
        if precise_size.Some? && precise_size.get - data_so_far < frame_size {
          plaintext_size, frame_type := precise_size.get - data_so_far, Cipher.FRAME_TYPE_FINAL;
        } else {
          plaintext_size, frame_type := frame_size, Cipher.FRAME_TYPE_FRAME;
        }
      } else {
        /* This is a non-framed message. We need the precise size before doing anything. */
        if precise_size == None {
          output_size_estimate, input_size_estimate := 0, 0;
          return AWS_OP_SUCCESS, output, input;
        }
        plaintext_size, frame_type := precise_size.get, Cipher.FRAME_TYPE_SINGLE;
      }

      if UINT32_MAX < frame_seqno {
        return AWS_CRYPTOSDK_ERR_LIMIT_EXCEEDED, output, input;
      }
      var frame: Frame;
      frame := frame.(typ := frame_type, sequence_number := frame_seqno);

      var ciphertext_size: nat, output_remaining;
      result, frame, ciphertext_size, output_remaining := aws_cryptosdk_serialize_frame(frame, plaintext_size, output, alg_props);
      output_size_estimate, input_size_estimate := ciphertext_size, plaintext_size;
      if result != AWS_OP_SUCCESS {
        if (aws_last_error() == AWS_ERROR_SHORT_BUFFER) {
          // The ciphertext buffer was too small. We've updated estimates;
          // just return without doing any work.
          result := AWS_OP_SUCCESS;
        } else {
          // Some kind of validation failed?
          result := AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
        }
        return result, output, input;
      }

      var success, plaintext, input_remaining := ByteCursorSplit(input, plaintext_size);
      if !success {
        // Not enough plaintext buffer space.
        return AWS_OP_SUCCESS, output, input;
      }
      result, header.message_id := alg_props.EncryptBody(frame.ciphertext,
              plaintext,
              frame.sequence_number,
              frame.iv.a,
              content_key,
              frame.authtag.a,
              frame.typ);
      if result != AWS_OP_SUCCESS {
        // Something terrible happened. Clear the ciphertext buffer and error out.
        ByteBufClear(output);
        return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN, output, input;
      }

      if signctx != null {
        // Note that the 'output' buffer contains only our ciphertext; we need to keep track of the frame
        // headers as well
        assert output.a == output_remaining.a && output.start == output_remaining.start;
        var original_start := output.start + output.len;
        var current_end    := output_remaining.start + output_remaining.len;

        var to_sign := ByteCursor(output.a, original_start, output_remaining.len - output.len);

        result := signctx.SigUpdate(to_sign);
        if result != AWS_OP_SUCCESS {
          // Something terrible happened. Clear the ciphertext buffer and error out.
          ByteCursorClear(to_sign);
          return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN, output, input;
        }
      }

      // Success! Write back our input/output cursors now, and update our state.
      output', input' := output_remaining, input_remaining;
      data_so_far := data_so_far + plaintext_size;
      frame_seqno := frame_seqno + 1;

      if frame.typ != Cipher.FRAME_TYPE_FRAME {
        // We've written a final frame, move on to the trailer
        state := WriteTrailer;
      }

      result := AWS_OP_SUCCESS;
    }

    method priv_write_trailer(output: ByteBuf) returns (result: Outcome, output': ByteBuf)
      requires GoodByteBuf(output)
      requires alg_props != null
      requires alg_props.signature_len != 0 ==> signctx != null
      modifies `input_size_estimate, `output_size_estimate, `signctx, `state, output.a
      ensures result != AWS_OP_SUCCESS ==> state == old(state) && output' == output
      ensures state == old(state) || state == Done
    {
      /* We definitely do not need any more input at this point.
       * We might need more output space, and if so we will update the
       * output estimate below. For now we set it to zero, so that when
       * session is done, both estimates will be zero.
       */
      input_size_estimate, output_size_estimate := 0, 0;

      if alg_props.signature_len == 0 {
        state := Done;
        return AWS_OP_SUCCESS, output;
      }

      // The trailer frame is a 16-bit length followed by the signature.
      // Since we generate the signature with a deterministic size, we know how much space we need
      // ahead of time.
      var size_needed := 2 + alg_props.signature_len;
      if ByteBufRemaining(output) < size_needed {
        output_size_estimate := size_needed;
        return AWS_OP_SUCCESS, output;
      }

      var signature;
      result, signature := signctx.SigFinish();
      // The signature context is unconditionally destroyed, so avoid double-free
      signctx := null;
      if result != AWS_OP_SUCCESS {
        return AWS_OP_ERR, output;
      }

      var success, bb := ByteBufWriteBe16(output, signature.Length);
      if success {
        success, bb := ByteBufWrite(bb, signature, signature.Length);
      }
      if !success {
        // Should never happen, but just in case
        return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN, output;
      }

      state := Done;
      return AWS_OP_SUCCESS, bb;
    }
  }

  type nat_4bytes = x | 0 <= x < 0x1_0000_0000

  class Header {
    var alg_id: AlgorithmID
    var frame_len: nat_4bytes
    var iv: ByteBuf
    var auth_tag: ByteBuf
    static const MESSAGE_ID_LEN := 16
    var message_id: array<byte>  // length MESSAGE_ID_LEN
    var enc_context: EncryptionContext
    var edk_list: seq<EDK.EncryptedDataKey>

    // number of bytes of header except for IV and auth tag,
    // i.e., exactly the bytes that get authenticated
    var auth_len: nat

    constructor () {  // aws_cryptosdk_hdr_init
    }

    method size() returns (bytes: nat)
      ensures iv.len + auth_tag.len <= bytes
    {
      // 18 is the total size of the non-variable-size fields in the header
      bytes := 18 + MESSAGE_ID_LEN + iv.len + auth_tag.len;
      var aad_len := enc_context_size();
      bytes := bytes + aad_len;

      var i := 0;
      while i < |edk_list|
        invariant 0 <= i <= |edk_list|
        invariant iv.len + auth_tag.len <= bytes
      {
        var edk := edk_list[i];
        // 2 bytes for each field's length header * 3 fields
        bytes := bytes + 6 + edk.provider_id.len + edk.provider_info.len + edk.ciphertext.len;
        i := i + 1;
      }
    }
    // Returns the size of enc_context
    method enc_context_size() returns (size: nat)
    {
      if |enc_context| == 0 {
        // Empty context.
        return 0;
      }
      size := 2;  // First two bytes are the number of k-v pairs
      var keysToGo := enc_context.Keys;
      while keysToGo != {}
        invariant keysToGo <= enc_context.Keys
        decreases keysToGo
      {
        var key :| key in keysToGo;
        keysToGo := keysToGo - {key};
        size := size + 2 /* key length */ + |key| + 2 /* value length */ + |enc_context[key]|;
      }
    }

    method write(outbuf: array<byte>) returns (r: Outcome, bytes_written: nat)  // int aws_cryptosdk_hdr_write(const struct aws_cryptosdk_hdr *hdr, size_t *bytes_written, uint8_t *outbuf, size_t outlen)
      modifies outbuf
  }
}
