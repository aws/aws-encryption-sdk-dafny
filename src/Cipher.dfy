include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "ByteBuf.dfy"
include "EDK.dfy"
module Cipher {
  import opened StandardLibrary
  import opened Aws
  import opened ByteBuffer
  import opened EDK

  newtype AESKeyLen = x | 0 <= x < 1_000_000
  const AWS_CRYPTOSDK_AES_128: AESKeyLen := 128 / 8
  const AWS_CRYPTOSDK_AES_192: AESKeyLen := 192 / 8
  const AWS_CRYPTOSDK_AES_256: AESKeyLen := 256 / 8

  trait AlgorithmProperties {
    // The name of the digest algorithm used for the KDF, or None if no KDF is used.
    const md_name: Option<string>
    // The name of the symmetric cipher in use.
    const cipher_name: string
    // The name of the overall algorithm suite in use (for debugging purposes)
    const alg_name: string

    // The length of the data key (that is, the key returned by the keyrings/CMMs)
    const data_key_len: nat
    /**
    * The length of the key used to actually encrypt/decrypt data. This may differ
    * if a KDF is in use.
    */
    const content_key_len: nat
    // The IV length for this algorithm suite
    const iv_len: byte
    /**
    * The AEAD tag length for this algorithm suite. Note that, currently, we only
    * support stream-like ciphers that do not require padding, so the ciphertext
    * size is equal to the plaintext size plus tag (and IV, if you pre/append IV).
    */
    const tag_len: nat
    /**
    * The length of the trailing signature. Zero if there is no trailing signature
    * for this algorithm suite.
    */
    const signature_len: nat

    /**
    * The algorithm ID for this algorithm suite
    */
    const alg_id: AlgorithmID

    method SignHeader(content_key: content_key, authtag: ByteBuf, header: ByteBuf) returns (r: Outcome)  // int aws_cryptosdk_sign_header(const struct aws_cryptosdk_alg_properties *props, const struct content_key *content_key, const struct aws_byte_buf *authtag, const struct aws_byte_buf *header)
      requires GoodByteBuf(authtag) && GoodByteBuf(header)
      modifies header.a
    {
      // TODO
    }

    method EncryptBody(outp: ByteBuf, inp: ByteCursor, seqno: nat, iv: array<byte>, key: content_key, tag: array<byte>, body_frame_type: FrameType)
      returns (result: Outcome, message_id: array<byte>)
      ensures fresh(message_id)
    {
      // TODO
      message_id := new [][];  // TODO
    }

  }

  class AlgorithmProperties_AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE extends AlgorithmProperties {
    constructor ()
      ensures alg_id == AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE
    {
      this.md_name := Some("NULL");
      this.cipher_name := "aes_128_gcm";
      this.alg_name := "AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE";
      this.data_key_len := 128 / 8;
      this.content_key_len := 128 / 8;
      this.iv_len := 12;
      this.tag_len := 16;
      this.signature_len := 0;
      this.alg_id := AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE;
    }
  }

  class AlgorithmProperties_AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE extends AlgorithmProperties {
    constructor ()
      ensures alg_id == AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE
    {
      this.md_name := Some("NULL");
      this.cipher_name := "aes_256_gcm";
      this.alg_name := "AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE";
      this.data_key_len := 256 / 8;
      this.content_key_len := 256 / 8;
      this.iv_len := 12;
      this.tag_len := 16;
      this.signature_len := 0;
      this.alg_id := AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE;
    }
  }

  /**
  * Looks up and returns the algorithm properties for a particular algorithm ID.
  * Returns null if alg_id is unknown.
  */
  method AlgProperties(id: AlgorithmID) returns (p: AlgorithmProperties?)
    ensures p != null ==> p.alg_id == id
  {
    if id == AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE {
      p := new AlgorithmProperties_AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE();
    } else if id == AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE {
      p := new AlgorithmProperties_AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE();
    } else {
      p := null;  // unknown
    }
  }

  datatype FrameType = FRAME_TYPE_SINGLE | FRAME_TYPE_FRAME | FRAME_TYPE_FINAL

  /**
  * Represents an ongoing sign or verify operation
  */
  class SignCtx {
    method SigUpdate(cursor: ByteCursor) returns (r: Outcome)
    method SigFinish() returns (r: Outcome, signature: array<byte>)
      ensures r == AWS_OP_SUCCESS ==> signature.Length < 0x1_0000
  }

  method GenRandom(buf: array<byte>) returns (r: Outcome)
    modifies buf
  {
    var rc := RAND_bytes(buf, buf.Length);
    if rc != 1 {
      forall i | 0 <= i < buf.Length {
        buf[i] := 0;
      }
      return AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN;
    }
    return AWS_OP_SUCCESS;
  }
  // TODO: the following method belongs in some library somewhere
  // A return code of 1 means success (how could this operation fail?)
  method RAND_bytes(buf: array<byte>, n: nat) returns (rc: int)
    requires n <= buf.Length
    modifies buf {}

  class content_key { }  // TODO

  method DeriveKey(properties: AlgorithmProperties, dataKey: array<byte>, messageId: array<byte>) 
  returns (r: Outcome, contentKey: content_key) {}

  method ByteBufCleanUp(bb: ByteBuf){}

  method EncContextSize(enc_context: EncryptionContext) returns (result: Outcome, aad_len: nat) {}

  method EncContextSerialize(aad: ByteBuf, enc_context: EncryptionContext) returns (result: Outcome) {}
/**
 * Does AES-GCM encryption using AES-256/192/128 with 12 byte IVs and 16 byte tags only.
 * Determines which AES algorithm to use based on length of key.
 *
 * Assumes cipher and tag are already allocated byte buffers. Does NOT assume that lengths
 * of buffers are already set, and will set them on successful encrypt.
 *
 * Returns AWS_OP_SUCCESS on a successful encrypt. On failure, returns AWS_OP_ERR and sets
 * one of the following error codes:
 *
 * AWS_INVALID_BUFFER_SIZE : bad key or IV length, or not enough capacity in output buffers
 * AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN : OpenSSL error
 *
 * On last error, output buffers will be set to all zero bytes, and their lengths will be
 * set to zero.
 */

  method AesGcmEncrypt(tag: ByteBuf, plain: ByteCursor, iv: ByteCursor,
  aad: ByteCursor, key: string) returns (result: Outcome, cipher: ByteBuf) {}

  /**
 * Does AES-GCM decryption using AES-256/192/128 with 12 byte IVs and 16 byte tags only.
 * Determines which AES algorithm to use based on length of key.
 *
 * Assumes plain is an already allocated byte buffer. Does NOT assume that length of plain
 * buffer is already set, and will set it to the length of plain on a successful decrypt.
 *
 * Returns AWS_OP_SUCCESS on a successful decrypt. On failure, returns AWS_OP_ERR and sets
 * one of the following error codes:
 *
 * AWS_INVALID_BUFFER_SIZE : bad key, tag, or IV length, or not enough capacity in plain
 * AWS_CRYPTOSDK_ERR_BAD_CIPHERTEXT : unable to decrypt or authenticate ciphertext
 * AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN : OpenSSL error
 *
 * On either of the last two errors, the plain buffer will be set to all zero bytes, and its
 * length will be set to zero.
 */

  method AesGcmDecrypt(cipher: ByteCursor, tag: ByteCursor, iv: ByteCursor, aad: ByteCursor, 
  key: string) returns (result: Outcome, plain: ByteBuf) {}

  /**
 * Does RSA encryption of an unencrypted data key to an encrypted data key.
 * RSA with PKCS1, OAEP_SHA1_MGF1 and OAEP_SHA256_MGF1 padding modes is supported.
 *
 * Here, 'cipher' is the encrypted AES data key obtained as a result of the RSA encryption,
 *'rsa_public_key_pem' is a string that contains the RSA public key in PEM format and 'plain'
 * refers to the unencrypted AES data key.
 *
 * This function requires that cipher has no memory allocated to it already, and allocates
 * it newly. The length of the buffer will be set to the length of cipher on a successful encrypt.
 *
 * Returns AWS_OP_SUCCESS on a successful encrypt. On failure, returns AWS_OP_ERR and sets
 * one of the following error codes:
 *
 * AWS_CRYPTOSDK_ERR_BAD_STATE : the output buffer was not in the proper (unallocated) state
 * AWS_CRYPTOSDK_ERR_UNSUPPORTED_FORMAT: unsupported padding mode for RSA wrapping algorithm
 * AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN : OpenSSL error or other unknown errors
 */
  method RsaEncrypt(plain: ByteCursor, rsa_public_key_pem: string,
    rsa_paddding_mode: RsaPaddingMode) returns (result: Outcome, cipher: ByteBuf) {}

/**
 * Does RSA decryption of an encrypted data key to an unecrypted data key.
 * RSA with PKCS1, OAEP_SHA1_MGF1 and OAEP_SHA256_MGF1 padding modes is supported.
 *
 * Here, 'plain' refers to the unencrypted AES data key obtained as a result of the RSA
 * decryption, 'rsa_private_key_pem' is a string that contains the RSA private key in PEM
 * format and 'cipher' is the encrypted AES data key.
 *
 * This function requires that plain has no memory allocated to it already, and allocates
 * it newly. The length of the buffer will be set to the length of plain on a successful decrypt.
 *
 * Returns AWS_OP_SUCCESS on a successful decrypt. On failure, returns AWS_OP_ERR and sets
 * one of the following error codes:
 *
 * AWS_CRYPTOSDK_ERR_BAD_STATE : the output buffer was not in the proper (unallocated) state
 * AWS_CRYPTOSDK_ERR_UNSUPPORTED_FORMAT: unsupported padding mode for RSA wrapping algorithm
 * AWS_CRYPTOSDK_ERR_BAD_CIPHERTEXT : unable to decrypt or authenticate cipher text
 * AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN : OpenSSL error
 */
  method RsaDecrypt(cipher: ByteCursor, rsa_private_key_pem: string, 
    rsa_paddding_mode: RsaPaddingMode) returns (result: Outcome, plain: ByteBuf) {}
}
