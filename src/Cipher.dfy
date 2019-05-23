include "StandardLibrary.dfy"
include "AwsCrypto.dfy"
include "ByteBuf.dfy"
include "ByteOrder.dfy"

module Cipher {
  import opened StandardLibrary
  import opened Aws
  import opened ByteBuffer
  import opened ByteOrder

  newtype AESKeyLen = x | 0 <= x < 1_000_000
  const AWS_CRYPTOSDK_AES_128: AESKeyLen := 128 / 8
  const AWS_CRYPTOSDK_AES_192: AESKeyLen := 192 / 8
  const AWS_CRYPTOSDK_AES_256: AESKeyLen := 256 / 8

  datatype RSAPaddingMode =
    | AWS_CRYPTOSDK_RSA_PKCS1
    | AWS_CRYPTOSDK_RSA_OAEP_SHA1_MGF1
    | AWS_CRYPTOSDK_RSA_OAEP_SHA256_MGF1

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
    modifies buf

  class content_key 
  {
    var k: array<byte>
    var len: nat
    constructor (k': array<byte>, len':nat)
      ensures k' == k
      ensures len' == len
    {
      this.k := k';
      this.len := len';
    }
  }  // TODO

  
  datatype HMAC_ALGORITHM = HmacSHA256 | HmacMD5 | HmacSHA1 | AWS_CRYPTOSDK_NOSHA
  method WhichSha(properties: AlgorithmProperties) returns (h: HMAC_ALGORITHM)

  method HKDF(which_sha: HMAC_ALGORITHM, salt: Option<array<byte>>, ikm: array<byte>, info: array<byte>, L: nat) returns (okm: array<byte>)
    ensures okm.Length == L
  method DeriveKey(properties: AlgorithmProperties, dataKey: array<byte>, messageId: array<byte>) returns (r: Outcome, contentKey: content_key)
    requires properties.data_key_len == dataKey.Length
    // TODO
  {
    var which_sha := WhichSha(properties);
    if (which_sha == AWS_CRYPTOSDK_NOSHA) {
      var okm := new byte[properties.data_key_len];
      forall i:nat | i < properties.data_key_len {
        okm[i] := dataKey[i];
      }
      contentKey := new content_key(okm, properties.data_key_len);
      r := AWS_OP_SUCCESS;
      return;
    }

    var info := new byte[messageId.Length + 2];
    info[0], info[1] := ToBytes2(properties.alg_id as nat);
    forall i:nat | i < messageId.Length {
      info[i+2] := messageId[i];
    }
    var L := properties.content_key_len;
    var salt := None;
    var ikm := dataKey;
    // TODO: initialize okm with content key? Does HKDF read/extend okm?
    var okm := HKDF(which_sha, salt, ikm, info, L);
    assert okm.Length == L;
    contentKey := new content_key(okm, L);
    assert L == contentKey.len;
    r := AWS_OP_SUCCESS;
  }
}
