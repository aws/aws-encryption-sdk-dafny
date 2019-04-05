include "StandardLibrary.dfy"
include "AwsCrypto.dfy"

module Cipher {
  import opened StandardLibrary
  import opened Aws

  newtype AESKeyLen = x | 0 <= x < 1_000_000
  const AWS_CRYPTOSDK_AES_128: AESKeyLen := 128 / 8
  const AWS_CRYPTOSDK_AES_192: AESKeyLen := 192 / 8
  const AWS_CRYPTOSDK_AES_256: AESKeyLen := 256 / 8

  datatype RSAPaddingMode =
    | AWS_CRYPTOSDK_RSA_PKCS1
    | AWS_CRYPTOSDK_RSA_OAEP_SHA1_MGF1
    | AWS_CRYPTOSDK_RSA_OAEP_SHA256_MGF1

  class AlgorithmProperties {
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
      const iv_len: nat
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

      /**
      * Looks up and returns the algorithm properties for a particular algorithm ID.
      * Returns null if alg_id is unknown.
      */
      static method AlgProperties(alg_id: AlgorithmID) returns (p: AlgorithmProperties?)
        ensures p != null ==> p.alg_id == alg_id
  }

  /**
  * Represents an ongoing sign or verify operation
  */
  class SignCtx { }
}
