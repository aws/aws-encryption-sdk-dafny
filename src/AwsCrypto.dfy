include "StandardLibrary.dfy"

// ----- general Aws Crypto things

module Aws {
  import opened StandardLibrary

  datatype Outcome =
    | AWS_OP_SUCCESS
    | AWS_OP_ERR
    /** The ciphertext was malformed or corrupt */
    | AWS_CRYPTOSDK_ERR_BAD_CIPHERTEXT /* 0x2000 */
    /** An unknown internal error has occurred */
    | AWS_CRYPTOSDK_ERR_CRYPTO_UNKNOWN
    /** An unsupported format version was encountered on decrypt */
    | AWS_CRYPTOSDK_ERR_UNSUPPORTED_FORMAT
    /** KMS returned an error */
    | AWS_CRYPTOSDK_ERR_KMS_FAILURE
    /** A function was called on an object in the wrong state */
    | AWS_CRYPTOSDK_ERR_BAD_STATE
    /** The failing call attempted to exceed a hard limit of some sort I*/
    | AWS_CRYPTOSDK_ERR_LIMIT_EXCEEDED
    /** No keyrings were able to decrypt the message in question */
    | AWS_CRYPTOSDK_ERR_CANNOT_DECRYPT
    | AWS_CRYPTOSDK_ERR_END_RANGE /* 0x2400 */
    | AWS_ERROR_SHORT_BUFFER

  function method aws_last_error(): Outcome  // TODO: this should not be a function like this

  type EncryptionContext = map<string,string>

  newtype AlgorithmID = x | 0 <= x < 0x1000
  const AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384 : AlgorithmID := 0x0378
  const AES_192_GCM_IV12_AUTH16_KDSHA384_SIGEC384 : AlgorithmID := 0x0346
  const AES_128_GCM_IV12_AUTH16_KDSHA256_SIGEC256 : AlgorithmID := 0x0214
  const AES_256_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : AlgorithmID := 0x0178
  const AES_192_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : AlgorithmID := 0x0146
  const AES_128_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : AlgorithmID := 0x0114
  const AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE    : AlgorithmID := 0x0078
  const AES_192_GCM_IV12_AUTH16_KDNONE_SIGNONE    : AlgorithmID := 0x0046
  const AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE    : AlgorithmID := 0x0014

  class SDKOptions { }
  method InitAPI() returns (options: SDKOptions) {
    options := new SDKOptions;
  }
  method ShutdownAPI(options: SDKOptions) {}

  const UINT64_MAX := 0xFFFF_FFFF_FFFF_FFFF
  const UINT32_MAX := 0xFFFF_FFFF

  // Mathematical encryption/decryption functions used in specifications
  module Math {
    import opened StandardLibrary
    // TODO: The properties about Encrypt and Decrypt stated here in
    // postconditions and a lemma are quite specific. They are just a proof-of-concept
    // for now and should be generalized.
    function {:axiom} Encrypt(plaintext: seq<byte>): seq<byte>
      //ensures |Encrypt(plaintext)| == |plaintext|
    function {:axiom} Decrypt(ciphertext: seq<byte>): seq<byte>
      //ensures |Decrypt(ciphertext)| == |ciphertext|
    lemma {:axiom} GoodEncryption(plaintext: seq<byte>)
      ensures Decrypt(Encrypt(plaintext)) == plaintext
  }
}
