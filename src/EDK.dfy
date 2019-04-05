include "StandardLibrary.dfy"
include "AwsCrypto.dfy"

module EDK {
  import opened StandardLibrary
  import opened Aws

  /*
  * This public interface to the encrypted data key (EDK) objects is provided for
  * developers of CMMs and keyrings only. If you are a user of the AWS Encryption
  * SDK and you are not developing your own CMMs and/or keyrings, you do not
  * need to use it and you should not do so.
  */

  type EncryptedDataKey
}
