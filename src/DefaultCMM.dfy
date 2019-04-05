include "StandardLibrary.dfy"
include "KeyringTrace.dfy"
include "EDK.dfy"
include "Materials.dfy"
include "Cipher.dfy"

module DefaultCryptoMaterialsManager {
  import opened StandardLibrary
  import opened Aws
  import opened KeyringTraceModule
  import opened EDK
  import opened Materials
  import opened Cipher

  /**
  * Instantiate the default (non-caching) implementation of the Crypto Materials
  * Manager (CMM). A Keyring (KR) must have already been instantiated
  * and a pointer to it passed in. This CMM maintains no state of its own other
  * than pointers to the KR and allocator. It implements all of the CMM virtual
  * functions.
  *
  * On each attempt to generate encryption materials, it asks the KR to generate a
  * data key.
  *
  * On each attempt to decrypt materials, it passes the full list of EDKs to the KR
  * and asks it to find one to decrypt.
  *
  * If a CMM that delegates to the default CMM selects an algorithm suite, that algorithm
  * suite will be used. Otherwise, the default CMM will select a default algorithm suite.
  * This is initially AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384, but can be overridden using
  * aws_cryptosdk_default_cmm_set_alg_id.
  *
  * On success allocates a CMM and returns its address. Be sure to deallocate it later
  * by calling aws_cryptosdk_cmm_destroy on the CMM pointer returned by this function.
  */
  class DefaultCMM extends CMM {
    var kr: Keyring
    var alg_props: AlgorithmProperties

    constructor New(kr: Keyring)
    {
      this.kr := kr;
    }

    /**
    * Selects the algorithm suite ID to use for encryption. If not called, a reasonable
    * default will be selected.
    * Raises AWS_CRYPTOSDK_ERR_UNSUPPORTED_FORMAT if the algorithm suite ID is unknown.
    */
    method SetAlgorithmID(alg_id: AlgorithmID) returns (result: Outcome)
    {

    }

    // TODO
    method Destroy()
    // TODO
    method Generate(request: EncryptionRequest) returns (result: Outcome, materials: EncryptionMaterials)
      modifies request
    // TODO
    method Decrypt(request: DecryptionRequest) returns (result: Outcome, materials: DecryptionMaterials)
  }
}
