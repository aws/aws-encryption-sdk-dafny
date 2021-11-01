// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "../EncryptionContext.dfy"
include "Defs.dfy"
include "../Keyring/Defs.dfy"
include "../MessageHeader.dfy"
include "../../Util/UTF8.dfy"
include "../Deserialize.dfy"

module {:extern "DefaultCMMDef"} DefaultCMMDef {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Materials
  import EncryptionContext
  import CMMDefs
  import KeyringDefs
  import AlgorithmSuite
  import Signature
  import Base64
  import MessageHeader
  import UTF8
  import Deserialize

  predicate {:opaque } DecryptionMaterialsFromDefaultCMM(key: seq<uint8>)
  {
    true
  }

  class DefaultCMM extends CMMDefs.CMM {
    const keyring: KeyringDefs.Keyring

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      keyring in Repr && keyring.Repr <= Repr && this !in keyring.Repr && keyring.Valid()
    }

    constructor OfKeyring(keyring: KeyringDefs.Keyring)
      //= compliance/framework/default-cmm.txt#2.5
      //= type=implication
      //# On default CMM initialization, the caller MUST provide the following
      //# value:
      // A valid Keyring
      requires keyring.Valid()
      ensures this.keyring == keyring
      ensures Valid() && fresh(Repr - keyring.Repr)
    {
      this.keyring := keyring;
      Repr := {this} + keyring.Repr;
    }

    method GetEncryptionMaterials(materialsRequest: Materials.EncryptionMaterialsRequest)
                                  returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid() 
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
        && res.value.Serializable()
        && CMMDefs.EncryptionMaterialsSignature(res.value)

      //= compliance/framework/default-cmm.txt#2.6.1
      //= type=implication
      //# If the encryption context included in the
      //# encryption materials request (cmm-interface.md#encryption-materials-
      //# request) already contains the "aws-crypto-public-key" key, this
      //# operation MUST fail rather than overwrite the associated value.
      ensures Materials.EC_PUBLIC_KEY_FIELD in materialsRequest.encryptionContext ==> res.Failure?
      
      ensures res.Success? && (materialsRequest.algorithmSuiteID.None? || materialsRequest.algorithmSuiteID.value.SignatureType().Some?) ==>
        Materials.EC_PUBLIC_KEY_FIELD in res.value.encryptionContext
      ensures res.Success? ==> res.value.Serializable()
      ensures res.Success? ==>
        match materialsRequest.algorithmSuiteID

        //= compliance/framework/default-cmm.txt#2.6.1
        //= type=implication
        //# *  If the encryption materials request (cmm-interface.md#encryption-
        //# materials-request) does contain an algorithm suite, the encryption
        //# materials returned MUST contain the same algorithm suite.
          case Some(id) => res.value.algorithmSuiteID == id

        // BLOCKED by absense of committment    
        //= compliance/framework/default-cmm.txt#2.6.1
        //= type=TODO
        //# *  If the encryption materials request (cmm-interface.md#encryption-
        //# materials-request) does contain an algorithm suite, the request
        //# MUST fail if the algorithm suite is not supported by the
        //# commitment policy (../client-apis/client.md#commitment-policy) on
        //# the request.
          case None => res.value.algorithmSuiteID == 0x0378

      //= compliance/framework/default-cmm.txt#2.6.1
      //= type=implication
      //# If the algorithm suite contains a signing algorithm (algorithm-
      //# suites.md#signature-algorithm), the default CMM MUST Add the key-
      //# value pair of key "aws-crypto-public-key", value "base64-encoded public
      //# verification key" to the encryption context (structures.md#encryption-
      //# context).      
      ensures res.Success? ==>
        match materialsRequest.algorithmSuiteID.UnwrapOr(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384).SignatureType()
          case Some(param) => |res.value.encryptionContext[Materials.EC_PUBLIC_KEY_FIELD]| > 0
          case _ => true
    {
      reveal CMMDefs.EncryptionMaterialsSignatureOpaque();
      var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
      assert reservedField in Materials.RESERVED_KEY_VALUES;
      
      //= compliance/framework/default-cmm.txt#2.6.1
      //# If the encryption context included in the
      //# encryption materials request (cmm-interface.md#encryption-materials-
      //# request) already contains the "aws-crypto-public-key" key, this
      //# operation MUST fail rather than overwrite the associated value.        
      if reservedField in materialsRequest.encryptionContext.Keys {
        return Failure("Reserved Field found in EncryptionContext keys.");
      }

      // BLOCKED by absense of committment
      //= compliance/framework/default-cmm.txt#2.6.1
      //= type=TODO
      //# *  If the encryption materials request (cmm-interface.md#encryption-
      //# materials-request) does not contain an algorithm suite, the
      //# operation MUST add the default algorithm suite for the commitment
      //# policy (../client-apis/client.md#commitment-policy) as the
      //# algorithm suite in the encryption materials returned.
      var algID := materialsRequest.algorithmSuiteID.UnwrapOr(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384);
      
      var signingKey := None;
      var encryptionContext := materialsRequest.encryptionContext;

      match algID.SignatureType() {
        case None =>

        case Some(param) =>
          
          //= compliance/framework/default-cmm.txt#2.6.1
          //# If the algorithm suite contains a signing algorithm (algorithm-
          //# suites.md#signature-algorithm), the default CMM MUST Generate a
          //# signing key (structures.md#signing-key).
          var signatureKeys :- Signature.KeyGen(param);

          //= compliance/framework/default-cmm.txt#2.6.1
          //# If the algorithm suite contains a signing algorithm (algorithm-
          //# suites.md#signature-algorithm), the default CMM MUST Add the key-
          //# value pair of key "aws-crypto-public-key", value "base64-encoded public
          //# verification key" to the encryption context (structures.md#encryption-
          //# context).
          signingKey := Some(signatureKeys.signingKey);
          var verificationKey :- UTF8.Encode(Base64.Encode(signatureKeys.verificationKey));
          encryptionContext := encryptionContext[reservedField := verificationKey];
          // The above also provides:
          //= compliance/framework/default-cmm.txt#2.6.1
          //= type=implication
          //# Adding the key "aws-crypto-public-key" SHOULD be done
          //# to a copy of the encryption context so that the caller's encryption
          //# context is not mutated.
          // Dafny implies this, as maps are immutable; thus changing a value
          // in a map actually creates a new map
      }

      // Check validity of the encryption context at runtime.
      var validAAD := EncryptionContext.CheckSerializable(encryptionContext);
      if !validAAD {
        //TODO: Provide a more specific error message here, depending on how the EncryptionContext spec was violated.
        return Failure("Invalid Encryption Context");
      }
      assert EncryptionContext.Serializable(encryptionContext);

      var materials := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algID, signingKey);
      assert materials.encryptionContext == encryptionContext;

      //= compliance/framework/default-cmm.txt#2.6.1
      //# On each call to Get Encryption Materials, the default CMM MUST make a
      //# call to its keyring's (Section 2.5.1) On Encrypt (keyring-
      //# interface.md#onencrypt) operation.
      materials :- keyring.OnEncrypt(materials);

      // The following two compliance tags are provided by the negative:
      if

        //= compliance/framework/default-cmm.txt#2.6.1
        //# The default CMM MUST obtain the Plaintext Data Key from the On
        //# Encrypt Response and include it in the encryption materials
        //# (structures.md#encryption-materials) returned.
        || materials.plaintextDataKey.None?

        //= compliance/framework/default-cmm.txt#2.6.1
        //# The default CMM MUST obtain the Encrypted Data Keys
        //# (structures.md#encrypted-data-keys) from the On Encrypt Response and
        //# include it in the encryption materials (structures.md#encryption-
        //# materials) returned.
        || |materials.encryptedDataKeys| == 0
      {
        return Failure("Could not retrieve materials required for encryption");
      }
      assert materials.Valid();
      return Success(materials);
    }

    method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                            returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
      
    {
      var verificationKey := None;

      //= compliance/framework/default-cmm.txt#2.6.2
      //= type=TODO
      //# The request MUST fail if the algorithm suite on the request is not
      //# supported by the commitment policy (../client-apis/
      //# client.md#commitment-policy) on the request.
      var algID := materialsRequest.algorithmSuiteID;
      
      var encryptionContext := materialsRequest.encryptionContext;
      var reservedField := Materials.EC_PUBLIC_KEY_FIELD;

      if algID.SignatureType().Some? {

        //= compliance/framework/default-cmm.txt#2.6.2
        //# If this key is not present in the encryption
        //# context, the operation MUST fail without returning any decryption
        //# materials.
        if reservedField !in encryptionContext {
          return Failure("Could not get materials required for decryption.");
        }

        //= compliance/framework/default-cmm.txt#2.6.2
        //# If the algorithm suite contains a signing algorithm (algorithm-
        //# suites.md#signature-algorithm), the default CMM MUST extract the
        //# verification key from the encryption context under the reserved "aws-
        //# crypto-public-key" key.
        var encodedVerificationKey := encryptionContext[reservedField];        
        var utf8Decoded :- UTF8.Decode(encodedVerificationKey);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        verificationKey := Some(base64Decoded);

      } else {

        //= compliance/framework/default-cmm.txt#2.6.2
        //# If the algorithm suite does not contain a signing algorithm
        //# (algorithm-suites.md#signature-algorithm), but the encryption context
        //# includes the reserved "aws-crypto-public-key" key, the operation MUST
        //# fail without returning any decryption materials.
        if reservedField in encryptionContext {
          return Failure("encryption context includes public key but algorithm is not a signing algorithm.");
        }
      }

      var materials := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algID, verificationKey);

      //= compliance/framework/default-cmm.txt#2.6.2
      //# On each call to Decrypt Materials, the default CMM MUST make a call
      //# to its keyring's (Section 2.5.1) On Decrypt (keyring-
      //# interface.md#ondecrypt) operation.
      materials :- keyring.OnDecrypt(materials, materialsRequest.encryptedDataKeys);

      //= compliance/framework/default-cmm.txt#2.6.2
      //# The default CMM MUST obtain the Plaintext Data Key from the On
      //# Decrypt response and include it in the decrypt materials returned.
      if materials.plaintextDataKey.None? {
        return Failure("Keyring.OnDecrypt failed to decrypt the plaintext data key.");
      }
      return Success(materials);
      
    }
  }
}



//= compliance/framework/default-cmm.txt#2.7.1
//= type=implication
//# Master key providers SHOULD NOT be
//# included in any additional implementations.

  //= compliance/framework/default-cmm.txt#2.7
  //= type=exception
  //# For implementations that support master key providers (master-key-
  //# provider-interface.md), the default CMM MUST support generating,
  //# encrypting, and decrypting data keys using master key providers.

  //= compliance/framework/default-cmm.txt#2.7.2
  //= type=exception
  //# On default CMM initialization, the caller MUST provide the following
  //# value:
  //#*  Master Key Provider (master-key-provider-interface.md)

  //= compliance/framework/default-cmm.txt#2.7.3
  //= type=exception
  //# The default CMM MUST call its master key provider's Get Master Keys
  //# for Encryption (master-key-provider-interface.md#get-master-keys-for-
  //# encryption) operation to obtain a list of master keys to use.

  //= compliance/framework/default-cmm.txt#2.7.3
  //= type=exception
  //# If the master key provider does not identify which master key MUST
  //# generate the data key, the default CMM MUST use the first master key
  //# in the list for that purpose.

  //= compliance/framework/default-cmm.txt#2.7.3
  //= type=exception
  //# The default CMM MUST generate the data
  //# key using this master key's Generate Data Key (master-key-
  //# interface.md#generate-data-key) operation.

  //= compliance/framework/default-cmm.txt#2.7.3
  //= type=exception
  //# For each remaining master key, the default CMM MUST call the master
  //# key's Encrypt Data Key (master-key-interface.md#encrypt-data-key)
  //# operation with the plaintext data key.

  //= compliance/framework/default-cmm.txt#2.7.4
  //= type=exception
  //# The default CMM MUST call its master key provider's Decrypt Data Key
  //# (master-key-provider-interface.md#decrypt-data-key) operation.

