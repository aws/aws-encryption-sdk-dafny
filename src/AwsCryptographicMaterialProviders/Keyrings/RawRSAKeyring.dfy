// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../AlgorithmSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"
include "../../Util/Streams.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"


  
module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.RawRSAKeyring"}
  MaterialProviders.RawRSAKeyring
{
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Crypto
  import Keyring
  import Materials
  import opened AlgorithmSuites
  import Random
  import RSAEncryption
  import UTF8
  import Seq

  type ValidRSAPublicKey = key: RSAEncryption.PublicKey | key.Valid()  witness *
  type ValidRSAPrivateKey = key: RSAEncryption.PrivateKey | key.Valid() witness *

  function method paddingSchemeToMinStrengthBits(
    padding: RSAEncryption.PaddingMode
  ): (strength: RSAEncryption.StrengthBits)
    //Reverse of RSAEncryption.GetBtyes
    ensures RSAEncryption.GetBytes(strength) == RSAEncryption.MinStrengthBytes(padding)
  {
    ((RSAEncryption.MinStrengthBytes(padding) * 8) - 7) as RSAEncryption.StrengthBits
  }

  //TODO :: What external method can we use to verify a pem is a pem?
  //TODO :: Where should this method live? Probably in AwsCryptographicMaterialProviders
  method importPrivateKey(
    pem: seq<uint8>,
    padding: RSAEncryption.PaddingMode
  ) returns (res: Result<ValidRSAPrivateKey, string>)
    requires |pem| > 0
    requires RSAEncryption.GetBytes(paddingSchemeToMinStrengthBits(padding)) >= RSAEncryption.MinStrengthBytes(padding)
    requires RSAEncryption.PEMGeneratedWithStrength(pem, paddingSchemeToMinStrengthBits(padding))
    requires RSAEncryption.PEMGeneratedWithPadding(pem, padding)
    ensures
      res.Success?
    ==>
      && res.value.pem == pem
      && res.value.strength >= paddingSchemeToMinStrengthBits(padding)
      && res.value.padding == padding
      && res.value.Valid()
  {
    var key := new RSAEncryption.PrivateKey(
      pem := pem,
      padding := padding,
      strength := paddingSchemeToMinStrengthBits(padding)
    );
    return Success(key);
  }

  //TODO :: What external method can we use to verify a pem is a pem?
  //TODO :: Where should calling said method live? Probably in AwsCryptographicMaterialProviders  
  method importPublicKey(
    pem: seq<uint8>,
    padding: RSAEncryption.PaddingMode
  ) returns (res: Result<ValidRSAPublicKey, string>)
    requires |pem| > 0
    requires RSAEncryption.GetBytes(paddingSchemeToMinStrengthBits(padding)) >= RSAEncryption.MinStrengthBytes(padding)
    requires RSAEncryption.PEMGeneratedWithStrength(pem, paddingSchemeToMinStrengthBits(padding))
    requires RSAEncryption.PEMGeneratedWithPadding(pem, padding)
    ensures
      res.Success?
    ==>
      && res.value.pem == pem
      && res.value.strength >= paddingSchemeToMinStrengthBits(padding)
      && res.value.padding == padding
      && res.value.Valid()
  {
    var key := new RSAEncryption.PublicKey(
      pem := pem,
      padding := padding,
      strength := paddingSchemeToMinStrengthBits(padding)
    );
    return Success(key);
  }
    
  class RawRSAKeyring
    extends Keyring.VerifiableInterface, Crypto.IKeyring
  {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const publicKey: Option<seq<uint8>>
    const privateKey: Option<seq<uint8>>
    const paddingScheme: RSAEncryption.PaddingMode

    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,
      publicKey: Option<seq<uint8>>,
      privateKey: Option<seq<uint8>>,
      paddingScheme: RSAEncryption.PaddingMode
    )
      requires |namespace| < UINT16_LIMIT
      requires |name| < UINT16_LIMIT
      ensures this.keyNamespace == namespace
      ensures this.keyName == name
      ensures this.paddingScheme == paddingScheme
      ensures this.publicKey == publicKey
      ensures this.privateKey == privateKey
    {
      this.keyNamespace := namespace;
      this.keyName := name;
      this.paddingScheme := paddingScheme;
      this.publicKey := publicKey;
      this.privateKey := privateKey;
    }
    
    method OnEncrypt(input: Crypto.OnEncryptInput)
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      ensures
        res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )
    {
      :- Need(
        this.publicKey.Some? && |this.publicKey.Extract()| > 0,
        "A RawRSAKeyring without a public key cannot provide OnEncrypt"
      );

      var materials := input.materials;
      var suite := GetSuite(materials.algorithmSuiteId);
      
      var newPlaintextDataKey :- Random.GenerateBytes(suite.encrypt.keyLength as int32);

      var plaintextDataKey :=
        if materials.plaintextDataKey.Some? && |materials.plaintextDataKey.Extract()| > 0
        then materials.plaintextDataKey.value
        else newPlaintextDataKey;
      
      var ciphertext :- RSAEncryption.EncryptExtern(
        this.paddingScheme,
        this.publicKey.Extract(),
        plaintextDataKey
      );
        
      var edk: Crypto.EncryptedDataKey := Crypto.EncryptedDataKey(
        keyProviderId := this.keyNamespace,
        keyProviderInfo := this.keyName,
        ciphertext := ciphertext
      );
        
      var r :- if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk])
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
      return Success(Crypto.OnEncryptOutput(materials := r));      
    }

    method OnDecrypt(input: Crypto.OnDecryptInput)
      returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )
    {
      :- Need(
        this.privateKey.Some? && |this.privateKey.Extract()| > 0,
        "A RawRSAKeyring without a private key cannot provide OnEncrypt"
      );

      var materials := input.materials;
      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        "Keyring received decryption materials that already contain a plaintext data key."
      );

      var i := 0;
      while i < |input.encryptedDataKeys|
        invariant forall prevIndex :: 0 <= prevIndex < i ==> prevIndex < |input.encryptedDataKeys|
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          var edk := input.encryptedDataKeys[i];
          var decryptResult := RSAEncryption.DecryptExtern(
            this.paddingScheme,
            this.privateKey.Extract(),
            edk.ciphertext
          );
  
          if decryptResult.Success? {
            var r :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResult.Extract());
            return Success(Crypto.OnDecryptOutput(materials := r));
          }
        }
        i := i + 1;
      }
      return Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.");
    }

    predicate method ShouldDecryptEDK(edk: Crypto.EncryptedDataKey) {
      && edk.keyProviderInfo == this.keyName
      && edk.keyProviderId == this.keyNamespace
      && |edk.ciphertext| > 0
    }
  }
}
