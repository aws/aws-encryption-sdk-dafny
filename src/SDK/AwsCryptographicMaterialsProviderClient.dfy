// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "EncryptionContext.dfy"
include "CMM/Defs.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "Deserialize.dfy"
include "Keyring/Defs.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/KeyDerivationAlgorithms.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Util/UTF8.dfy"
include "../Crypto/EncryptionSuites.dfy"
include "Keyring/PolymorphRawAESKeyring.dfy"
include "CMM/PolymorphDefaultCMM.dfy"
include "Client.dfy"

module {:extern "MaterialsProviderClientDefs"} MaterialsProviderClientDefs {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import EncryptionSuites
  import UTF8
  import Aws.Crypto
  import PolymorphDefaultCMMDef
  import PolymorphRawAESKeyringDef
  import Aws.Esdk
  import Client = ESDKClient

  const VALID_ALGORITHMS := {EncryptionSuites.AES_GCM_128, EncryptionSuites.AES_GCM_192, EncryptionSuites.AES_GCM_256}

  class MaterialsProviderClient extends Crypto.IAwsCryptographicMaterialsProviderClient {
    constructor () {}

    method CreateRawAesKeyring(input: Crypto.CreateRawAesKeyringInput) returns (res: Crypto.IKeyring)
      requires input.Valid()
    {
      var wrappingAlg:EncryptionSuites.EncryptionSuite;
      if (input.wrappingAlg==Crypto.ALG_AES128_GCM_IV12_TAG16) {
        wrappingAlg := EncryptionSuites.AES_GCM_128;
      } else if (input.wrappingAlg==Crypto.ALG_AES192_GCM_IV12_TAG16) {
        wrappingAlg := EncryptionSuites.AES_GCM_192;
      } else {
        assert input.wrappingAlg==Crypto.ALG_AES256_GCM_IV12_TAG16;
        wrappingAlg := EncryptionSuites.AES_GCM_256;
      }
      // I have no idea why :- isn't working here...
      var namespaceRes := UTF8.Encode(input.keyNamespace);
      var namespace;
      if namespaceRes.Success? {
        namespace := namespaceRes.value;
      }
      var nameRes := UTF8.Encode(input.keyName);
      var name;
      if nameRes.Success? {
        name := nameRes.value;
      }
      assert wrappingAlg in VALID_ALGORITHMS;
      assert wrappingAlg.Valid(); 

      expect |namespace| < UINT16_LIMIT;
      expect |input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32;
      expect |input.wrappingKey| == wrappingAlg.keyLen as int;
      
      return new PolymorphRawAESKeyringDef.PolymorphRawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput) returns (res: Crypto.ICryptographicMaterialsManager)
      requires input.Valid()
    {
        expect input.keyring.Valid();
        return new PolymorphDefaultCMMDef.PolymorphDefaultCMM.OfKeyring(input.keyring);
    }
  }

  // move to different module
  class PolymorphClient extends Esdk.IAwsEncryptionSdkClient {
        constructor () {}

        method Encrypt(input: Esdk.EncryptInput) returns (res: Result<Esdk.EncryptOutput, string>)
            requires input.Valid()
            ensures input.materialsManager.Valid()
        {
            expect input.materialsManager.Valid();
            var encryptRequest := Client.EncryptRequest.WithCMM(input.plaintext, input.materialsManager).SetEncryptionContext(input.encryptionContext);
            var e :- expect Client.Encrypt(encryptRequest);
            // TODO is this weird?
            expect input.materialsManager.Valid();
            return Success(Esdk.EncryptOutput(ciphertext:=e));
        }
        method Decrypt(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, string>)
            requires input.Valid()
            ensures input.materialsManager.Valid()
        {
            expect input.materialsManager.Valid();
            var decryptRequest := Client.DecryptRequest.WithCMM(input.ciphertext, input.materialsManager);
            var d :- expect Client.Decrypt(decryptRequest);
            // TODO is this weird?
            expect input.materialsManager.Valid();
            return Success(Esdk.DecryptOutput(plaintext:=d));
        }
  }
}