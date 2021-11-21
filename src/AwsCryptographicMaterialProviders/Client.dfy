// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Util/UTF8.dfy"
include "../Crypto/AESEncryption.dfy"
include "Keyrings/RawAESKeyring.dfy"
include "CMMs/DefaultCMM.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.Client"}
  MaterialProviders.Client
{
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Aws.Crypto
  import AESEncryption
  import RawAESKeyring
  import DefaultCMM

  export
    provides
      AwsCryptographicMaterialProvidersClient

  class AwsCryptographicMaterialProvidersClient
    // extends Crypto.IAwsCryptographicMaterialsProviderClient
  {
    constructor () {}

    method CreateRawAesKeyring(input: Crypto.CreateRawAesKeyringInput)
      returns (res: Crypto.IKeyring)
    {
      var wrappingAlg:AESEncryption.AES_GCM;
      if (input.wrappingAlg==Crypto.ALG_AES128_GCM_IV12_TAG16) {
        wrappingAlg := AESEncryption.AES_GCM(
          keyLength := 16 as AESEncryption.KeyLength,
          tagLength := 16 as AESEncryption.TagLength,
          ivLength := 12 as AESEncryption.IVLength
        );
      } else if (input.wrappingAlg==Crypto.ALG_AES192_GCM_IV12_TAG16) {
        wrappingAlg := AESEncryption.AES_GCM(
          keyLength := 24 as AESEncryption.KeyLength,
          tagLength := 16 as AESEncryption.TagLength,
          ivLength := 12 as AESEncryption.IVLength
        );
      } else {
        assert input.wrappingAlg==Crypto.ALG_AES256_GCM_IV12_TAG16;
        wrappingAlg := AESEncryption.AES_GCM(
          keyLength := 32 as AESEncryption.KeyLength,
          tagLength := 16 as AESEncryption.TagLength,
          ivLength := 12 as AESEncryption.IVLength
        );
      }
      // I have no idea why :- isn't working here...
      // Here is why: To use :- requires the type of "res" to be "Result<Crypto.IKeyring, string>".
      var namespaceRes := UTF8.Encode(input.keyNamespace);
      var namespace := []; // TODO: This value gets used below if UTF8.Encode fails
      if namespaceRes.Success? {
        namespace := namespaceRes.value;
      }
      var nameRes := UTF8.Encode(input.keyName);
      var name := []; // TODO: This value gets used below if UTF8.Encode fails
      if nameRes.Success? {
        name := nameRes.value;
      }

      expect |namespace| < UINT16_LIMIT;
      expect |input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32;
      expect |input.wrappingKey| == wrappingAlg.keyLength as int;

      var keyring := new RawAESKeyring.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
      return keyring;
    }


    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput)
      returns (res: Crypto.ICryptographicMaterialsManager)
    {
        return new DefaultCMM.DefaultCMM.OfKeyring(input.keyring);
    }
  }

}
