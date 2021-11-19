// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// TODO: Originally written as part of POC; we should come back through this
// to refine it

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Util/UTF8.dfy"
include "../Crypto/EncryptionSuites.dfy"
include "Keyring/RawAESKeyring.dfy"
include "CMM/DefaultCMM.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient"} AwsCryptographicMaterialProviders {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionSuites
  import UTF8
  import Aws.Crypto
  import DefaultCMMDef
  import RawAESKeyringDef
  import Aws.Esdk

  class AwsCryptographicMaterialProvidersClient extends Crypto.IAwsCryptographicMaterialsProviderClient {
    constructor () {}

    method CreateRawAesKeyring(input: Crypto.CreateRawAesKeyringInput) returns (res: Crypto.IKeyring)
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
      assert wrappingAlg.Valid();

      expect |namespace| < UINT16_LIMIT;
      expect |input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32;
      expect |input.wrappingKey| == wrappingAlg.keyLen as int;

      return new RawAESKeyringDef.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput) returns (res: Crypto.ICryptographicMaterialsManager)
    {
        return new DefaultCMMDef.DefaultCMM.OfKeyring(input.keyring);
    }
  }
}