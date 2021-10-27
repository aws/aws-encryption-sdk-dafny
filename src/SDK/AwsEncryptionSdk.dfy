// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Util/UTF8.dfy"
include "EncryptDecrypt.dfy"

module {:extern "AwsEncryptionSdk"} AwsEncryptionSdk {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Aws.Crypto
  import Aws.Esdk
  import EncryptDecrypt

  // move to different module
  class AwsEncryptionSdkClient extends Esdk.IAwsEncryptionSdkClient {
        constructor () {}

        method Encrypt(input: Esdk.EncryptInput) returns (res: Result<Esdk.EncryptOutput, string>)
            requires input.Valid()
        {
            var encryptRequest := EncryptDecrypt.EncryptRequest.WithCMM(input.plaintext, input.materialsManager).SetEncryptionContext(input.encryptionContext);
            var e :- expect EncryptDecrypt.Encrypt(encryptRequest);
            return Success(Esdk.EncryptOutput(ciphertext:=e));
        }
        method Decrypt(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, string>)
            requires input.Valid()
        {
            var decryptRequest := EncryptDecrypt.DecryptRequest.WithCMM(input.ciphertext, input.materialsManager);
            var d :- expect EncryptDecrypt.Decrypt(decryptRequest);
            return Success(Esdk.DecryptOutput(plaintext:=d));
        }
  }
}