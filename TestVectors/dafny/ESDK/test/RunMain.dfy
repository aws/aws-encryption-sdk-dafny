// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Test vector projects just run as a CLI
// So all the tests are in the Main.
// By creating a single file here,
// it is easy to kick off a test run.
include "../src/Index.dfy"

module TestWrappedMaterialProvidersMain {
  import WrappedESDKMain
  import EsdkTestManifests
  import EsdkManifestOptions
  import opened Wrappers

  // method {:test} TestV1Vectors() {
  //   var _ :- expect EsdkTestManifests.StartV1DecryptVectors(
  //     "aws-encryption-sdk-test-vectors/vectors/awses-decrypt/python-1.3.5/decrypt_message.json",
  //     "aws-encryption-sdk-test-vectors/vectors/awses-decrypt/python-1.3.5/keys.json"
  //   );
  // }


  // method {:test} TestV2Vectors() {
  //   var _ :- expect EsdkTestManifests.StartDecryptVectors(
  //     EsdkManifestOptions.Decrypt(
  //       manifestPath := "aws-encryption-sdk-test-vectors/vectors/awses-decrypt/python-2.3.0/"
  //     )
  //   );
  // }

  method {:test} TestEncryptVectors() {
    var result := EsdkTestManifests.StartEncryptVectors(
      EsdkManifestOptions.Encrypt(
        manifestPath := "./",
        manifest := "0003-awses-message-encryption.v1.json",
        decryptManifestOutput := "decrypt-manifest/"
      )
    );

    if result.Failure? {
      print result.error, "\n";
    }

    expect result.Success?;
  }

  method {:test} TestDecryptVectors() {
    var _ :- expect EsdkTestManifests.StartDecryptVectors(
      EsdkManifestOptions.Decrypt(
        manifestPath := "decrypt-manifest/"
      )
    );
  }

  // method {:test} TestV2Vectors() {
  //   TestEsdkManifests.StartV1Vectors(
  //     "dafny/ESDK/test/python-2.3.0/manifest.json",
  //     "dafny/ESDK/test/python-2.3.0/keys.json"
  //   );

  // }

}
