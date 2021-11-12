// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../AwsCryptographicMaterialProviders/AlgorithmSuites.dfy"

module {:extern "EncryptionSuites"} EncryptionSuites {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AwsCryptographicMaterialProviders2.AlgorithmSuites

  datatype EncryptionAlgorithm = AES(mode: AESMode)
  datatype AESMode = GCM

  datatype EncryptionSuite = EncryptionSuite(alg: EncryptionAlgorithm, keyLen: uint8, tagLen: uint8, ivLen: uint8)
  {
    // TODO does this need to be a method, or can it be pure?
    predicate method Valid() {
      match alg
      case AES(mode) => keyLen as int in AES_CIPHER_KEY_LENGTHS && tagLen == AES_TAG_LEN && ivLen == AES_IV_LEN && mode == GCM
    }
  }

  const AES_MAX_KEY_LEN := 32
  const AES_CIPHER_KEY_LENGTHS := {32, 24, 16};
  const AES_TAG_LEN := 16 as uint8;
  const AES_IV_LEN := 12 as uint8;

  const AES_GCM_128 := EncryptionSuite(AES(GCM), 16, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_192 := EncryptionSuite(AES(GCM), 24, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_256 := EncryptionSuite(AES(GCM), 32, AES_TAG_LEN, AES_IV_LEN)

  function method Translate(suite: AlgorithmSuites.AlgorithmSuite)
    :(res: Result<EncryptionSuite, string>)
    ensures res.Success?
    ==>
      && res.value.Valid()
  {
    match suite.keyLen
      case 16 => Success(AES_GCM_128)
      case 24 => Success(AES_GCM_192)
      case 32 => Success(AES_GCM_256)
      case _ => Failure("Unsupported")
  }

}
