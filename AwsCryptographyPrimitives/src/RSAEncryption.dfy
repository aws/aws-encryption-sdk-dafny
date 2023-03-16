// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  method GenerateKeyPair(lengthBits: Types.RSAModulusLengthBitsToGenerate)
      returns (publicKey: Types.RSAPublicKey, privateKey: Types.RSAPrivateKey)
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(lengthBits);
    privateKey := Types.RSAPrivateKey(pem := pemPrivate, lengthBits := lengthBits);
    publicKey := Types.RSAPublicKey(pem := pemPublic, lengthBits := lengthBits);
  }

  method GetRSAKeyModulusLength(publicKey: seq<uint8>)
      returns (res: Result<Types.RSAModulusLengthBits, Types.Error>)
  {
    var length :- GetRSAKeyModulusLengthExtern(publicKey);
    :- Need(81 <= length as int < INT32_MAX_LIMIT,
        Types.AwsCryptographicPrimitivesError(message := "Unsupported length for RSA modulus."));
    return Success(length as int32);
  }

  method Decrypt(input: Types.RSADecryptInput)
    returns (output: Result<seq<uint8>, Types.Error>)
  {
    :- Need(0 < |input.privateKey| && 0 < |input.cipherText|, Types.AwsCryptographicPrimitivesError( message := ""));
    output := DecryptExtern(input.padding, input.privateKey, input.cipherText);
  }

  method Encrypt(input: Types.RSAEncryptInput)
    returns (output: Result<seq<uint8>, Types.Error>)
  {
    :- Need(0 < |input.publicKey| && 0 < |input.plaintext|, Types.AwsCryptographicPrimitivesError( message := ""));
    output := EncryptExtern(input.padding, input.publicKey, input.plaintext);
  }

  method {:extern "RSAEncryption.RSA", "GenerateKeyPairExtern"} GenerateKeyPairExtern(lengthBits: Types.RSAModulusLengthBitsToGenerate)
      returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    ensures |publicKey| > 0
    ensures |privateKey| > 0

  method {:extern "RSAEncryption.RSA", "GetRSAKeyModulusLengthExtern"} GetRSAKeyModulusLengthExtern(publicKey: seq<uint8>)
      returns (length: Result<uint32, Types.Error>)

  method {:extern "RSAEncryption.RSA", "DecryptExtern"} DecryptExtern(padding: Types.RSAPaddingMode, privateKey: seq<uint8>,
                                                                      cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |privateKey| > 0
    requires |cipherText| > 0

  method {:extern "RSAEncryption.RSA", "EncryptExtern"} EncryptExtern(padding: Types.RSAPaddingMode, publicKey: seq<uint8>,
                                                                      plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
}
