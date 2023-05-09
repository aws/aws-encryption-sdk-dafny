// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace AWS.Cryptography.Primitives {
 public static class TypeConversion {
 internal static AWS.Cryptography.Primitives.AESDecryptInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput (software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput)value; AWS.Cryptography.Primitives.AESDecryptInput converted = new AWS.Cryptography.Primitives.AESDecryptInput();  converted.EncAlg = (AWS.Cryptography.Primitives.AES_GCM) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M6_encAlg(concrete._encAlg);
  converted.Key = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_key(concrete._key);
  converted.CipherTxt = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M9_cipherTxt(concrete._cipherTxt);
  converted.AuthTag = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M7_authTag(concrete._authTag);
  converted.Iv = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M2_iv(concrete._iv);
  converted.Aad = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_aad(concrete._aad); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput (AWS.Cryptography.Primitives.AESDecryptInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M6_encAlg(value.EncAlg) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_key(value.Key) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M9_cipherTxt(value.CipherTxt) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M7_authTag(value.AuthTag) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M2_iv(value.Iv) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_aad(value.Aad) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput__M9_plaintext(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput__M9_plaintext(value);
}
 internal static AWS.Cryptography.Primitives.AESEncryptInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput (software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput)value; AWS.Cryptography.Primitives.AESEncryptInput converted = new AWS.Cryptography.Primitives.AESEncryptInput();  converted.EncAlg = (AWS.Cryptography.Primitives.AES_GCM) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M6_encAlg(concrete._encAlg);
  converted.Iv = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M2_iv(concrete._iv);
  converted.Key = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_key(concrete._key);
  converted.Msg = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_msg(concrete._msg);
  converted.Aad = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_aad(concrete._aad); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput (AWS.Cryptography.Primitives.AESEncryptInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M6_encAlg(value.EncAlg) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M2_iv(value.Iv) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_key(value.Key) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_msg(value.Msg) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_aad(value.Aad) ) ;
}
 internal static AWS.Cryptography.Primitives.AESEncryptOutput FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput (software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput value) {
 software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput concrete = (software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput)value; AWS.Cryptography.Primitives.AESEncryptOutput converted = new AWS.Cryptography.Primitives.AESEncryptOutput();  converted.CipherText = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M10_cipherText(concrete._cipherText);
  converted.AuthTag = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M7_authTag(concrete._authTag); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput (AWS.Cryptography.Primitives.AESEncryptOutput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M10_cipherText(value.CipherText) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M7_authTag(value.AuthTag) ) ;
}
 internal static AWS.Cryptography.Primitives.AesKdfCtrInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput (software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput)value; AWS.Cryptography.Primitives.AesKdfCtrInput converted = new AWS.Cryptography.Primitives.AesKdfCtrInput();  converted.Ikm = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M3_ikm(concrete._ikm);
  converted.ExpectedLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M14_expectedLength(concrete._expectedLength);
 if (concrete._nonce.is_Some) converted.Nonce = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M5_nonce(concrete._nonce); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput (AWS.Cryptography.Primitives.AesKdfCtrInput value) {
 System.IO.MemoryStream var_nonce = value.IsSetNonce() ? value.Nonce : (System.IO.MemoryStream) null;
 return new software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M3_ikm(value.Ikm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M14_expectedLength(value.ExpectedLength) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M5_nonce(var_nonce) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput__M3_okm(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput__M3_okm(value);
}
 internal static AWS.Cryptography.Primitives.AwsCryptographicPrimitivesError FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError (software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError value) {
 return new AWS.Cryptography.Primitives.AwsCryptographicPrimitivesError (
 FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError__M7_message(value._message)
 ) ;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError (AWS.Cryptography.Primitives.AwsCryptographicPrimitivesError value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError (
 ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError__M7_message(value.Message)
 ) ;
}
 internal static AWS.Cryptography.Primitives.CryptoConfig FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_CryptoConfig (software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig value) {
 software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig concrete = (software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig)value; AWS.Cryptography.Primitives.CryptoConfig converted = new AWS.Cryptography.Primitives.CryptoConfig();  return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_CryptoConfig (AWS.Cryptography.Primitives.CryptoConfig value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig (  ) ;
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 if (value.is_SHA__512) return AWS.Cryptography.Primitives.DigestAlgorithm.SHA_512;
 if (value.is_SHA__384) return AWS.Cryptography.Primitives.DigestAlgorithm.SHA_384;
 if (value.is_SHA__256) return AWS.Cryptography.Primitives.DigestAlgorithm.SHA_256;
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.DigestAlgorithm value");
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 if (AWS.Cryptography.Primitives.DigestAlgorithm.SHA_512.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__512();
 if (AWS.Cryptography.Primitives.DigestAlgorithm.SHA_384.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__384();
 if (AWS.Cryptography.Primitives.DigestAlgorithm.SHA_256.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256();
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.DigestAlgorithm value");
}
 internal static AWS.Cryptography.Primitives.DigestInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput (software.amazon.cryptography.primitives.internaldafny.types._IDigestInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.DigestInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.DigestInput)value; AWS.Cryptography.Primitives.DigestInput converted = new AWS.Cryptography.Primitives.DigestInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M15_digestAlgorithm(concrete._digestAlgorithm);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M7_message(concrete._message); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput (AWS.Cryptography.Primitives.DigestInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.DigestInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M7_message(value.Message) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput__M6_digest(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput__M6_digest(value);
}
 internal static AWS.Cryptography.Primitives.ECDSASignatureAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm value) {
 if (value.is_ECDSA__P384) return AWS.Cryptography.Primitives.ECDSASignatureAlgorithm.ECDSA_P384;
 if (value.is_ECDSA__P256) return AWS.Cryptography.Primitives.ECDSASignatureAlgorithm.ECDSA_P256;
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value");
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value) {
 if (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm.ECDSA_P384.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.create_ECDSA__P384();
 if (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm.ECDSA_P256.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.create_ECDSA__P256();
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value");
}
 internal static AWS.Cryptography.Primitives.ECDSASignInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput)value; AWS.Cryptography.Primitives.ECDSASignInput converted = new AWS.Cryptography.Primitives.ECDSASignInput();  converted.SignatureAlgorithm = (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M18_signatureAlgorithm(concrete._signatureAlgorithm);
  converted.SigningKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M10_signingKey(concrete._signingKey);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M7_message(concrete._message); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput (AWS.Cryptography.Primitives.ECDSASignInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M18_signatureAlgorithm(value.SignatureAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M10_signingKey(value.SigningKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M7_message(value.Message) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput__M9_signature(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput__M9_signature(value);
}
 internal static AWS.Cryptography.Primitives.ECDSAVerifyInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput (software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput)value; AWS.Cryptography.Primitives.ECDSAVerifyInput converted = new AWS.Cryptography.Primitives.ECDSAVerifyInput();  converted.SignatureAlgorithm = (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M18_signatureAlgorithm(concrete._signatureAlgorithm);
  converted.VerificationKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M15_verificationKey(concrete._verificationKey);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M7_message(concrete._message);
  converted.Signature = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M9_signature(concrete._signature); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput (AWS.Cryptography.Primitives.ECDSAVerifyInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M18_signatureAlgorithm(value.SignatureAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M15_verificationKey(value.VerificationKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M7_message(value.Message) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M9_signature(value.Signature) ) ;
}
 internal static bool FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput (bool value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput__M7_success(value);
}
 internal static bool ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput (bool value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput__M7_success(value);
}
 internal static AWS.Cryptography.Primitives.GenerateECDSASignatureKeyInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput (software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput)value; AWS.Cryptography.Primitives.GenerateECDSASignatureKeyInput converted = new AWS.Cryptography.Primitives.GenerateECDSASignatureKeyInput();  converted.SignatureAlgorithm = (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput__M18_signatureAlgorithm(concrete._signatureAlgorithm); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput (AWS.Cryptography.Primitives.GenerateECDSASignatureKeyInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput__M18_signatureAlgorithm(value.SignatureAlgorithm) ) ;
}
 internal static AWS.Cryptography.Primitives.GenerateECDSASignatureKeyOutput FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput (software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput)value; AWS.Cryptography.Primitives.GenerateECDSASignatureKeyOutput converted = new AWS.Cryptography.Primitives.GenerateECDSASignatureKeyOutput();  converted.SignatureAlgorithm = (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M18_signatureAlgorithm(concrete._signatureAlgorithm);
  converted.VerificationKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M15_verificationKey(concrete._verificationKey);
  converted.SigningKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M10_signingKey(concrete._signingKey); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput (AWS.Cryptography.Primitives.GenerateECDSASignatureKeyOutput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M18_signatureAlgorithm(value.SignatureAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M15_verificationKey(value.VerificationKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M10_signingKey(value.SigningKey) ) ;
}
 internal static AWS.Cryptography.Primitives.GenerateRandomBytesInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput (software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput)value; AWS.Cryptography.Primitives.GenerateRandomBytesInput converted = new AWS.Cryptography.Primitives.GenerateRandomBytesInput();  converted.Length = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput__M6_length(concrete._length); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput (AWS.Cryptography.Primitives.GenerateRandomBytesInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput__M6_length(value.Length) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput__M4_data(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput__M4_data(value);
}
 internal static AWS.Cryptography.Primitives.GenerateRSAKeyPairInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput (software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput)value; AWS.Cryptography.Primitives.GenerateRSAKeyPairInput converted = new AWS.Cryptography.Primitives.GenerateRSAKeyPairInput();  converted.LengthBits = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput__M10_lengthBits(concrete._lengthBits); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput (AWS.Cryptography.Primitives.GenerateRSAKeyPairInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput__M10_lengthBits(value.LengthBits) ) ;
}
 internal static AWS.Cryptography.Primitives.GenerateRSAKeyPairOutput FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput (software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput)value; AWS.Cryptography.Primitives.GenerateRSAKeyPairOutput converted = new AWS.Cryptography.Primitives.GenerateRSAKeyPairOutput();  converted.PublicKey = (AWS.Cryptography.Primitives.RSAPublicKey) FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M9_publicKey(concrete._publicKey);
  converted.PrivateKey = (AWS.Cryptography.Primitives.RSAPrivateKey) FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M10_privateKey(concrete._privateKey); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput (AWS.Cryptography.Primitives.GenerateRSAKeyPairOutput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M9_publicKey(value.PublicKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M10_privateKey(value.PrivateKey) ) ;
}
 internal static AWS.Cryptography.Primitives.GetRSAKeyModulusLengthInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput (software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput)value; AWS.Cryptography.Primitives.GetRSAKeyModulusLengthInput converted = new AWS.Cryptography.Primitives.GetRSAKeyModulusLengthInput();  converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput__M9_publicKey(concrete._publicKey); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput (AWS.Cryptography.Primitives.GetRSAKeyModulusLengthInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput__M9_publicKey(value.PublicKey) ) ;
}
 internal static AWS.Cryptography.Primitives.GetRSAKeyModulusLengthOutput FromDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput (software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput value) {
 software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput concrete = (software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput)value; AWS.Cryptography.Primitives.GetRSAKeyModulusLengthOutput converted = new AWS.Cryptography.Primitives.GetRSAKeyModulusLengthOutput();  converted.Length = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput__M6_length(concrete._length); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput ToDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput (AWS.Cryptography.Primitives.GetRSAKeyModulusLengthOutput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput__M6_length(value.Length) ) ;
}
 internal static AWS.Cryptography.Primitives.HkdfExpandInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput (software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput)value; AWS.Cryptography.Primitives.HkdfExpandInput converted = new AWS.Cryptography.Primitives.HkdfExpandInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M15_digestAlgorithm(concrete._digestAlgorithm);
  converted.Prk = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M3_prk(concrete._prk);
  converted.Info = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M4_info(concrete._info);
  converted.ExpectedLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M14_expectedLength(concrete._expectedLength); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput (AWS.Cryptography.Primitives.HkdfExpandInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M3_prk(value.Prk) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M4_info(value.Info) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M14_expectedLength(value.ExpectedLength) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput__M3_okm(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput__M3_okm(value);
}
 internal static AWS.Cryptography.Primitives.HkdfExtractInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput (software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput)value; AWS.Cryptography.Primitives.HkdfExtractInput converted = new AWS.Cryptography.Primitives.HkdfExtractInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M15_digestAlgorithm(concrete._digestAlgorithm);
 if (concrete._salt.is_Some) converted.Salt = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M4_salt(concrete._salt);
  converted.Ikm = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M3_ikm(concrete._ikm); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput (AWS.Cryptography.Primitives.HkdfExtractInput value) {
 System.IO.MemoryStream var_salt = value.IsSetSalt() ? value.Salt : (System.IO.MemoryStream) null;
 return new software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M4_salt(var_salt) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M3_ikm(value.Ikm) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput__M3_prk(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput__M3_prk(value);
}
 internal static AWS.Cryptography.Primitives.HkdfInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput (software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.HkdfInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.HkdfInput)value; AWS.Cryptography.Primitives.HkdfInput converted = new AWS.Cryptography.Primitives.HkdfInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M15_digestAlgorithm(concrete._digestAlgorithm);
 if (concrete._salt.is_Some) converted.Salt = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_salt(concrete._salt);
  converted.Ikm = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M3_ikm(concrete._ikm);
  converted.Info = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_info(concrete._info);
  converted.ExpectedLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M14_expectedLength(concrete._expectedLength); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput (AWS.Cryptography.Primitives.HkdfInput value) {
 System.IO.MemoryStream var_salt = value.IsSetSalt() ? value.Salt : (System.IO.MemoryStream) null;
 return new software.amazon.cryptography.primitives.internaldafny.types.HkdfInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_salt(var_salt) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M3_ikm(value.Ikm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_info(value.Info) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M14_expectedLength(value.ExpectedLength) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput__M3_okm(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput__M3_okm(value);
}
 internal static AWS.Cryptography.Primitives.HMacInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput (software.amazon.cryptography.primitives.internaldafny.types._IHMacInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.HMacInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.HMacInput)value; AWS.Cryptography.Primitives.HMacInput converted = new AWS.Cryptography.Primitives.HMacInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M15_digestAlgorithm(concrete._digestAlgorithm);
  converted.Key = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M3_key(concrete._key);
  converted.Message = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M7_message(concrete._message); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IHMacInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput (AWS.Cryptography.Primitives.HMacInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.HMacInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M3_key(value.Key) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M7_message(value.Message) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput__M6_digest(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput__M6_digest(value);
}
 internal static AWS.Cryptography.Primitives.KdfCtrInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput (software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput)value; AWS.Cryptography.Primitives.KdfCtrInput converted = new AWS.Cryptography.Primitives.KdfCtrInput();  converted.DigestAlgorithm = (AWS.Cryptography.Primitives.DigestAlgorithm) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M15_digestAlgorithm(concrete._digestAlgorithm);
  converted.Ikm = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M3_ikm(concrete._ikm);
  converted.ExpectedLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M14_expectedLength(concrete._expectedLength);
 if (concrete._purpose.is_Some) converted.Purpose = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M7_purpose(concrete._purpose);
 if (concrete._nonce.is_Some) converted.Nonce = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M5_nonce(concrete._nonce); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput (AWS.Cryptography.Primitives.KdfCtrInput value) {
 System.IO.MemoryStream var_purpose = value.IsSetPurpose() ? value.Purpose : (System.IO.MemoryStream) null;
 System.IO.MemoryStream var_nonce = value.IsSetNonce() ? value.Nonce : (System.IO.MemoryStream) null;
 return new software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M15_digestAlgorithm(value.DigestAlgorithm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M3_ikm(value.Ikm) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M14_expectedLength(value.ExpectedLength) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M7_purpose(var_purpose) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M5_nonce(var_nonce) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput__M3_okm(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput__M3_okm(value);
}
 internal static AWS.Cryptography.Primitives.RSADecryptInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput (software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput)value; AWS.Cryptography.Primitives.RSADecryptInput converted = new AWS.Cryptography.Primitives.RSADecryptInput();  converted.Padding = (AWS.Cryptography.Primitives.RSAPaddingMode) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M7_padding(concrete._padding);
  converted.PrivateKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_privateKey(concrete._privateKey);
  converted.CipherText = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_cipherText(concrete._cipherText); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput (AWS.Cryptography.Primitives.RSADecryptInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M7_padding(value.Padding) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_privateKey(value.PrivateKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_cipherText(value.CipherText) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput__M9_plaintext(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput__M9_plaintext(value);
}
 internal static AWS.Cryptography.Primitives.RSAEncryptInput FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput (software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput value) {
 software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput concrete = (software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput)value; AWS.Cryptography.Primitives.RSAEncryptInput converted = new AWS.Cryptography.Primitives.RSAEncryptInput();  converted.Padding = (AWS.Cryptography.Primitives.RSAPaddingMode) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M7_padding(concrete._padding);
  converted.PublicKey = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_publicKey(concrete._publicKey);
  converted.Plaintext = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_plaintext(concrete._plaintext); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput (AWS.Cryptography.Primitives.RSAEncryptInput value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M7_padding(value.Padding) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_publicKey(value.PublicKey) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_plaintext(value.Plaintext) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput (Dafny.ISequence<byte> value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput__M10_cipherText(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput (System.IO.MemoryStream value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput__M10_cipherText(value);
}
 internal static AWS.Cryptography.Primitives.RSAPaddingMode FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode value) {
 if (value.is_PKCS1) return AWS.Cryptography.Primitives.RSAPaddingMode.PKCS1;
 if (value.is_OAEP__SHA1) return AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA1;
 if (value.is_OAEP__SHA256) return AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA256;
 if (value.is_OAEP__SHA384) return AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA384;
 if (value.is_OAEP__SHA512) return AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA512;
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.RSAPaddingMode value");
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode (AWS.Cryptography.Primitives.RSAPaddingMode value) {
 if (AWS.Cryptography.Primitives.RSAPaddingMode.PKCS1.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_PKCS1();
 if (AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA1.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_OAEP__SHA1();
 if (AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA256.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_OAEP__SHA256();
 if (AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA384.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_OAEP__SHA384();
 if (AWS.Cryptography.Primitives.RSAPaddingMode.OAEP_SHA512.Equals(value)) return software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_OAEP__SHA512();
throw new System.ArgumentException("Invalid AWS.Cryptography.Primitives.RSAPaddingMode value");
}
 internal static AWS.Cryptography.Primitives.AES_GCM FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M6_encAlg (software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M6_encAlg (AWS.Cryptography.Primitives.AES_GCM value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_key (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_key (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M9_cipherTxt (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M9_cipherTxt (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M7_authTag (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M7_authTag (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M2_iv (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M2_iv (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_aad (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput__M3_aad (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput__M9_plaintext (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput__M9_plaintext (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.AES_GCM FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M6_encAlg (software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M6_encAlg (AWS.Cryptography.Primitives.AES_GCM value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M2_iv (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M2_iv (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_key (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_key (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_msg (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_msg (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_aad (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput__M3_aad (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M10_cipherText (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M10_cipherText (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M7_authTag (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput__M7_authTag (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M3_ikm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M3_ikm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M14_expectedLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M14_expectedLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M5_nonce (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_AesKdfCtrInput__M5_nonce (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput__M3_okm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AesKdfCtrOutput__M3_okm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static string FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError__M7_message (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError__M7_message (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M7_message (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput__M7_message (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput__M6_digest (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput__M6_digest (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.ECDSASignatureAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M18_signatureAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M18_signatureAlgorithm (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M10_signingKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M10_signingKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M7_message (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_ECDSASignInput__M7_message (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput__M9_signature (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_ECDSASignOutput__M9_signature (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.ECDSASignatureAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M18_signatureAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M18_signatureAlgorithm (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M15_verificationKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M15_verificationKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M7_message (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M7_message (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M9_signature (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_ECDSAVerifyInput__M9_signature (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static bool FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput__M7_success (bool value) {
 return FromDafny_N6_smithy__N3_api__S7_Boolean(value);
}
 internal static bool ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_ECDSAVerifyOutput__M7_success (bool value) {
 return ToDafny_N6_smithy__N3_api__S7_Boolean(value);
}
 internal static AWS.Cryptography.Primitives.ECDSASignatureAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput__M18_signatureAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S30_GenerateECDSASignatureKeyInput__M18_signatureAlgorithm (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static AWS.Cryptography.Primitives.ECDSASignatureAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M18_signatureAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M18_signatureAlgorithm (AWS.Cryptography.Primitives.ECDSASignatureAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_ECDSASignatureAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M15_verificationKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M15_verificationKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M10_signingKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_GenerateECDSASignatureKeyOutput__M10_signingKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput__M6_length (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput__M6_length (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput__M4_data (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput__M4_data (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput__M10_lengthBits (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S30_RSAModulusLengthBitsToGenerate(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S23_GenerateRSAKeyPairInput__M10_lengthBits (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S30_RSAModulusLengthBitsToGenerate(value);
}
 internal static AWS.Cryptography.Primitives.RSAPublicKey FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M9_publicKey (software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M9_publicKey (AWS.Cryptography.Primitives.RSAPublicKey value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey(value);
}
 internal static AWS.Cryptography.Primitives.RSAPrivateKey FromDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M10_privateKey (software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRSAKeyPairOutput__M10_privateKey (AWS.Cryptography.Primitives.RSAPrivateKey value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput__M9_publicKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S27_GetRSAKeyModulusLengthInput__M9_publicKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput__M6_length (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S28_GetRSAKeyModulusLengthOutput__M6_length (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M3_prk (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M3_prk (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M4_info (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M4_info (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M14_expectedLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput__M14_expectedLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput__M3_okm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput__M3_okm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M4_salt (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M4_salt (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M3_ikm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput__M3_ikm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput__M3_prk (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput__M3_prk (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_salt (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_salt (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M3_ikm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M3_ikm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_info (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M4_info (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M14_expectedLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput__M14_expectedLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput__M3_okm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput__M3_okm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M3_key (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M3_key (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M7_message (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput__M7_message (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput__M6_digest (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput__M6_digest (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.DigestAlgorithm FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M15_digestAlgorithm (software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M15_digestAlgorithm (AWS.Cryptography.Primitives.DigestAlgorithm value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_DigestAlgorithm(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M3_ikm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M3_ikm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M14_expectedLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M14_expectedLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M7_purpose (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M7_purpose (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M5_nonce (Wrappers_Compile._IOption<Dafny.ISequence<byte>> value) {
 return value.is_None ? (System.IO.MemoryStream) null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_KdfCtrInput__M5_nonce (System.IO.MemoryStream value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream) value));
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput__M3_okm (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_KdfCtrOutput__M3_okm (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.RSAPaddingMode FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M7_padding (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M7_padding (AWS.Cryptography.Primitives.RSAPaddingMode value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_privateKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_privateKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_cipherText (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSADecryptInput__M10_cipherText (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput__M9_plaintext (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSADecryptOutput__M9_plaintext (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.RSAPaddingMode FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M7_padding (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode(value);
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M7_padding (AWS.Cryptography.Primitives.RSAPaddingMode value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S14_RSAPaddingMode(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_publicKey (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_publicKey (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_plaintext (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_RSAEncryptInput__M9_plaintext (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput__M10_cipherText (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_RSAEncryptOutput__M10_cipherText (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static AWS.Cryptography.Primitives.AES_GCM FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM (software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM value) {
 software.amazon.cryptography.primitives.internaldafny.types.AES__GCM concrete = (software.amazon.cryptography.primitives.internaldafny.types.AES__GCM)value; AWS.Cryptography.Primitives.AES_GCM converted = new AWS.Cryptography.Primitives.AES_GCM();  converted.KeyLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_keyLength(concrete._keyLength);
  converted.TagLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_tagLength(concrete._tagLength);
  converted.IvLength = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M8_ivLength(concrete._ivLength); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM (AWS.Cryptography.Primitives.AES_GCM value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.AES__GCM ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_keyLength(value.KeyLength) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_tagLength(value.TagLength) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M8_ivLength(value.IvLength) ) ;
}
 internal static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob (Dafny.ISequence<byte> value) {
 return new System.IO.MemoryStream(value.Elements);
}
 internal static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob (System.IO.MemoryStream value) {
 return Dafny.Sequence<byte>.FromArray(value.ToArray());
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_PositiveInteger (int value) {
 return value;
}
 internal static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static bool FromDafny_N6_smithy__N3_api__S7_Boolean (bool value) {
 return value;
}
 internal static bool ToDafny_N6_smithy__N3_api__S7_Boolean (bool value) {
 return value;
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S30_RSAModulusLengthBitsToGenerate (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S30_RSAModulusLengthBitsToGenerate (int value) {
 return value;
}
 internal static AWS.Cryptography.Primitives.RSAPublicKey FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey (software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey value) {
 software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey concrete = (software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey)value; AWS.Cryptography.Primitives.RSAPublicKey converted = new AWS.Cryptography.Primitives.RSAPublicKey();  converted.LengthBits = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M10_lengthBits(concrete._lengthBits);
  converted.Pem = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M3_pem(concrete._pem); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey (AWS.Cryptography.Primitives.RSAPublicKey value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M10_lengthBits(value.LengthBits) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M3_pem(value.Pem) ) ;
}
 internal static AWS.Cryptography.Primitives.RSAPrivateKey FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey (software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey value) {
 software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey concrete = (software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey)value; AWS.Cryptography.Primitives.RSAPrivateKey converted = new AWS.Cryptography.Primitives.RSAPrivateKey();  converted.LengthBits = (int) FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M10_lengthBits(concrete._lengthBits);
  converted.Pem = (System.IO.MemoryStream) FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M3_pem(concrete._pem); return converted;
}
 internal static software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey (AWS.Cryptography.Primitives.RSAPrivateKey value) {

 return new software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey ( ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M10_lengthBits(value.LengthBits) , ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M3_pem(value.Pem) ) ;
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits (int value) {
 return value;
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_keyLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S18_SymmetricKeyLength(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_keyLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S18_SymmetricKeyLength(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_tagLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_Uint8Bytes(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M9_tagLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_Uint8Bytes(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M8_ivLength (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_Uint8Bits(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S7_AES_GCM__M8_ivLength (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_Uint8Bits(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M10_lengthBits (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M10_lengthBits (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M3_pem (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S12_RSAPublicKey__M3_pem (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M10_lengthBits (int value) {
 return FromDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M10_lengthBits (int value) {
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S20_RSAModulusLengthBits(value);
}
 internal static System.IO.MemoryStream FromDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M3_pem (Dafny.ISequence<byte> value) {
 return FromDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static Dafny.ISequence<byte> ToDafny_N3_aws__N12_cryptography__N10_primitives__S13_RSAPrivateKey__M3_pem (System.IO.MemoryStream value) {
 return ToDafny_N6_smithy__N3_api__S4_Blob(value);
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S18_SymmetricKeyLength (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S18_SymmetricKeyLength (int value) {
 return value;
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_Uint8Bytes (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S10_Uint8Bytes (int value) {
 return value;
}
 internal static int FromDafny_N3_aws__N12_cryptography__N10_primitives__S9_Uint8Bits (int value) {
 return value;
}
 internal static int ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_Uint8Bits (int value) {
 return value;
}
 public static System.Exception FromDafny_CommonError(software.amazon.cryptography.primitives.internaldafny.types._IError value) {
 switch(value)
 {

 case software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError dafnyVal:
return FromDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError(dafnyVal);
 case software.amazon.cryptography.primitives.internaldafny.types.Error_CollectionOfErrors dafnyVal:
 return new CollectionOfErrors(new System.Collections.Generic.List<Exception>(dafnyVal._list.Elements.Select(x => TypeConversion.FromDafny_CommonError(x))));
 case software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static software.amazon.cryptography.primitives.internaldafny.types._IError ToDafny_CommonError(System.Exception value) {

 switch (value)
 {
 case AWS.Cryptography.Primitives.AwsCryptographicPrimitivesError exception:
 return ToDafny_N3_aws__N12_cryptography__N10_primitives__S31_AwsCryptographicPrimitivesError(exception);
 case CollectionOfErrors collectionOfErrors:
 return new software.amazon.cryptography.primitives.internaldafny.types.Error_CollectionOfErrors(
     Dafny.Sequence<software.amazon.cryptography.primitives.internaldafny.types._IError>
     .FromArray(
         collectionOfErrors.list.Select
             (x => TypeConversion.ToDafny_CommonError(x))
         .ToArray()
     )
 );

 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque(exception);
 case System.Exception exception:
 return new software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque(value);
}
}
}
}
