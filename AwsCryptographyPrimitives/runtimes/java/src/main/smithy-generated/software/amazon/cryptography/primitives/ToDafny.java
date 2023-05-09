// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives;

import Wrappers_Compile.Option;
import dafny.DafnySequence;
import java.lang.Boolean;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Integer;
import java.lang.RuntimeException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput;
import software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput;
import software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput;
import software.amazon.cryptography.primitives.internaldafny.types.AES__CTR;
import software.amazon.cryptography.primitives.internaldafny.types.AES__GCM;
import software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput;
import software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig;
import software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.DigestInput;
import software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput;
import software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput;
import software.amazon.cryptography.primitives.internaldafny.types.Error;
import software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError;
import software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput;
import software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput;
import software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput;
import software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput;
import software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput;
import software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput;
import software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput;
import software.amazon.cryptography.primitives.internaldafny.types.HMacInput;
import software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput;
import software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput;
import software.amazon.cryptography.primitives.internaldafny.types.HkdfInput;
import software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient;
import software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput;
import software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput;
import software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput;
import software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode;
import software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey;
import software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey;
import software.amazon.cryptography.primitives.model.AES_CTR;
import software.amazon.cryptography.primitives.model.AES_GCM;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;
import software.amazon.cryptography.primitives.model.CollectionOfErrors;
import software.amazon.cryptography.primitives.model.OpaqueError;

public class ToDafny {
  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof AwsCryptographicPrimitivesError) {
      return ToDafny.Error((AwsCryptographicPrimitivesError) nativeValue);
    }
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list = software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(), 
        ToDafny::Error, 
        Error._typeDescriptor());
    return Error.create_CollectionOfErrors(list);
  }

  public static AES__CTR AES_CTR(AES_CTR nativeValue) {
    Integer keyLength;
    keyLength = (nativeValue.keyLength());
    Integer nonceLength;
    nonceLength = (nativeValue.nonceLength());
    return new AES__CTR(keyLength, nonceLength);
  }

  public static AES__GCM AES_GCM(AES_GCM nativeValue) {
    Integer keyLength;
    keyLength = (nativeValue.keyLength());
    Integer tagLength;
    tagLength = (nativeValue.tagLength());
    Integer ivLength;
    ivLength = (nativeValue.ivLength());
    return new AES__GCM(keyLength, tagLength, ivLength);
  }

  public static AESDecryptInput AESDecryptInput(
      software.amazon.cryptography.primitives.model.AESDecryptInput nativeValue) {
    AES__GCM encAlg;
    encAlg = ToDafny.AES_GCM(nativeValue.encAlg());
    DafnySequence<? extends Byte> key;
    key = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.key());
    DafnySequence<? extends Byte> cipherTxt;
    cipherTxt = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.cipherTxt());
    DafnySequence<? extends Byte> authTag;
    authTag = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.authTag());
    DafnySequence<? extends Byte> iv;
    iv = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.iv());
    DafnySequence<? extends Byte> aad;
    aad = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.aad());
    return new AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad);
  }

  public static DafnySequence<? extends Byte> AESDecryptOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> plaintext;
    plaintext = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return plaintext;
  }

  public static AESEncryptInput AESEncryptInput(
      software.amazon.cryptography.primitives.model.AESEncryptInput nativeValue) {
    AES__GCM encAlg;
    encAlg = ToDafny.AES_GCM(nativeValue.encAlg());
    DafnySequence<? extends Byte> iv;
    iv = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.iv());
    DafnySequence<? extends Byte> key;
    key = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.key());
    DafnySequence<? extends Byte> msg;
    msg = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.msg());
    DafnySequence<? extends Byte> aad;
    aad = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.aad());
    return new AESEncryptInput(encAlg, iv, key, msg, aad);
  }

  public static AESEncryptOutput AESEncryptOutput(
      software.amazon.cryptography.primitives.model.AESEncryptOutput nativeValue) {
    DafnySequence<? extends Byte> cipherText;
    cipherText = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.cipherText());
    DafnySequence<? extends Byte> authTag;
    authTag = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.authTag());
    return new AESEncryptOutput(cipherText, authTag);
  }

  public static AesKdfCtrInput AesKdfCtrInput(
      software.amazon.cryptography.primitives.model.AesKdfCtrInput nativeValue) {
    DafnySequence<? extends Byte> ikm;
    ikm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ikm());
    Integer expectedLength;
    expectedLength = (nativeValue.expectedLength());
    Option<DafnySequence<? extends Byte>> nonce;
    nonce = Objects.nonNull(nativeValue.nonce()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.nonce()))
        : Option.create_None();
    return new AesKdfCtrInput(ikm, expectedLength, nonce);
  }

  public static DafnySequence<? extends Byte> AesKdfCtrOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> okm;
    okm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return okm;
  }

  public static CryptoConfig CryptoConfig(
      software.amazon.cryptography.primitives.model.CryptoConfig nativeValue) {
    return new CryptoConfig();
  }

  public static DigestInput DigestInput(
      software.amazon.cryptography.primitives.model.DigestInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    DafnySequence<? extends Byte> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.message());
    return new DigestInput(digestAlgorithm, message);
  }

  public static DafnySequence<? extends Byte> DigestOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> digest;
    digest = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return digest;
  }

  public static ECDSASignInput ECDSASignInput(
      software.amazon.cryptography.primitives.model.ECDSASignInput nativeValue) {
    ECDSASignatureAlgorithm signatureAlgorithm;
    signatureAlgorithm = ToDafny.ECDSASignatureAlgorithm(nativeValue.signatureAlgorithm());
    DafnySequence<? extends Byte> signingKey;
    signingKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey());
    DafnySequence<? extends Byte> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.message());
    return new ECDSASignInput(signatureAlgorithm, signingKey, message);
  }

  public static DafnySequence<? extends Byte> ECDSASignOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> signature;
    signature = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return signature;
  }

  public static ECDSAVerifyInput ECDSAVerifyInput(
      software.amazon.cryptography.primitives.model.ECDSAVerifyInput nativeValue) {
    ECDSASignatureAlgorithm signatureAlgorithm;
    signatureAlgorithm = ToDafny.ECDSASignatureAlgorithm(nativeValue.signatureAlgorithm());
    DafnySequence<? extends Byte> verificationKey;
    verificationKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey());
    DafnySequence<? extends Byte> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.message());
    DafnySequence<? extends Byte> signature;
    signature = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signature());
    return new ECDSAVerifyInput(signatureAlgorithm, verificationKey, message, signature);
  }

  public static Boolean ECDSAVerifyOutput(Boolean nativeValue) {
    Boolean success;
    success = (nativeValue);
    return success;
  }

  public static GenerateECDSASignatureKeyInput GenerateECDSASignatureKeyInput(
      software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyInput nativeValue) {
    ECDSASignatureAlgorithm signatureAlgorithm;
    signatureAlgorithm = ToDafny.ECDSASignatureAlgorithm(nativeValue.signatureAlgorithm());
    return new GenerateECDSASignatureKeyInput(signatureAlgorithm);
  }

  public static GenerateECDSASignatureKeyOutput GenerateECDSASignatureKeyOutput(
      software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyOutput nativeValue) {
    ECDSASignatureAlgorithm signatureAlgorithm;
    signatureAlgorithm = ToDafny.ECDSASignatureAlgorithm(nativeValue.signatureAlgorithm());
    DafnySequence<? extends Byte> verificationKey;
    verificationKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.verificationKey());
    DafnySequence<? extends Byte> signingKey;
    signingKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.signingKey());
    return new GenerateECDSASignatureKeyOutput(signatureAlgorithm, verificationKey, signingKey);
  }

  public static GenerateRandomBytesInput GenerateRandomBytesInput(
      software.amazon.cryptography.primitives.model.GenerateRandomBytesInput nativeValue) {
    Integer length;
    length = (nativeValue.length());
    return new GenerateRandomBytesInput(length);
  }

  public static DafnySequence<? extends Byte> GenerateRandomBytesOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> data;
    data = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return data;
  }

  public static GenerateRSAKeyPairInput GenerateRSAKeyPairInput(
      software.amazon.cryptography.primitives.model.GenerateRSAKeyPairInput nativeValue) {
    Integer lengthBits;
    lengthBits = (nativeValue.lengthBits());
    return new GenerateRSAKeyPairInput(lengthBits);
  }

  public static GenerateRSAKeyPairOutput GenerateRSAKeyPairOutput(
      software.amazon.cryptography.primitives.model.GenerateRSAKeyPairOutput nativeValue) {
    RSAPublicKey publicKey;
    publicKey = ToDafny.RSAPublicKey(nativeValue.publicKey());
    RSAPrivateKey privateKey;
    privateKey = ToDafny.RSAPrivateKey(nativeValue.privateKey());
    return new GenerateRSAKeyPairOutput(publicKey, privateKey);
  }

  public static GetRSAKeyModulusLengthInput GetRSAKeyModulusLengthInput(
      software.amazon.cryptography.primitives.model.GetRSAKeyModulusLengthInput nativeValue) {
    DafnySequence<? extends Byte> publicKey;
    publicKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.publicKey());
    return new GetRSAKeyModulusLengthInput(publicKey);
  }

  public static GetRSAKeyModulusLengthOutput GetRSAKeyModulusLengthOutput(
      software.amazon.cryptography.primitives.model.GetRSAKeyModulusLengthOutput nativeValue) {
    Integer length;
    length = (nativeValue.length());
    return new GetRSAKeyModulusLengthOutput(length);
  }

  public static HkdfExpandInput HkdfExpandInput(
      software.amazon.cryptography.primitives.model.HkdfExpandInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    DafnySequence<? extends Byte> prk;
    prk = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.prk());
    DafnySequence<? extends Byte> info;
    info = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.info());
    Integer expectedLength;
    expectedLength = (nativeValue.expectedLength());
    return new HkdfExpandInput(digestAlgorithm, prk, info, expectedLength);
  }

  public static DafnySequence<? extends Byte> HkdfExpandOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> okm;
    okm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return okm;
  }

  public static HkdfExtractInput HkdfExtractInput(
      software.amazon.cryptography.primitives.model.HkdfExtractInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    Option<DafnySequence<? extends Byte>> salt;
    salt = Objects.nonNull(nativeValue.salt()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.salt()))
        : Option.create_None();
    DafnySequence<? extends Byte> ikm;
    ikm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ikm());
    return new HkdfExtractInput(digestAlgorithm, salt, ikm);
  }

  public static DafnySequence<? extends Byte> HkdfExtractOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> prk;
    prk = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return prk;
  }

  public static HkdfInput HkdfInput(
      software.amazon.cryptography.primitives.model.HkdfInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    Option<DafnySequence<? extends Byte>> salt;
    salt = Objects.nonNull(nativeValue.salt()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.salt()))
        : Option.create_None();
    DafnySequence<? extends Byte> ikm;
    ikm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ikm());
    DafnySequence<? extends Byte> info;
    info = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.info());
    Integer expectedLength;
    expectedLength = (nativeValue.expectedLength());
    return new HkdfInput(digestAlgorithm, salt, ikm, info, expectedLength);
  }

  public static DafnySequence<? extends Byte> HkdfOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> okm;
    okm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return okm;
  }

  public static HMacInput HMacInput(
      software.amazon.cryptography.primitives.model.HMacInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    DafnySequence<? extends Byte> key;
    key = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.key());
    DafnySequence<? extends Byte> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.message());
    return new HMacInput(digestAlgorithm, key, message);
  }

  public static DafnySequence<? extends Byte> HMacOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> digest;
    digest = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return digest;
  }

  public static KdfCtrInput KdfCtrInput(
      software.amazon.cryptography.primitives.model.KdfCtrInput nativeValue) {
    DigestAlgorithm digestAlgorithm;
    digestAlgorithm = ToDafny.DigestAlgorithm(nativeValue.digestAlgorithm());
    DafnySequence<? extends Byte> ikm;
    ikm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.ikm());
    Integer expectedLength;
    expectedLength = (nativeValue.expectedLength());
    Option<DafnySequence<? extends Byte>> purpose;
    purpose = Objects.nonNull(nativeValue.purpose()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.purpose()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> nonce;
    nonce = Objects.nonNull(nativeValue.nonce()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.nonce()))
        : Option.create_None();
    return new KdfCtrInput(digestAlgorithm, ikm, expectedLength, purpose, nonce);
  }

  public static DafnySequence<? extends Byte> KdfCtrOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> okm;
    okm = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return okm;
  }

  public static RSADecryptInput RSADecryptInput(
      software.amazon.cryptography.primitives.model.RSADecryptInput nativeValue) {
    RSAPaddingMode padding;
    padding = ToDafny.RSAPaddingMode(nativeValue.padding());
    DafnySequence<? extends Byte> privateKey;
    privateKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.privateKey());
    DafnySequence<? extends Byte> cipherText;
    cipherText = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.cipherText());
    return new RSADecryptInput(padding, privateKey, cipherText);
  }

  public static DafnySequence<? extends Byte> RSADecryptOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> plaintext;
    plaintext = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return plaintext;
  }

  public static RSAEncryptInput RSAEncryptInput(
      software.amazon.cryptography.primitives.model.RSAEncryptInput nativeValue) {
    RSAPaddingMode padding;
    padding = ToDafny.RSAPaddingMode(nativeValue.padding());
    DafnySequence<? extends Byte> publicKey;
    publicKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.publicKey());
    DafnySequence<? extends Byte> plaintext;
    plaintext = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.plaintext());
    return new RSAEncryptInput(padding, publicKey, plaintext);
  }

  public static DafnySequence<? extends Byte> RSAEncryptOutput(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> cipherText;
    cipherText = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue);
    return cipherText;
  }

  public static RSAPrivateKey RSAPrivateKey(
      software.amazon.cryptography.primitives.model.RSAPrivateKey nativeValue) {
    Integer lengthBits;
    lengthBits = (nativeValue.lengthBits());
    DafnySequence<? extends Byte> pem;
    pem = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.pem());
    return new RSAPrivateKey(lengthBits, pem);
  }

  public static RSAPublicKey RSAPublicKey(
      software.amazon.cryptography.primitives.model.RSAPublicKey nativeValue) {
    Integer lengthBits;
    lengthBits = (nativeValue.lengthBits());
    DafnySequence<? extends Byte> pem;
    pem = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.pem());
    return new RSAPublicKey(lengthBits, pem);
  }

  public static Error Error(AwsCryptographicPrimitivesError nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_AwsCryptographicPrimitivesError(message);
  }

  public static DigestAlgorithm DigestAlgorithm(
      software.amazon.cryptography.primitives.model.DigestAlgorithm nativeValue) {
    switch (nativeValue) {
      case SHA_512: {
        return DigestAlgorithm.create_SHA__512();
      }
      case SHA_384: {
        return DigestAlgorithm.create_SHA__384();
      }
      case SHA_256: {
        return DigestAlgorithm.create_SHA__256();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.");
      }
    }
  }

  public static ECDSASignatureAlgorithm ECDSASignatureAlgorithm(
      software.amazon.cryptography.primitives.model.ECDSASignatureAlgorithm nativeValue) {
    switch (nativeValue) {
      case ECDSA_P384: {
        return ECDSASignatureAlgorithm.create_ECDSA__P384();
      }
      case ECDSA_P256: {
        return ECDSASignatureAlgorithm.create_ECDSA__P256();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.");
      }
    }
  }

  public static RSAPaddingMode RSAPaddingMode(
      software.amazon.cryptography.primitives.model.RSAPaddingMode nativeValue) {
    switch (nativeValue) {
      case PKCS1: {
        return RSAPaddingMode.create_PKCS1();
      }
      case OAEP_SHA1: {
        return RSAPaddingMode.create_OAEP__SHA1();
      }
      case OAEP_SHA256: {
        return RSAPaddingMode.create_OAEP__SHA256();
      }
      case OAEP_SHA384: {
        return RSAPaddingMode.create_OAEP__SHA384();
      }
      case OAEP_SHA512: {
        return RSAPaddingMode.create_OAEP__SHA512();
      }
      default: {
        throw new RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.");
      }
    }
  }

  public static IAwsCryptographicPrimitivesClient AwsCryptographicPrimitives(
      AtomicPrimitives nativeValue) {
    return nativeValue.impl();
  }
}
