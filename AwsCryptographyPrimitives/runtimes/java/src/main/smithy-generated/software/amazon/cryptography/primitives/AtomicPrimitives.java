// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives;

import Wrappers_Compile.Result;
import dafny.DafnySequence;
import java.lang.Boolean;
import java.lang.Byte;
import java.lang.IllegalArgumentException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient;
import software.amazon.cryptography.primitives.internaldafny.__default;
import software.amazon.cryptography.primitives.internaldafny.types.Error;
import software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient;
import software.amazon.cryptography.primitives.model.AESDecryptInput;
import software.amazon.cryptography.primitives.model.AESEncryptInput;
import software.amazon.cryptography.primitives.model.AESEncryptOutput;
import software.amazon.cryptography.primitives.model.AesKdfCtrInput;
import software.amazon.cryptography.primitives.model.CryptoConfig;
import software.amazon.cryptography.primitives.model.DigestInput;
import software.amazon.cryptography.primitives.model.ECDSASignInput;
import software.amazon.cryptography.primitives.model.ECDSAVerifyInput;
import software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyInput;
import software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyOutput;
import software.amazon.cryptography.primitives.model.GenerateRSAKeyPairInput;
import software.amazon.cryptography.primitives.model.GenerateRSAKeyPairOutput;
import software.amazon.cryptography.primitives.model.GenerateRandomBytesInput;
import software.amazon.cryptography.primitives.model.GetRSAKeyModulusLengthInput;
import software.amazon.cryptography.primitives.model.GetRSAKeyModulusLengthOutput;
import software.amazon.cryptography.primitives.model.HMacInput;
import software.amazon.cryptography.primitives.model.HkdfExpandInput;
import software.amazon.cryptography.primitives.model.HkdfExtractInput;
import software.amazon.cryptography.primitives.model.HkdfInput;
import software.amazon.cryptography.primitives.model.KdfCtrInput;
import software.amazon.cryptography.primitives.model.RSADecryptInput;
import software.amazon.cryptography.primitives.model.RSAEncryptInput;

public class AtomicPrimitives {
  private final IAwsCryptographicPrimitivesClient _impl;

  protected AtomicPrimitives(BuilderImpl builder) {
    CryptoConfig nativeValue = builder.CryptoConfig();
    software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig dafnyValue = ToDafny.CryptoConfig(nativeValue);
    Result<AtomicPrimitivesClient, Error> result = __default.AtomicPrimitives(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  AtomicPrimitives(IAwsCryptographicPrimitivesClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public ByteBuffer AESDecrypt(AESDecryptInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput dafnyValue = ToDafny.AESDecryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.AESDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public AESEncryptOutput AESEncrypt(AESEncryptInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput dafnyValue = ToDafny.AESEncryptInput(nativeValue);
    Result<software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput, Error> result = this._impl.AESEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.AESEncryptOutput(result.dtor_value());
  }

  public ByteBuffer AesKdfCounterMode(AesKdfCtrInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput dafnyValue = ToDafny.AesKdfCtrInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.AesKdfCounterMode(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer Digest(DigestInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.DigestInput dafnyValue = ToDafny.DigestInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.Digest(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer ECDSASign(ECDSASignInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput dafnyValue = ToDafny.ECDSASignInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.ECDSASign(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public Boolean ECDSAVerify(ECDSAVerifyInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput dafnyValue = ToDafny.ECDSAVerifyInput(nativeValue);
    Result<Boolean, Error> result = this._impl.ECDSAVerify(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return (result.dtor_value());
  }

  public GenerateECDSASignatureKeyOutput GenerateECDSASignatureKey(
      GenerateECDSASignatureKeyInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput dafnyValue = ToDafny.GenerateECDSASignatureKeyInput(nativeValue);
    Result<software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput, Error> result = this._impl.GenerateECDSASignatureKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GenerateECDSASignatureKeyOutput(result.dtor_value());
  }

  public ByteBuffer GenerateRandomBytes(GenerateRandomBytesInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput dafnyValue = ToDafny.GenerateRandomBytesInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.GenerateRandomBytes(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public GenerateRSAKeyPairOutput GenerateRSAKeyPair(GenerateRSAKeyPairInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput dafnyValue = ToDafny.GenerateRSAKeyPairInput(nativeValue);
    Result<software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput, Error> result = this._impl.GenerateRSAKeyPair(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GenerateRSAKeyPairOutput(result.dtor_value());
  }

  public GetRSAKeyModulusLengthOutput GetRSAKeyModulusLength(
      GetRSAKeyModulusLengthInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput dafnyValue = ToDafny.GetRSAKeyModulusLengthInput(nativeValue);
    Result<software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput, Error> result = this._impl.GetRSAKeyModulusLength(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetRSAKeyModulusLengthOutput(result.dtor_value());
  }

  public ByteBuffer Hkdf(HkdfInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.HkdfInput dafnyValue = ToDafny.HkdfInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.Hkdf(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer HkdfExpand(HkdfExpandInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput dafnyValue = ToDafny.HkdfExpandInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HkdfExpand(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer HkdfExtract(HkdfExtractInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput dafnyValue = ToDafny.HkdfExtractInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HkdfExtract(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer HMac(HMacInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.HMacInput dafnyValue = ToDafny.HMacInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HMac(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer KdfCounterMode(KdfCtrInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput dafnyValue = ToDafny.KdfCtrInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.KdfCounterMode(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer RSADecrypt(RSADecryptInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput dafnyValue = ToDafny.RSADecryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.RSADecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  public ByteBuffer RSAEncrypt(RSAEncryptInput nativeValue) {
    software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput dafnyValue = ToDafny.RSAEncryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.RSAEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(result.dtor_value());
  }

  protected IAwsCryptographicPrimitivesClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder CryptoConfig(CryptoConfig CryptoConfig);

    CryptoConfig CryptoConfig();

    AtomicPrimitives build();
  }

  static class BuilderImpl implements Builder {
    protected CryptoConfig CryptoConfig;

    protected BuilderImpl() {
    }

    public Builder CryptoConfig(CryptoConfig CryptoConfig) {
      this.CryptoConfig = CryptoConfig;
      return this;
    }

    public CryptoConfig CryptoConfig() {
      return this.CryptoConfig;
    }

    public AtomicPrimitives build() {
      if (Objects.isNull(this.CryptoConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `CryptoConfig`");
      }
      return new AtomicPrimitives(this);
    }
  }
}
