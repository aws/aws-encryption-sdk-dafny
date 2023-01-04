// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives;

import Dafny.Aws.Cryptography.Primitives.AtomicPrimitivesClient;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Dafny.Aws.Cryptography.Primitives.Types.IAwsCryptographicPrimitivesClient;
import Dafny.Aws.Cryptography.Primitives.__default;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import java.lang.Boolean;
import java.lang.Byte;
import java.lang.IllegalArgumentException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.primitives.model.AESDecryptInput;
import software.amazon.cryptography.primitives.model.AESEncryptInput;
import software.amazon.cryptography.primitives.model.AESEncryptOutput;
import software.amazon.cryptography.primitives.model.CryptoConfig;
import software.amazon.cryptography.primitives.model.DigestInput;
import software.amazon.cryptography.primitives.model.ECDSASignInput;
import software.amazon.cryptography.primitives.model.ECDSAVerifyInput;
import software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyInput;
import software.amazon.cryptography.primitives.model.GenerateECDSASignatureKeyOutput;
import software.amazon.cryptography.primitives.model.GenerateRSAKeyPairInput;
import software.amazon.cryptography.primitives.model.GenerateRSAKeyPairOutput;
import software.amazon.cryptography.primitives.model.GenerateRandomBytesInput;
import software.amazon.cryptography.primitives.model.HMacInput;
import software.amazon.cryptography.primitives.model.HkdfExpandInput;
import software.amazon.cryptography.primitives.model.HkdfExtractInput;
import software.amazon.cryptography.primitives.model.HkdfInput;
import software.amazon.cryptography.primitives.model.RSADecryptInput;
import software.amazon.cryptography.primitives.model.RSAEncryptInput;

public class AtomicPrimitives {
  private final IAwsCryptographicPrimitivesClient _impl;

  protected AtomicPrimitives(BuilderImpl builder) {
    CryptoConfig nativeValue = builder.CryptoConfig();
    Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig dafnyValue = ToDafny.CryptoConfig(nativeValue);
    Result<AtomicPrimitivesClient, Error> result = __default.AtomicPrimitives(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public ByteBuffer GenerateRandomBytes(GenerateRandomBytesInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.GenerateRandomBytesInput dafnyValue = ToDafny.GenerateRandomBytesInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.GenerateRandomBytes(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GenerateRandomBytesOutput(result.dtor_value());
  }

  public ByteBuffer Digest(DigestInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.DigestInput dafnyValue = ToDafny.DigestInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.Digest(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DigestOutput(result.dtor_value());
  }

  public ByteBuffer HMac(HMacInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.HMacInput dafnyValue = ToDafny.HMacInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HMac(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.HMacOutput(result.dtor_value());
  }

  public ByteBuffer HkdfExtract(HkdfExtractInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.HkdfExtractInput dafnyValue = ToDafny.HkdfExtractInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HkdfExtract(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.HkdfExtractOutput(result.dtor_value());
  }

  public ByteBuffer HkdfExpand(HkdfExpandInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.HkdfExpandInput dafnyValue = ToDafny.HkdfExpandInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.HkdfExpand(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.HkdfExpandOutput(result.dtor_value());
  }

  public ByteBuffer Hkdf(HkdfInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.HkdfInput dafnyValue = ToDafny.HkdfInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.Hkdf(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.HkdfOutput(result.dtor_value());
  }

  public AESEncryptOutput AESEncrypt(AESEncryptInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.AESEncryptInput dafnyValue = ToDafny.AESEncryptInput(nativeValue);
    Result<Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput, Error> result = this._impl.AESEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.AESEncryptOutput(result.dtor_value());
  }

  public ByteBuffer AESDecrypt(AESDecryptInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.AESDecryptInput dafnyValue = ToDafny.AESDecryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.AESDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.AESDecryptOutput(result.dtor_value());
  }

  public GenerateRSAKeyPairOutput GenerateRSAKeyPair(GenerateRSAKeyPairInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.GenerateRSAKeyPairInput dafnyValue = ToDafny.GenerateRSAKeyPairInput(nativeValue);
    Result<Dafny.Aws.Cryptography.Primitives.Types.GenerateRSAKeyPairOutput, Error> result = this._impl.GenerateRSAKeyPair(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GenerateRSAKeyPairOutput(result.dtor_value());
  }

  public ByteBuffer RSADecrypt(RSADecryptInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.RSADecryptInput dafnyValue = ToDafny.RSADecryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.RSADecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.RSADecryptOutput(result.dtor_value());
  }

  public ByteBuffer RSAEncrypt(RSAEncryptInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.RSAEncryptInput dafnyValue = ToDafny.RSAEncryptInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.RSAEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.RSAEncryptOutput(result.dtor_value());
  }

  public GenerateECDSASignatureKeyOutput GenerateECDSASignatureKey(
      GenerateECDSASignatureKeyInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.GenerateECDSASignatureKeyInput dafnyValue = ToDafny.GenerateECDSASignatureKeyInput(nativeValue);
    Result<Dafny.Aws.Cryptography.Primitives.Types.GenerateECDSASignatureKeyOutput, Error> result = this._impl.GenerateECDSASignatureKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GenerateECDSASignatureKeyOutput(result.dtor_value());
  }

  public ByteBuffer ECDSASign(ECDSASignInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.ECDSASignInput dafnyValue = ToDafny.ECDSASignInput(nativeValue);
    Result<DafnySequence<? extends Byte>, Error> result = this._impl.ECDSASign(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.ECDSASignOutput(result.dtor_value());
  }

  public Boolean ECDSAVerify(ECDSAVerifyInput nativeValue) {
    Dafny.Aws.Cryptography.Primitives.Types.ECDSAVerifyInput dafnyValue = ToDafny.ECDSAVerifyInput(nativeValue);
    Result<Boolean, Error> result = this._impl.ECDSAVerify(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.ECDSAVerifyOutput(result.dtor_value());
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
