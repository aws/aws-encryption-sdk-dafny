// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.model.OnDecryptInput;
import software.amazon.cryptography.materialproviders.model.OnDecryptOutput;
import software.amazon.cryptography.materialproviders.model.OnEncryptInput;
import software.amazon.cryptography.materialproviders.model.OnEncryptOutput;

public final class Keyring implements IKeyring {
  private final software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _impl;

  private Keyring(
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring iKeyring) {
    Objects.requireNonNull(iKeyring, "Missing value for required argument `iKeyring`");
    this._impl = iKeyring;
  }

  public static Keyring wrap(
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring iKeyring) {
    return new Keyring(iKeyring);
  }

  public static <I extends IKeyring> Keyring wrap(I iKeyring) {
    Objects.requireNonNull(iKeyring, "Missing value for required argument `iKeyring`");
    if (iKeyring instanceof software.amazon.cryptography.materialproviders.Keyring) {
      return ((Keyring) iKeyring);
    }
    return Keyring.wrap(new NativeWrapper(iKeyring));
  }

  public software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring impl() {
    return this._impl;
  }

  public OnDecryptOutput OnDecrypt(OnDecryptInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput dafnyValue = ToDafny.OnDecryptInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput, Error> result = this._impl.OnDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.OnDecryptOutput(result.dtor_value());
  }

  public OnEncryptOutput OnEncrypt(OnEncryptInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput dafnyValue = ToDafny.OnEncryptInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput, Error> result = this._impl.OnEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.OnEncryptOutput(result.dtor_value());
  }

  protected static final class NativeWrapper implements software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring {
    protected final IKeyring _impl;

    NativeWrapper(IKeyring nativeImpl) {
      if (nativeImpl instanceof Keyring) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput, Error> OnDecrypt(
        software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput dafnyInput) {
      OnDecryptInput nativeInput = ToNative.OnDecryptInput(dafnyInput);
      try {
        OnDecryptOutput nativeOutput = this._impl.OnDecrypt(nativeInput);
        software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput dafnyOutput = ToDafny.OnDecryptOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput, Error> OnDecrypt_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput, Error> OnEncrypt(
        software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput dafnyInput) {
      OnEncryptInput nativeInput = ToNative.OnEncryptInput(dafnyInput);
      try {
        OnEncryptOutput nativeOutput = this._impl.OnEncrypt(nativeInput);
        software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput dafnyOutput = ToDafny.OnEncryptOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput, Error> OnEncrypt_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
