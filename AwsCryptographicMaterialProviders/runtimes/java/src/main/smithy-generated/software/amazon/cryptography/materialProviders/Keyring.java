// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.OnDecryptInput;
import software.amazon.cryptography.materialProviders.model.OnDecryptOutput;
import software.amazon.cryptography.materialProviders.model.OnEncryptInput;
import software.amazon.cryptography.materialProviders.model.OnEncryptOutput;

public final class Keyring implements IKeyring {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring _impl;

  private Keyring(Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring iKeyring) {
    Objects.requireNonNull(iKeyring, "Missing value for required argument `iKeyring`");
    this._impl = iKeyring;
  }

  public static Keyring create(Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring iKeyring) {
    return new Keyring(iKeyring);
  }

  public static <I extends IKeyring> Keyring create(I iKeyring) {
    Objects.requireNonNull(iKeyring, "Missing value for required argument `iKeyring`");
    if (iKeyring instanceof software.amazon.cryptography.materialProviders.Keyring) {
      return ((Keyring) iKeyring);
    }
    throw new IllegalArgumentException("Custom implementations of software.amazon.cryptography.materialProviders.IKeyring are NOT supported at this time.");
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring impl() {
    return this._impl;
  }

  public OnEncryptOutput OnEncrypt(OnEncryptInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptInput dafnyValue = ToDafny.OnEncryptInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.OnEncryptOutput, Error> result = this._impl.OnEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.OnEncryptOutput(result.dtor_value());
  }

  public OnDecryptOutput OnDecrypt(OnDecryptInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptInput dafnyValue = ToDafny.OnDecryptInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.OnDecryptOutput, Error> result = this._impl.OnDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.OnDecryptOutput(result.dtor_value());
  }
}
