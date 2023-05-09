// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialproviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.GetEncryptionMaterialsOutput;

public final class CryptographicMaterialsManager implements ICryptographicMaterialsManager {
  private final software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager _impl;

  private CryptographicMaterialsManager(
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager iCryptographicMaterialsManager) {
    Objects.requireNonNull(iCryptographicMaterialsManager, "Missing value for required argument `iCryptographicMaterialsManager`");
    this._impl = iCryptographicMaterialsManager;
  }

  public static CryptographicMaterialsManager wrap(
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager iCryptographicMaterialsManager) {
    return new CryptographicMaterialsManager(iCryptographicMaterialsManager);
  }

  public static <I extends ICryptographicMaterialsManager> CryptographicMaterialsManager wrap(
      I iCryptographicMaterialsManager) {
    Objects.requireNonNull(iCryptographicMaterialsManager, "Missing value for required argument `iCryptographicMaterialsManager`");
    if (iCryptographicMaterialsManager instanceof software.amazon.cryptography.materialproviders.CryptographicMaterialsManager) {
      return ((CryptographicMaterialsManager) iCryptographicMaterialsManager);
    }
    return CryptographicMaterialsManager.wrap(new NativeWrapper(iCryptographicMaterialsManager));
  }

  public software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager impl(
      ) {
    return this._impl;
  }

  public DecryptMaterialsOutput DecryptMaterials(DecryptMaterialsInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput dafnyValue = ToDafny.DecryptMaterialsInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput, Error> result = this._impl.DecryptMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DecryptMaterialsOutput(result.dtor_value());
  }

  public GetEncryptionMaterialsOutput GetEncryptionMaterials(
      GetEncryptionMaterialsInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput dafnyValue = ToDafny.GetEncryptionMaterialsInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput, Error> result = this._impl.GetEncryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetEncryptionMaterialsOutput(result.dtor_value());
  }

  protected static final class NativeWrapper implements software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager {
    protected final ICryptographicMaterialsManager _impl;

    NativeWrapper(ICryptographicMaterialsManager nativeImpl) {
      if (nativeImpl instanceof CryptographicMaterialsManager) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput, Error> DecryptMaterials(
        software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput dafnyInput) {
      DecryptMaterialsInput nativeInput = ToNative.DecryptMaterialsInput(dafnyInput);
      try {
        DecryptMaterialsOutput nativeOutput = this._impl.DecryptMaterials(nativeInput);
        software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput dafnyOutput = ToDafny.DecryptMaterialsOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsOutput, Error> DecryptMaterials_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput, Error> GetEncryptionMaterials(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput dafnyInput) {
      GetEncryptionMaterialsInput nativeInput = ToNative.GetEncryptionMaterialsInput(dafnyInput);
      try {
        GetEncryptionMaterialsOutput nativeOutput = this._impl.GetEncryptionMaterials(nativeInput);
        software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput dafnyOutput = ToDafny.GetEncryptionMaterialsOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsOutput, Error> GetEncryptionMaterials_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
