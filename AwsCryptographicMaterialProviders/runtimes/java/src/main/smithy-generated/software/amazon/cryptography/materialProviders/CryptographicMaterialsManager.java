// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Wrappers_Compile.Result;
import java.lang.Exception;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.NativeError;
import software.amazon.cryptography.materialProviders.model.OpaqueError;

public final class CryptographicMaterialsManager implements ICryptographicMaterialsManager {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager _impl;

  private CryptographicMaterialsManager(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager iCryptographicMaterialsManager) {
    Objects.requireNonNull(iCryptographicMaterialsManager, "Missing value for required argument `iCryptographicMaterialsManager`");
    this._impl = iCryptographicMaterialsManager;
  }

  public static CryptographicMaterialsManager create(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager iCryptographicMaterialsManager) {
    return new CryptographicMaterialsManager(iCryptographicMaterialsManager);
  }

  public static <I extends ICryptographicMaterialsManager> CryptographicMaterialsManager create(
      I iCryptographicMaterialsManager) {
    Objects.requireNonNull(iCryptographicMaterialsManager, "Missing value for required argument `iCryptographicMaterialsManager`");
    if (iCryptographicMaterialsManager instanceof software.amazon.cryptography.materialProviders.CryptographicMaterialsManager) {
      return ((CryptographicMaterialsManager) iCryptographicMaterialsManager);
    }
    return CryptographicMaterialsManager.create(new NativeWrapper(iCryptographicMaterialsManager));
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager impl() {
    return this._impl;
  }

  public GetEncryptionMaterialsOutput GetEncryptionMaterials(
      GetEncryptionMaterialsInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsInput dafnyValue = ToDafny.GetEncryptionMaterialsInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput, Error> result = this._impl.GetEncryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetEncryptionMaterialsOutput(result.dtor_value());
  }

  public DecryptMaterialsOutput DecryptMaterials(DecryptMaterialsInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsInput dafnyValue = ToDafny.DecryptMaterialsInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput, Error> result = this._impl.DecryptMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DecryptMaterialsOutput(result.dtor_value());
  }

  private static final class NativeWrapper implements Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager {
    private final ICryptographicMaterialsManager _impl;

    NativeWrapper(ICryptographicMaterialsManager nativeImpl) {
      if (nativeImpl instanceof CryptographicMaterialsManager) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput, Error> GetEncryptionMaterials(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsInput dafnyInput) {
      GetEncryptionMaterialsInput nativeInput = ToNative.GetEncryptionMaterialsInput(dafnyInput);
      try {
        GetEncryptionMaterialsOutput nativeOutput = this._impl.GetEncryptionMaterials(nativeInput);
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput dafnyOutput = ToDafny.GetEncryptionMaterialsOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (NativeError ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      } catch (Exception ex) {
        OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
        return Result.create_Failure(ToDafny.Error(error));
      }
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsOutput, Error> GetEncryptionMaterials_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetEncryptionMaterialsInput dafnyInput) {
      throw NativeError.builder().message("Not supported at this time.").build();
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput, Error> DecryptMaterials(
        Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsInput dafnyInput) {
      DecryptMaterialsInput nativeInput = ToNative.DecryptMaterialsInput(dafnyInput);
      try {
        DecryptMaterialsOutput nativeOutput = this._impl.DecryptMaterials(nativeInput);
        Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput dafnyOutput = ToDafny.DecryptMaterialsOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (NativeError ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      } catch (Exception ex) {
        OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
        return Result.create_Failure(ToDafny.Error(error));
      }
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsOutput, Error> DecryptMaterials_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptMaterialsInput dafnyInput) {
      throw NativeError.builder().message("Not supported at this time.").build();
    }
  }
}
