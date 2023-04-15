// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Wrappers_Compile.Result;
import dafny.Tuple0;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.DeleteCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialProviders.model.PutCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.UpdaterUsageMetadataInput;

public final class CryptographicMaterialsCache implements ICryptographicMaterialsCache {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache _impl;

  private CryptographicMaterialsCache(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache iCryptographicMaterialsCache) {
    Objects.requireNonNull(iCryptographicMaterialsCache, "Missing value for required argument `iCryptographicMaterialsCache`");
    this._impl = iCryptographicMaterialsCache;
  }

  public static CryptographicMaterialsCache wrap(
      Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache iCryptographicMaterialsCache) {
    return new CryptographicMaterialsCache(iCryptographicMaterialsCache);
  }

  public static <I extends ICryptographicMaterialsCache> CryptographicMaterialsCache wrap(
      I iCryptographicMaterialsCache) {
    Objects.requireNonNull(iCryptographicMaterialsCache, "Missing value for required argument `iCryptographicMaterialsCache`");
    if (iCryptographicMaterialsCache instanceof software.amazon.cryptography.materialProviders.CryptographicMaterialsCache) {
      return ((CryptographicMaterialsCache) iCryptographicMaterialsCache);
    }
    return CryptographicMaterialsCache.wrap(new NativeWrapper(iCryptographicMaterialsCache));
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache impl() {
    return this._impl;
  }

  public void PutCacheEntry(PutCacheEntryInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.PutCacheEntryInput dafnyValue = ToDafny.PutCacheEntryInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.PutCacheEntry(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public GetCacheEntryOutput GetCacheEntry(GetCacheEntryInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryInput dafnyValue = ToDafny.GetCacheEntryInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryOutput, Error> result = this._impl.GetCacheEntry(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetCacheEntryOutput(result.dtor_value());
  }

  public void UpdaterUsageMetadata(UpdaterUsageMetadataInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.UpdaterUsageMetadataInput dafnyValue = ToDafny.UpdaterUsageMetadataInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.UpdaterUsageMetadata(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void DeleteCacheEntry(DeleteCacheEntryInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.DeleteCacheEntryInput dafnyValue = ToDafny.DeleteCacheEntryInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.DeleteCacheEntry(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  protected static final class NativeWrapper implements Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache {
    protected final ICryptographicMaterialsCache _impl;

    NativeWrapper(ICryptographicMaterialsCache nativeImpl) {
      if (nativeImpl instanceof CryptographicMaterialsCache) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<Tuple0, Error> PutCacheEntry(
        Dafny.Aws.Cryptography.MaterialProviders.Types.PutCacheEntryInput dafnyInput) {
      PutCacheEntryInput nativeInput = ToNative.PutCacheEntryInput(dafnyInput);
      try {
        this._impl.PutCacheEntry(nativeInput);
        return Result.create_Success(Tuple0.create());
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<Tuple0, Error> PutCacheEntry_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.PutCacheEntryInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryOutput, Error> GetCacheEntry(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryInput dafnyInput) {
      GetCacheEntryInput nativeInput = ToNative.GetCacheEntryInput(dafnyInput);
      try {
        GetCacheEntryOutput nativeOutput = this._impl.GetCacheEntry(nativeInput);
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryOutput dafnyOutput = ToDafny.GetCacheEntryOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryOutput, Error> GetCacheEntry_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetCacheEntryInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }

    public Result<Tuple0, Error> UpdaterUsageMetadata(
        Dafny.Aws.Cryptography.MaterialProviders.Types.UpdaterUsageMetadataInput dafnyInput) {
      UpdaterUsageMetadataInput nativeInput = ToNative.UpdaterUsageMetadataInput(dafnyInput);
      try {
        this._impl.UpdaterUsageMetadata(nativeInput);
        return Result.create_Success(Tuple0.create());
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<Tuple0, Error> UpdaterUsageMetadata_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.UpdaterUsageMetadataInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }

    public Result<Tuple0, Error> DeleteCacheEntry(
        Dafny.Aws.Cryptography.MaterialProviders.Types.DeleteCacheEntryInput dafnyInput) {
      DeleteCacheEntryInput nativeInput = ToNative.DeleteCacheEntryInput(dafnyInput);
      try {
        this._impl.DeleteCacheEntry(nativeInput);
        return Result.create_Success(Tuple0.create());
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<Tuple0, Error> DeleteCacheEntry_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.DeleteCacheEntryInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
