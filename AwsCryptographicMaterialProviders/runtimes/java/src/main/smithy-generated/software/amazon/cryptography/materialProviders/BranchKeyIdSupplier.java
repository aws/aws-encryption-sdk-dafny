// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Wrappers_Compile.Result;
import java.lang.Exception;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.GetBranchKeyIdInput;
import software.amazon.cryptography.materialProviders.model.GetBranchKeyIdOutput;
import software.amazon.cryptography.materialProviders.model.NativeError;
import software.amazon.cryptography.materialProviders.model.OpaqueError;

public final class BranchKeyIdSupplier implements IBranchKeyIdSupplier {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier _impl;

  private BranchKeyIdSupplier(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier iBranchKeyIdSupplier) {
    Objects.requireNonNull(iBranchKeyIdSupplier, "Missing value for required argument `iBranchKeyIdSupplier`");
    this._impl = iBranchKeyIdSupplier;
  }

  public static BranchKeyIdSupplier wrap(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier iBranchKeyIdSupplier) {
    return new BranchKeyIdSupplier(iBranchKeyIdSupplier);
  }

  public static <I extends IBranchKeyIdSupplier> BranchKeyIdSupplier wrap(I iBranchKeyIdSupplier) {
    Objects.requireNonNull(iBranchKeyIdSupplier, "Missing value for required argument `iBranchKeyIdSupplier`");
    if (iBranchKeyIdSupplier instanceof software.amazon.cryptography.materialProviders.BranchKeyIdSupplier) {
      return ((BranchKeyIdSupplier) iBranchKeyIdSupplier);
    }
    return BranchKeyIdSupplier.wrap(new NativeWrapper(iBranchKeyIdSupplier));
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier impl() {
    return this._impl;
  }

  public GetBranchKeyIdOutput GetBranchKeyId(GetBranchKeyIdInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdInput dafnyValue = ToDafny.GetBranchKeyIdInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdOutput, Error> result = this._impl.GetBranchKeyId(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBranchKeyIdOutput(result.dtor_value());
  }

  protected static final class NativeWrapper implements Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier {
    protected final IBranchKeyIdSupplier _impl;

    NativeWrapper(IBranchKeyIdSupplier nativeImpl) {
      if (nativeImpl instanceof BranchKeyIdSupplier) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdOutput, Error> GetBranchKeyId(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdInput dafnyInput) {
      GetBranchKeyIdInput nativeInput = ToNative.GetBranchKeyIdInput(dafnyInput);
      try {
        GetBranchKeyIdOutput nativeOutput = this._impl.GetBranchKeyId(nativeInput);
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdOutput dafnyOutput = ToDafny.GetBranchKeyIdOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (NativeError ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      } catch (Exception ex) {
        OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
        return Result.create_Failure(ToDafny.Error(error));
      }
    }

    public Result<Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdOutput, Error> GetBranchKeyId_k(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetBranchKeyIdInput dafnyInput) {
      throw NativeError.builder().message("Not supported at this time.").build();
    }
  }
}
