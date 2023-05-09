// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdInput;
import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdOutput;

public final class BranchKeyIdSupplier implements IBranchKeyIdSupplier {
  private final software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier _impl;

  private BranchKeyIdSupplier(
      software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier iBranchKeyIdSupplier) {
    Objects.requireNonNull(iBranchKeyIdSupplier, "Missing value for required argument `iBranchKeyIdSupplier`");
    this._impl = iBranchKeyIdSupplier;
  }

  public static BranchKeyIdSupplier wrap(
      software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier iBranchKeyIdSupplier) {
    return new BranchKeyIdSupplier(iBranchKeyIdSupplier);
  }

  public static <I extends IBranchKeyIdSupplier> BranchKeyIdSupplier wrap(I iBranchKeyIdSupplier) {
    Objects.requireNonNull(iBranchKeyIdSupplier, "Missing value for required argument `iBranchKeyIdSupplier`");
    if (iBranchKeyIdSupplier instanceof software.amazon.cryptography.materialproviders.BranchKeyIdSupplier) {
      return ((BranchKeyIdSupplier) iBranchKeyIdSupplier);
    }
    return BranchKeyIdSupplier.wrap(new NativeWrapper(iBranchKeyIdSupplier));
  }

  public software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier impl(
      ) {
    return this._impl;
  }

  public GetBranchKeyIdOutput GetBranchKeyId(GetBranchKeyIdInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdInput dafnyValue = ToDafny.GetBranchKeyIdInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput, Error> result = this._impl.GetBranchKeyId(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBranchKeyIdOutput(result.dtor_value());
  }

  protected static final class NativeWrapper implements software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier {
    protected final IBranchKeyIdSupplier _impl;

    NativeWrapper(IBranchKeyIdSupplier nativeImpl) {
      if (nativeImpl instanceof BranchKeyIdSupplier) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput, Error> GetBranchKeyId(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdInput dafnyInput) {
      GetBranchKeyIdInput nativeInput = ToNative.GetBranchKeyIdInput(dafnyInput);
      try {
        GetBranchKeyIdOutput nativeOutput = this._impl.GetBranchKeyId(nativeInput);
        software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput dafnyOutput = ToDafny.GetBranchKeyIdOutput(nativeOutput);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput, Error> GetBranchKeyId_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
