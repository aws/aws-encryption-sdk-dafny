// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.model.GetClientInput;
import software.amazon.cryptography.services.kms.internaldafny.Shim;
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;

public final class ClientSupplier implements IClientSupplier {
  private final software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _impl;

  private ClientSupplier(
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    this._impl = iClientSupplier;
  }

  public static ClientSupplier wrap(
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier iClientSupplier) {
    return new ClientSupplier(iClientSupplier);
  }

  public static <I extends IClientSupplier> ClientSupplier wrap(I iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    if (iClientSupplier instanceof software.amazon.cryptography.materialproviders.ClientSupplier) {
      return ((ClientSupplier) iClientSupplier);
    }
    return ClientSupplier.wrap(new NativeWrapper(iClientSupplier));
  }

  public software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier impl() {
    return this._impl;
  }

  public KmsClient GetClient(GetClientInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput dafnyValue = ToDafny.GetClientInput(nativeValue);
    Result<IKMSClient, Error> result = this._impl.GetClient(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(result.dtor_value());
  }

  protected static final class NativeWrapper implements software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier {
    protected final IClientSupplier _impl;

    NativeWrapper(IClientSupplier nativeImpl) {
      if (nativeImpl instanceof ClientSupplier) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<IKMSClient, Error> GetClient(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput dafnyInput) {
      GetClientInput nativeInput = ToNative.GetClientInput(dafnyInput);
      try {
        KmsClient nativeOutput = this._impl.GetClient(nativeInput);
        IKMSClient dafnyOutput = new Shim(nativeOutput, null);
        return Result.create_Success(dafnyOutput);
      } catch (RuntimeException ex) {
        return Result.create_Failure(ToDafny.Error(ex));
      }
    }

    public Result<IKMSClient, Error> GetClient_k(
        software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
