// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Com.Amazonaws.Kms.Shim;
import Dafny.Com.Amazonaws.Kms.Types.IKMSClient;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.cryptography.materialProviders.model.GetClientInput;

public final class ClientSupplier implements IClientSupplier {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier _impl;

  private ClientSupplier(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    this._impl = iClientSupplier;
  }

  public static ClientSupplier wrap(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier iClientSupplier) {
    return new ClientSupplier(iClientSupplier);
  }

  public static <I extends IClientSupplier> ClientSupplier wrap(I iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    if (iClientSupplier instanceof software.amazon.cryptography.materialProviders.ClientSupplier) {
      return ((ClientSupplier) iClientSupplier);
    }
    return ClientSupplier.wrap(new NativeWrapper(iClientSupplier));
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier impl() {
    return this._impl;
  }

  public KmsClient GetClient(GetClientInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput dafnyValue = ToDafny.GetClientInput(nativeValue);
    Result<IKMSClient, Error> result = this._impl.GetClient(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Dafny.Com.Amazonaws.Kms.ToNative.TrentService(result.dtor_value());
  }

  protected static final class NativeWrapper implements Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier {
    protected final IClientSupplier _impl;

    NativeWrapper(IClientSupplier nativeImpl) {
      if (nativeImpl instanceof ClientSupplier) {
        throw new IllegalArgumentException("Recursive wrapping is strictly forbidden.");
      }
      this._impl = nativeImpl;
    }

    public Result<IKMSClient, Error> GetClient(
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput dafnyInput) {
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
        Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput dafnyInput) {
      throw new RuntimeException("Not supported at this time.");
    }
  }
}
