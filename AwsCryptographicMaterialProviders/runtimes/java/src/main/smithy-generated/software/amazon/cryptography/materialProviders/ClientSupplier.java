// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.GetClientInput;

public final class ClientSupplier implements IClientSupplier {
  private final Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier _impl;

  private ClientSupplier(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    this._impl = iClientSupplier;
  }

  public static ClientSupplier create(
      Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier iClientSupplier) {
    return new ClientSupplier(iClientSupplier);
  }

  public static <I extends IClientSupplier> ClientSupplier create(I iClientSupplier) {
    Objects.requireNonNull(iClientSupplier, "Missing value for required argument `iClientSupplier`");
    if (iClientSupplier instanceof software.amazon.cryptography.materialProviders.ClientSupplier) {
      return ((ClientSupplier) iClientSupplier);
    }
    throw new IllegalArgumentException("Custom implementations of software.amazon.cryptography.materialProviders.IClientSupplier are NOT supported at this time.");
  }

  public Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier impl() {
    return this._impl;
  }

  public IKeyManagementServiceClient GetClient(GetClientInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.GetClientInput dafnyValue = ToDafny.GetClientInput(nativeValue);
    Result<IKeyManagementServiceClient, Error> result = this._impl.GetClient(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return result.dtor_value();
  }
}
