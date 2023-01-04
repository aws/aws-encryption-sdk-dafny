// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput;

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
    throw new IllegalArgumentException("Custom implementations of software.amazon.cryptography.materialProviders.ICryptographicMaterialsManager are NOT supported at this time.");
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
}
