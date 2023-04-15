// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore;

import Dafny.Aws.Cryptography.KeyStore.KeyStoreClient;
import Dafny.Aws.Cryptography.KeyStore.Types.Error;
import Dafny.Aws.Cryptography.KeyStore.Types.IKeyStoreClient;
import Dafny.Aws.Cryptography.KeyStore.__default;
import Wrappers_Compile.Result;
import dafny.Tuple0;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.keyStore.model.CreateKeyInput;
import software.amazon.cryptography.keyStore.model.CreateKeyOutput;
import software.amazon.cryptography.keyStore.model.CreateKeyStoreInput;
import software.amazon.cryptography.keyStore.model.CreateKeyStoreOutput;
import software.amazon.cryptography.keyStore.model.GetActiveBranchKeyInput;
import software.amazon.cryptography.keyStore.model.GetActiveBranchKeyOutput;
import software.amazon.cryptography.keyStore.model.GetBeaconKeyInput;
import software.amazon.cryptography.keyStore.model.GetBeaconKeyOutput;
import software.amazon.cryptography.keyStore.model.GetBranchKeyVersionInput;
import software.amazon.cryptography.keyStore.model.GetBranchKeyVersionOutput;
import software.amazon.cryptography.keyStore.model.KeyStoreConfig;
import software.amazon.cryptography.keyStore.model.VersionKeyInput;

public class KeyStore {
  private final IKeyStoreClient _impl;

  protected KeyStore(BuilderImpl builder) {
    KeyStoreConfig nativeValue = builder.KeyStoreConfig();
    Dafny.Aws.Cryptography.KeyStore.Types.KeyStoreConfig dafnyValue = ToDafny.KeyStoreConfig(nativeValue);
    Result<KeyStoreClient, Error> result = __default.KeyStore(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  KeyStore(IKeyStoreClient impl) {
    this._impl = impl;
  }

  public CreateKeyStoreOutput CreateKeyStore(CreateKeyStoreInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreInput dafnyValue = ToDafny.CreateKeyStoreInput(nativeValue);
    Result<Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreOutput, Error> result = this._impl.CreateKeyStore(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.CreateKeyStoreOutput(result.dtor_value());
  }

  public CreateKeyOutput CreateKey(CreateKeyInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyInput dafnyValue = ToDafny.CreateKeyInput(nativeValue);
    Result<Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyOutput, Error> result = this._impl.CreateKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.CreateKeyOutput(result.dtor_value());
  }

  public void VersionKey(VersionKeyInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.VersionKeyInput dafnyValue = ToDafny.VersionKeyInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.VersionKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public GetActiveBranchKeyOutput GetActiveBranchKey(GetActiveBranchKeyInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyInput dafnyValue = ToDafny.GetActiveBranchKeyInput(nativeValue);
    Result<Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyOutput, Error> result = this._impl.GetActiveBranchKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetActiveBranchKeyOutput(result.dtor_value());
  }

  public GetBranchKeyVersionOutput GetBranchKeyVersion(GetBranchKeyVersionInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionInput dafnyValue = ToDafny.GetBranchKeyVersionInput(nativeValue);
    Result<Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionOutput, Error> result = this._impl.GetBranchKeyVersion(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBranchKeyVersionOutput(result.dtor_value());
  }

  public GetBeaconKeyOutput GetBeaconKey(GetBeaconKeyInput nativeValue) {
    Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyInput dafnyValue = ToDafny.GetBeaconKeyInput(nativeValue);
    Result<Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyOutput, Error> result = this._impl.GetBeaconKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBeaconKeyOutput(result.dtor_value());
  }

  protected IKeyStoreClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder KeyStoreConfig(KeyStoreConfig KeyStoreConfig);

    KeyStoreConfig KeyStoreConfig();

    KeyStore build();
  }

  static class BuilderImpl implements Builder {
    protected KeyStoreConfig KeyStoreConfig;

    protected BuilderImpl() {
    }

    public Builder KeyStoreConfig(KeyStoreConfig KeyStoreConfig) {
      this.KeyStoreConfig = KeyStoreConfig;
      return this;
    }

    public KeyStoreConfig KeyStoreConfig() {
      return this.KeyStoreConfig;
    }

    public KeyStore build() {
      if (Objects.isNull(this.KeyStoreConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `KeyStoreConfig`");
      }
      return new KeyStore(this);
    }
  }
}
