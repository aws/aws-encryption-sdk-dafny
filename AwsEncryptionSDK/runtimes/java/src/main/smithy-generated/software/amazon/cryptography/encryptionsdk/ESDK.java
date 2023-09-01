// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.encryptionsdk.internaldafny.ESDKClient;
import software.amazon.cryptography.encryptionsdk.internaldafny.__default;
import software.amazon.cryptography.encryptionsdk.internaldafny.types.Error;
import software.amazon.cryptography.encryptionsdk.internaldafny.types.IAwsEncryptionSdkClient;
import software.amazon.cryptography.encryptionsdk.model.AwsEncryptionSdkConfig;
import software.amazon.cryptography.encryptionsdk.model.DecryptInput;
import software.amazon.cryptography.encryptionsdk.model.DecryptOutput;
import software.amazon.cryptography.encryptionsdk.model.EncryptInput;
import software.amazon.cryptography.encryptionsdk.model.EncryptOutput;

public class ESDK {
  private final IAwsEncryptionSdkClient _impl;

  protected ESDK(BuilderImpl builder) {
    AwsEncryptionSdkConfig input = builder.AwsEncryptionSdkConfig();
    software.amazon.cryptography.encryptionsdk.internaldafny.types.AwsEncryptionSdkConfig dafnyValue = ToDafny.AwsEncryptionSdkConfig(input);
    Result<ESDKClient, Error> result = __default.ESDK(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  ESDK(IAwsEncryptionSdkClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public DecryptOutput Decrypt(DecryptInput input) {
    software.amazon.cryptography.encryptionsdk.internaldafny.types.DecryptInput dafnyValue = ToDafny.DecryptInput(input);
    Result<software.amazon.cryptography.encryptionsdk.internaldafny.types.DecryptOutput, Error> result = this._impl.Decrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DecryptOutput(result.dtor_value());
  }

  public EncryptOutput Encrypt(EncryptInput input) {
    software.amazon.cryptography.encryptionsdk.internaldafny.types.EncryptInput dafnyValue = ToDafny.EncryptInput(input);
    Result<software.amazon.cryptography.encryptionsdk.internaldafny.types.EncryptOutput, Error> result = this._impl.Encrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.EncryptOutput(result.dtor_value());
  }

  protected IAwsEncryptionSdkClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder AwsEncryptionSdkConfig(AwsEncryptionSdkConfig AwsEncryptionSdkConfig);

    AwsEncryptionSdkConfig AwsEncryptionSdkConfig();

    ESDK build();
  }

  static class BuilderImpl implements Builder {
    protected AwsEncryptionSdkConfig AwsEncryptionSdkConfig;

    protected BuilderImpl() {
    }

    public Builder AwsEncryptionSdkConfig(AwsEncryptionSdkConfig AwsEncryptionSdkConfig) {
      this.AwsEncryptionSdkConfig = AwsEncryptionSdkConfig;
      return this;
    }

    public AwsEncryptionSdkConfig AwsEncryptionSdkConfig() {
      return this.AwsEncryptionSdkConfig;
    }

    public ESDK build() {
      if (Objects.isNull(this.AwsEncryptionSdkConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `AwsEncryptionSdkConfig`");
      }
      return new ESDK(this);
    }
  }
}
