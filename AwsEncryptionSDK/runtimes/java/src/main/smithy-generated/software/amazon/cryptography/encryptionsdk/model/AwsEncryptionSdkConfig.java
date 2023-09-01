// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

import software.amazon.cryptography.materialproviders.model.ESDKCommitmentPolicy;

public class AwsEncryptionSdkConfig {
  private final ESDKCommitmentPolicy commitmentPolicy;

  private final long maxEncryptedDataKeys;

  protected AwsEncryptionSdkConfig(BuilderImpl builder) {
    this.commitmentPolicy = builder.commitmentPolicy();
    this.maxEncryptedDataKeys = builder.maxEncryptedDataKeys();
  }

  public ESDKCommitmentPolicy commitmentPolicy() {
    return this.commitmentPolicy;
  }

  public long maxEncryptedDataKeys() {
    return this.maxEncryptedDataKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder commitmentPolicy(ESDKCommitmentPolicy commitmentPolicy);

    ESDKCommitmentPolicy commitmentPolicy();

    Builder maxEncryptedDataKeys(long maxEncryptedDataKeys);

    long maxEncryptedDataKeys();

    AwsEncryptionSdkConfig build();
  }

  static class BuilderImpl implements Builder {
    protected ESDKCommitmentPolicy commitmentPolicy;

    protected long maxEncryptedDataKeys;

    private boolean _maxEncryptedDataKeysSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AwsEncryptionSdkConfig model) {
      this.commitmentPolicy = model.commitmentPolicy();
      this.maxEncryptedDataKeys = model.maxEncryptedDataKeys();
      this._maxEncryptedDataKeysSet = true;
    }

    public Builder commitmentPolicy(ESDKCommitmentPolicy commitmentPolicy) {
      this.commitmentPolicy = commitmentPolicy;
      return this;
    }

    public ESDKCommitmentPolicy commitmentPolicy() {
      return this.commitmentPolicy;
    }

    public Builder maxEncryptedDataKeys(long maxEncryptedDataKeys) {
      this.maxEncryptedDataKeys = maxEncryptedDataKeys;
      this._maxEncryptedDataKeysSet = true;
      return this;
    }

    public long maxEncryptedDataKeys() {
      return this.maxEncryptedDataKeys;
    }

    public AwsEncryptionSdkConfig build() {
      if (this._maxEncryptedDataKeysSet && this.maxEncryptedDataKeys() < 1) {
        throw new IllegalArgumentException("`maxEncryptedDataKeys` must be greater than or equal to 1");
      }
      return new AwsEncryptionSdkConfig(this);
    }
  }
}
